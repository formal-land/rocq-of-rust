"""Export the field-equality fragment used in pair.rs from a pinned Verus VIR dump."""
import argparse
import json
import re
from pathlib import Path


def parse_forest(text):
    """Parse the S-expressions, retaining strings as single tokens."""
    roots = []
    stack = [roots]
    for token in re.findall(r'"(?:\\.|[^"\\])*"|[()]|[^\s()"]+', text):
        if token == '(':
            node = []
            stack[-1].append(node)
            stack.append(node)
        elif token == ')':
            if len(stack) == 1:
                raise ValueError("unexpected closing parenthesis")
            stack.pop()
        else:
            stack[-1].append(token)
    if len(stack) != 1:
        raise ValueError("unterminated expression")
    return roots


def attr(node, key):
    return node[node.index(':' + key) + 1]


def payload(node):
    if node[0] != '@@':
        raise ValueError("expected a typed expression or place")
    return node[2]


def term(node):
    expr = payload(node)
    match expr:
        case ['>', 'ReadPlace', place, _] | ['Place', 'Temporary', place]:
            return term(place)
        case ['Place', 'Local', ['VarIdent', name, _]]:
            return ('var', json.loads(name))
        case ['Place', 'DerefMut', arg]:
            return ('deref', term(arg))
        case ['>', 'Old', arg]:
            return ('old', term(arg))
        case ['>', 'Unary', ['UnaryOp', 'MutRefFuture', ['MutRefFutureSourceName', 'Final']], arg]:
            return ('final', term(arg))
        case ['Place', 'Field', info, arg] if attr(info, 'datatype') == ['Dt', 'Path', 'pair::t%Pair']:
            return ('field', json.loads(attr(info, 'field')), term(arg))
    raise ValueError(f"unsupported contract term {expr[:2]}")


def word(node, binding):
    if node[-1] != ['Typ', 'Int', ['IntRange', 'U', '32']]:
        raise ValueError("expected u32")
    match term(node):
        case ('field', name, phase) if name in ('left', 'right'):
            if phase == ('deref', ('old', ('var', 'p'))):
                return 'old ' + name.title()
            if phase == ('final', ('var', 'p')):
                return 'final ' + name.title()
        case ('deref', ('var', 'r')) if binding == 'borrow':
            return 'returned'
        case ('final', ('var', 'r')) if binding == 'borrow':
            return 'later'
        case ('var', 'v') if binding == 'value':
            return 'v'
    raise ValueError(f"unsupported observation {term(node)}")


def export(text):
    # These bindings specify the three known function interfaces of this experiment.
    bindings = {'copy_right': ('pair', ''), 'left_mut': ('borrow', ' (returned later : W)'),
                'write_through': ('value', ' (v : W)')}
    emitted = set()
    lines = ['(* Generated from the ensures clauses in the Verus VIR. *)',
             'Inductive field := Left | Right.']
    for root in parse_forest(text):
        if not isinstance(root, list) or root[0] != '@' or root[2][0] != 'Function':
            continue
        f = root[2]
        path = attr(attr(f, 'name'), 'path')
        name = path.removeprefix('pair::')
        if path != 'pair::' + name or name not in bindings:
            continue
        if name in emitted or attr(f, 'require') != [] or attr(f, 'mode') != 'Exec':
            raise ValueError(f"unexpected function or preconditions for {path}")
        binding, extra = bindings[name]
        u32 = ['Typ', 'Int', ['IntRange', 'U', '32']]
        pair = ['Typ', 'Datatype', ['Dt', 'Path', 'pair::t%Pair'], [], []]
        params = [(json.loads(attr(p[2], 'name')[1]), attr(p[2], 'typ')) for p in attr(f, 'params')]
        expected = [('p', ['Typ', 'MutRef', pair])]
        if binding == 'value':
            expected.append(('v', u32))
        ret = attr(f, 'outer_ret')[2]
        unit = ['Typ', 'Datatype', ['Dt', 'Tuple', '0'], [], []]
        if params != expected or attr(ret, 'typ') != (['Typ', 'MutRef', u32] if binding == 'borrow' else unit):
            raise ValueError(f"unexpected signature of {path}")
        if binding == 'borrow' and json.loads(attr(ret, 'name')[1]) != 'r':
            raise ValueError("expected named return r")
        ensures = attr(f, 'ensure')
        if len(ensures) != 3 or ensures[0] != 'tuple' or ensures[2] != []:
            raise ValueError(f"unsupported postconditions for {path}")
        equations = []
        for clause in ensures[1]:
            match payload(clause):
                case ['>', 'Binary', ['BinaryOp', 'Eq', 'Spec'], lhs, rhs]:
                    equations.append(word(lhs, binding) + ' = ' + word(rhs, binding))
                case _:
                    raise ValueError(f"unsupported clause in {path}")
        if not equations:
            raise ValueError(f"empty contract for {path}")
        emitted.add(name)
        lines.append(f'Definition {name}_post {{W : Type}} (old final : field -> W){extra} : Prop :=')
        lines.append('  ' + ' /\\ '.join(equations) + '.')
    if emitted != bindings.keys():
        raise ValueError("missing expected functions")
    return '\n'.join(lines) + '\n'


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('vir', type=Path)
    parser.add_argument('rocq', type=Path)
    args = parser.parse_args()
    args.rocq.write_text(export(args.vir.read_text()))
