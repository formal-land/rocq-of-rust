"""Read source-level obligations from the pinned --log vir S-expression format."""
import json
import re

from export_contracts import attr, parse_forest, payload


def fail(node, message):
    raise ValueError(f"{node[1]}: {message}")


def ident(token):
    value = json.loads(token)
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', value):
        raise ValueError(f"unsupported observation name {value!r}")
    return value


def call(node):
    expr = payload(node)
    if expr[:2] == ['>', 'Call']:
        target = attr(expr, 'target')
        if target[:2] == ['CallTarget', 'Fun']:
            return attr(target[3], 'path'), attr(expr, 'args'), target[2]
    return None, [], None


def conjunction(clauses):
    if not clauses:
        return 'Truth'
    result = clauses[-1]
    for clause in reversed(clauses[:-1]):
        result = f'(Both {clause} {result})'
    return result


U32 = ['Typ', 'Int', ['IntRange', 'U', '32']]
SHARED_U32_SLICE = ['Typ', 'Decorate', ['TypDecoration', 'Ref'], 'None',
                    ['Typ', 'Primitive', ['Primitive', 'Slice'], [U32]]]


class Emitter:
    def __init__(self, function, declarations):
        # Preserve VIR identities before erasing disambiguators to source names.
        params = [p[2] for p in attr(function, 'params') + [attr(function, 'outer_ret')]]
        self.bindings = {json.loads(attr(p, 'name')[1]): attr(p, 'name') for p in params}
        self.fields = {}
        for decl in declarations:
            if decl[0] != 'Datatype' or attr(decl, 'typ_params'):
                continue
            name = attr(decl, 'name')
            variants = attr(decl, 'variants')
            if name[:2] != ['Dt', 'Path'] or len(variants) != 1:
                continue
            variant = variants[0]
            for _, field, spec in attr(variant, 'fields'):
                if spec[2] == 'Exec':
                    self.fields[name[2], attr(variant, 'name'), field] = spec[1]

    def observe(self, node, phase="Current"):
        expr = payload(node)
        match expr:
            case ['Place', 'DerefMut', child]:
                if node[-1][:2] == ['Typ', 'MutRef']:
                    fail(node, 'nested reference indirection requires a loan observation')
                return self.observe(child, phase)
            case ['>', 'ReadPlace', child, _] | ['Place', 'Temporary', child]:
                return self.observe(child, phase)
            case ['>', 'Old', child] if phase == "Current":
                return self.observe(child, "Entry")
            case ['>', 'Unary', ['UnaryOp', 'MutRefFuture', ['MutRefFutureSourceName', 'Final']], child] if phase == "Current":
                return self.observe(child, "Expiry")
            case ['Place', 'Field', info, child] if attr(info, 'check') == ['VariantCheck', 'None']:
                datatype = attr(info, 'datatype')
                field = ident(attr(info, 'field'))
                if (datatype[:2] != ['Dt', 'Path'] or
                        self.fields.get((datatype[2], attr(info, 'variant'), field)) != node[-1]):
                    fail(node, 'expected a typed executable field of a single-variant record')
                p, root, fields = self.observe(child, phase)
                return p, root, [*fields, field]
            case [">", "VarAt", var, ["VarAt", "Pre"]] if phase in ("Entry", "Current"):
                return "Entry", var, []
            case ['Place', 'Local', var]:
                return phase, var, []
        fail(node, f"unsupported memory observation {expr[:2]}")


    def address(self, phase, var, fields):
        name = ident(var[1])
        if self.bindings.setdefault(name, var) != var:
            raise ValueError(f"distinct VIR variables named {name!r} require distinct observations")
        path = [name, *fields]
        return phase + ' [' + '; '.join(json.dumps(v) for v in path) + ']'


    def seq(self, node):
        fun, args, kind = call(node)
        if (fun == 'vstd::t%view::t%View::view' and len(args) == 1
                and kind[:2] == ['CallTargetKind', 'DynamicResolved']
                and attr(attr(kind, 'resolved'), 'path') == 'vstd::t%slice::impl&%0::view'
                and args[0][-1] == SHARED_U32_SLICE):
            return self.address(*self.observe(args[0]))
        fail(node, "expected the vstd view of a [u32] slice")


    def number(self, node, bound, partial):
        expr = payload(node)
        typ = node[-1]
        if typ[:2] != ['Typ', 'Int'] or typ[2] not in (['IntRange', 'Int'], ['IntRange', 'Nat'],
                ['IntRange', 'USize'], ['IntRange', 'U', '32']):
            fail(node, f"unsupported numerical sort {typ}")
        fun, args, kind = call(node)
        if fun == 'vstd::t%seq::t%Seq::len' and kind == ['CallTargetKind', 'Static']:
            return f"(Length {self.seq(args[0])})"
        if fun == 'vstd::t%seq::impl&%2::spec_index' and kind == ['CallTargetKind', 'Static']:
            if not partial:
                fail(node, "index in a premise requires a definedness proof")
            return f"(Index {self.seq(args[0])} {self.number(args[1], bound, False)})"
        match expr:
            case ['>', 'Const', ['Constant', 'Int', n]] if re.fullmatch('-?[0-9]+', n):
                return f"(Number ({n}))"
            case ['>', 'Binary', ['BinaryOp', 'Arith', ['ArithOp', op, ['OverflowBehavior', 'Truncate', ['IntRange','Int']]]], a, b] if op in ('Add','Sub'):
                ctor = {'Add':'Plus','Sub':'Minus'}[op]
                return f"({ctor} {self.number(a, bound, partial)} {self.number(b, bound, partial)})"
        phase, var, fields = self.observe(node)
        if var in bound:
            if phase != 'Current' or fields:
                fail(node, "invalid bound variable projection")
            return f"(Bound {bound.index(var)}%nat)"
        return f"(Word {self.address(phase, var, fields)})"


    def formula(self, node, bound=(), partial=True):
        expr = payload(node)
        def comparison(op, a, b):
            match op:
                case ['BinaryOp', 'Eq', 'Spec']:
                    tag = 'Equal'
                case [_, 'Inequality', ['InequalityOp', rel]] if rel in ('Le','Lt','Ge','Gt'):
                    if rel in ('Ge','Gt'):
                        a,b = b,a
                    tag = 'AtMost' if rel in ('Le','Ge') else 'Less'
                case _:
                    fail(node, f"unsupported comparison {op}")
            return f'(Compare {tag} {self.number(a,bound,partial)} {self.number(b,bound,partial)})'
        match expr:
            case ['>', 'Binary', op, a, b]:
                return comparison(op,a,b)
            case ['>', 'Multi', ['MultiOp', 'Chained', ops], terms] if len(terms) == len(ops)+1:
                return conjunction([comparison(op,a,b) for op,a,b in zip(ops,terms,terms[1:])])
            case ['>', 'Logical', ['LogicalOp', op], a, b] if op in ('And','Implies'):
                ctor = 'Both' if op=='And' else 'Implies'
                return f'({ctor} {self.formula(a,bound,partial and op=="And")} {self.formula(b,bound,partial)})'
            case ['>', 'Quant', ['Forall'], [['->', var, ['Typ','Int',['IntRange','Int']]]], body]:
                return f'(ForallInt {self.formula(body,(var,*bound),partial)})'
            case ['>', 'Unary', ['UnaryOp','Trigger',_], child]:
                return self.formula(child,bound,partial)
            case ['>', 'Const', ['Constant','Bool','true']]:
                return 'Truth'
        fail(node, f"unsupported formula {expr[:3]}")


def body_sites(tree):
    if not isinstance(tree, list):
        return
    if tree[:1] == ['@@'] and isinstance(tree[2], list) and tree[2][1] in (
            'AssertBy', 'AssertQuery', 'AssertCompute', 'AssertAssumeUserDefinedTypeInvariant'):
        fail(tree, f"unsupported assertion form {tree[2][1]}")
    if tree[:2] == ['>', 'Loop']:
        for inv in attr(tree, 'invs'):
            yield 'invariant', attr(inv, 'inv')
    if tree[:2] == ['>', 'AssertAssume'] and attr(tree, 'is_assume') == 'false':
        yield 'assert', attr(tree, 'expr')
    for child in tree:
        yield from body_sites(child)


def generate(text, function, at=None):
    declarations = [r[2] for r in parse_forest(text)
                    if isinstance(r, list) and len(r) > 2 and r[0] == '@']
    functions = [decl for decl in declarations if decl[0] == 'Function'
                 and attr(attr(decl, 'name'), 'path') == function]
    if len(functions)!=1:
        raise ValueError(f"no unique typed VIR function {function}")
    f = functions[0]
    ensures = attr(f,'ensure')
    if attr(f,'mode')!='Exec' or ensures[0]!='tuple' or ensures[2] or attr(f,'returns')!='None':
        raise ValueError(f"unsupported function contract for {function}")
    sites = [('requires', n) for n in attr(f,'require')] + [('ensures', n) for n in ensures[1]]
    sites.extend(body_sites(attr(f,'body')))
    emitter = Emitter(f, declarations)
    names, clauses, inventory = {}, {}, []
    for kind,node in sites:
        idx = names.get(kind,0)
        names[kind] = idx+1
        key = f'{kind}_{idx}'
        try:
            clauses[key] = emitter.formula(node,partial=kind!='requires')
        except (ValueError, IndexError, KeyError) as error:
            fail(node, str(error))
        inventory.append({'id':key,'span':json.loads(node[1])})
    selected='contract'
    if at:
        matches=[]
        for item in inventory:
            match=re.fullmatch(r'(.+):(\d+):(\d+): (\d+):(\d+) \(#\d+\)',item['span'])
            if match:
                a,b,c,d=map(int,match.groups()[1:])
                if match[1].rsplit('/',1)[-1] == function.split('::')[0]+'.rs' and (a,b)<=at<(c,d):
                    matches.append(item['id'])
        if len(matches)!=1:
            raise ValueError(f"expected one assertion at {at}, found {matches}")
        selected=matches[0]
        if selected.startswith('requires_'):
            raise ValueError('callee preconditions are assumptions; select a postcondition or a body assertion')
    def group(kind):
        return conjunction([k for k in clauses if k.startswith(kind+'_')])
    post = group('ensures') if selected=='contract' else selected
    if selected=='contract' and not ensures[1]:
        raise ValueError('function has no postcondition')
    lines=['Require Export Assertion.', 'Import ListNotations.', 'Open Scope string_scope.',
           f'Definition target_function := "{function}".', f'Definition target_site := "{selected}".']
    lines.extend(f'Definition {k} := {v}.' for k,v in clauses.items())
    lines.append(f'Definition contract_post (o : observations) := holds o [] {group("ensures")}.')
    lines.extend([f'Definition pre_syntax := {group("requires")}.', f'Definition post_syntax := {post}.',
                  'Definition pre (o : observations) := holds o [] pre_syntax.',
                  'Definition post (o : observations) := holds o [] post_syntax.'])
    return '\n'.join(lines)+'\n', inventory, selected
