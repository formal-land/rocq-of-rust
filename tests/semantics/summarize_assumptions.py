"""Group the kernel's assumption reports by dependency for a reviewable CI diff."""

from collections import defaultdict
from pathlib import Path
import re
import sys

theorems = re.findall(
    r"^Print Assumptions (\S+)\.$",
    Path(__file__).with_name("assumptions.v").read_text(),
    re.MULTILINE,
)
reports = []
section = None
for line in sys.stdin.read().splitlines():
    if line in {"Axioms:", "Closed under the global context"}:
        reports.append(set())
        section = line
    elif line == "Theory:":
        section = line
    elif not line or line[0].isspace():
        continue
    elif section == "Axioms:" and re.match(r"^\S+\s+:", line):
        reports[-1].add(line.split()[0])
    elif section == "Theory:" and reports:
        reports[-1].add(line)
    else:
        sys.exit(f"Unrecognized assumption report line: {line!r}")

if len(reports) != len(theorems):
    sys.exit(f"Expected {len(theorems)} assumption reports, found {len(reports)}")
dependencies = defaultdict(list)
for theorem, report in zip(theorems, reports):
    for dependency in report:
        dependencies[dependency].append(theorem)
for dependency, users in sorted(dependencies.items()):
    print(dependency)
    for theorem in users:
        print(f"  {theorem}")
