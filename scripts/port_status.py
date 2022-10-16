#!/usr/bin/env python3
import os
import re
import yaml
import networkx as nx
from urllib.request import urlopen

from pathlib import Path

import_re = re.compile(r"^import ([^ ]*)")

def mk_label(path: Path) -> str:
    rel = path.relative_to(Path('src'))
    return str(rel.with_suffix('')).replace(os.sep, '.')

graph = nx.DiGraph()

for path in Path('src').glob('**/*.lean'):
    if path.parts[1] in ['tactic', 'meta']:
        continue
    graph.add_node(mk_label(path))

for path in Path('src').glob('**/*.lean'):
    if path.parts[1] in ['tactic', 'meta']:
        continue
    for line in path.read_text().split('\n'):
        if (m := import_re.match(line)):
            imported = m.group(1)
            if imported.startswith('tactic.') or imported.startswith('meta.'):
                continue
            if imported not in graph.nodes:
                if imported + '.default' in graph.nodes:
                    imported = imported + '.default'
                else:
                    imported = 'lean_core.' + imported
            graph.add_edge(imported, mk_label(path))

try:
    data = yaml.safe_load(urlopen('https://raw.githubusercontent.com/wiki/leanprover-community/mathlib/mathlib4-port-status.md'))

except FileNotFoundError:
    data = dict()

# First make sure all nodes exists in the data set
for node in graph.nodes:
    data.setdefault(node, 'No')
yaml.dump(data, Path('port_status.yaml').open('w'))

allDone = dict()
parentsDone = dict()
for node in graph.nodes:
    ancestors = nx.ancestors(graph, node)
    if all(data[imported] == 'Yes' for imported in ancestors) and data[node] == 'No':
        allDone[node] = len(nx.descendants(graph, node))
    else:
        if all(data[imported] == 'Yes' for imported in graph.predecessors(node)) and data[node] == 'No':
            parentsDone[node] = len(nx.descendants(graph, node))

print('# The following files have all dependencies ported already, and should be ready to port:')
print('# Earlier items in the list are required in more places in mathlib.')
allDone = dict(sorted(allDone.items(), key=lambda item: -item[1]))
for k in allDone:
  print(k)

print()
print('# The following files have their immediate dependencies ported already, and may be ready to port:')
parentsDone = dict(sorted(parentsDone.items(), key=lambda item: -item[1]))
for k in parentsDone:
  print(k)
