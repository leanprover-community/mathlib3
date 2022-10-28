#!/usr/bin/env python3
import os
import re
import yaml
import networkx as nx
import subprocess
from urllib.request import urlopen

from pathlib import Path

import_re = re.compile(r"^import ([^ ]*)")
synchronized_re = re.compile(r".*SYNCHRONIZED WITH MATHLIB4.*")
hash_re = re.compile(r"[0-9a-f]*")

def mk_label(path: Path) -> str:
    rel = path.relative_to(Path('src'))
    return str(rel.with_suffix('')).replace(os.sep, '.')

# So that the port status wiki page is human readable, we enclose the YAML with backticks,
# which need to be removed here.
def yaml_md_load(wikicontent: bytes):
    return yaml.safe_load(wikicontent.replace(b"```", b""))

def stripPrefix(tag : str) -> str:
    if tag.startswith('No: '):
        return tag[4:]
    else:
        if tag.startswith('No'):
            return tag[2:].lstrip()
        else:
            return tag

graph = nx.DiGraph()

for path in Path('src').glob('**/*.lean'):
    if path.parts[1] in ['tactic', 'meta']:
        continue
    graph.add_node(mk_label(path))

synchronized = dict()

for path in Path('src').glob('**/*.lean'):
    if path.parts[1] in ['tactic', 'meta']:
        continue
    label = mk_label(path)
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
            graph.add_edge(imported, label)
        if synchronized_re.match(line):
            synchronized[label] = True


data = yaml_md_load(urlopen('https://raw.githubusercontent.com/wiki/leanprover-community/mathlib/mathlib4-port-status.md').read())

# First make sure all nodes exists in the data set
for node in graph.nodes:
    data.setdefault(node, 'No')
yaml.dump(data, Path('port_status.yaml').open('w'))

allDone = dict()
parentsDone = dict()
verified = dict()
touched = dict()
for node in graph.nodes:
    if data[node].startswith('Yes'):
      chunks = data[node].split(' ')
      if len(chunks) > 2:
        if hash_re.match(chunks[2]):
            verified[node] = chunks[2]
            result = subprocess.run(['git', 'diff', '--name-only', chunks[2] + "..HEAD", "src" + os.sep + node.replace('.', os.sep) + ".lean"], stdout=subprocess.PIPE)
            if result.stdout != b'':
                touched[node] = True
        else:
            print("Bad status for " + node)
            print("Expected 'Yes MATHLIB4-PR MATHLIB-HASH'")
    ancestors = nx.ancestors(graph, node)
    if all(data[imported].startswith('Yes') for imported in ancestors) and data[node].startswith('No'):
        allDone[node] = (len(nx.descendants(graph, node)), stripPrefix(data[node]))
    else:
        if all(data[imported].startswith('Yes') for imported in graph.predecessors(node)) and data[node].startswith('No'):
            parentsDone[node] = (len(nx.descendants(graph, node)), stripPrefix(data[node]))

print('# The following files have all dependencies ported already, and should be ready to port:')
print('# Earlier items in the list are required in more places in mathlib.')
allDone = dict(sorted(allDone.items(), key=lambda item: -item[1][0]))
for k, v in allDone.items():
    if v[1] == "":
        print(k)
    else:
        print(k + "    -- " + v[1])

print()
print('# The following files have their immediate dependencies ported already, and may be ready to port:')
parentsDone = dict(sorted(parentsDone.items(), key=lambda item: -item[1][0]))
for k, v in parentsDone.items():
    if v[1] == "":
        print(k)
    else:
        print(k + "    -- " + v[1])

print()
print('# The following files are marked as ported, but do not have a SYNCHRONIZED WITH MATHLIB4 label.')
for node in graph.nodes:
    if data[node].startswith('Yes') and not node in synchronized:
        print(node)

print()
print('# The following files are marked as ported, but have not been verified against a commit hash from mathlib.')
for node in graph.nodes:
    if data[node].startswith('Yes') and not node in verified:
        print(node)

if len(touched) > 0:
    print()
    print('# The following files have been modified since the commit at which they were verified.')
    for n in touched.keys():
        print(n)
