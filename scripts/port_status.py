#!/usr/bin/env python3
import os
import re
import yaml
import networkx as nx
import subprocess
from urllib.request import urlopen
from mathlibtools.lib import PortStatus, LeanProject, FileStatus
from sys import argv
from pathlib import Path
import shlex

import_re = re.compile(r"^import ([^ ]*)")
synchronized_re = re.compile(r".*SYNCHRONIZED WITH MATHLIB4.*")
hash_re = re.compile(r"[0-9a-f]*")

# Not using re.compile as this is passed to git which uses a different regex dialect:
# https://www.sjoerdlangkemper.nl/2021/08/13/how-does-git-diff-ignore-matching-lines-work/
comment_git_re = r'\`(' + r'|'.join([
    re.escape("> THIS FILE IS SYNCHRONIZED WITH MATHLIB4."),
    re.escape("> https://github.com/leanprover-community/mathlib4/pull/") + r"[0-9]*",
    re.escape("> Any changes to this file require a corresponding PR to mathlib4."),
    r"",
]) + r")" + "\n"

proj = LeanProject.from_path(Path(__file__).parent.parent)

def mk_label(path: Path) -> str:
    rel = path.relative_to(Path('src'))
    return str(rel.with_suffix('')).replace(os.sep, '.')

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
        m = import_re.match(line)
        if m:
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


data = PortStatus.deserialize_old().file_statuses
# First make sure all nodes exists in the data set
for node in graph.nodes:
    data.setdefault(node, FileStatus())
yaml.dump(data, Path('port_status.yaml').open('w'))

allDone = dict()
parentsDone = dict()
verified = dict()
touched = dict()
for node in graph.nodes:
    if data[node].mathlib3_hash:
        verified[node] = data[node].mathlib3_hash
        find_blobs_command = ['git', 'cat-file', '-t', data[node].mathlib3_hash]
        hash_type = subprocess.check_output(find_blobs_command)
        # the hash_type should be commits mostly, we are not interested in blobs
        if b'blob\n' == hash_type:
            break
        git_command = ['git', 'diff', '--quiet',
            f'--ignore-matching-lines={comment_git_re}',
            data[node].mathlib3_hash + "..HEAD", "--", "src" + os.sep + node.replace('.', os.sep) + ".lean"]
        result = subprocess.run(git_command)
        if result.returncode == 1:
            git_command.remove('--quiet')
            touched[node] = git_command
    elif data[node].ported:
        print("Bad status for " + node)
        print("Expected 'Yes MATHLIB4-PR MATHLIB-HASH'")
    ancestors = nx.ancestors(graph, node)
    if all(data[imported].ported for imported in ancestors) and not data[node].ported:
        allDone[node] = (len(nx.descendants(graph, node)), data[node].comments or "")
    else:
        if all(data[imported].ported for imported in graph.predecessors(node)) and not data[node].ported:
            parentsDone[node] = (len(nx.descendants(graph, node)), data[node].comments or "")

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
    if data[node].ported and not node in synchronized:
        print(node + "     -- mathlib4#" + str(data[node].mathlib4_pr))

print()
print('# The following files are marked as ported, but have not been verified against a commit hash from mathlib.')
for node in graph.nodes:
    if data[node].ported and not node in verified:
        print(node)

if len(touched) > 0:
    print()
    print('# The following files have been modified since the commit at which they were verified.')
    for v in touched.values():
        print(' '.join(shlex.quote(vi) for vi in v))
