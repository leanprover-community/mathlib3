"""
This Python script computes and prints the "Longest Pole" as described in
[this thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/The.20long.20pole.20in.20mathlib/near/253932389).

It assumes the presence of a file "scripts/times.json" containing data as
found, for example, [here](https://mathlib-bench.limperg.de/commit/a5d2dbc51bbf61b715b09552717001c6c5ae653b/json)

This implementation depends on the NetworkX python module.
"""

import json
import os
import networkx as nx

timings = json.load(open("scripts/times.json"))["timings"]

import_graph = nx.DiGraph()

timing_filename_set = set(timings)

for filename in timings:
    import_graph.add_node(filename, weight=timings[filename])

print(f"{len(import_graph.nodes)} timings added")

count = 0

walked_set = set()

for root, directories, filenames in os.walk('src'):

    for filename in filenames:

        if filename.endswith(".lean"):
            count += 1
            file = os.path.join(root, filename)
            rel_file = file[4:]

            walked_set.add(rel_file)

            found_import = False
            for line in open(file):
                if line.startswith("/-!"):
                    # we have reached the module docstring, there are no more
                    # imports
                    break
                if line.startswith("import"):
                    found_import = True
                    imported = line[7:-1].replace(".", "/") + ".lean"
                    time = timings[rel_file] if rel_file in timings else 0
                    import_graph.add_edge(rel_file, imported, weight=time)
                else:
                    if found_import:
                        # We have left the import section
                        # Important as some files include commented examples
                        # of imports, which are not true imports
                        break

print(f"Walked {count} lean files")

longest_path = nx.dag_longest_path(import_graph, default_weight=0)
longest_path_length = nx.dag_longest_path_length(import_graph, default_weight=0)

print("Longest Pole:")

for file in longest_path:
    print(file, timings[file])

print(f"Total time {longest_path_length}")
