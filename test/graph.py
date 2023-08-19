import networkx as nx

import json5

with open('graph.json', encoding='utf8') as f:
    data = json5.load(f)


g = nx.DiGraph()
for decl, info in data.items():
    g.add_node(info['class'], typ="class", shape="plaintext", width=0, height=0, margin="0.1,0.1", fontname="inconsolata")
    if len(info['inputs']) != 1:
        continue
    src = info['inputs'][0]
    g.add_edge(src, info['class'])
g = g.subgraph(nx.node_connected_component(g.to_undirected(as_view=True), 'monoid')).copy()
to_keep = ['has_one', 'has_zero', 'has_add', 'has_mul', 'has_neg', 'has_inv', 'has_le']
for k in to_keep:
    g.nodes()[k]['rank'] = 0
g = g.subgraph(set.union(
    *[{n} | nx.ancestors(g, n) for n in to_keep])).copy()
g.remove_nodes_from({'has_le'} | nx.ancestors(g, 'has_le'))

from networkx.drawing.nx_agraph import write_dot
print(g)
print(nx.to_latex(g))
write_dot(g, "graph.dot")
