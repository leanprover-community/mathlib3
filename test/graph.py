import networkx as nx

import json5

with open('graph.json', encoding='utf8') as f:
    data = json5.load(f)

def fix(n):
    return n.replace('non_unital', 'nu').replace('non_assoc', 'na').replace('left_', 'l_').replace('right_', 'r_')

g = nx.DiGraph()
for decl, info in data.items():
    g.add_node(fix(info['class']), typ="class", shape="plaintext", width=0, height=0, margin="0.1,0.1", fontname="inconsolata")
    if len(info['inputs']) != 1:
        continue
    src = info['inputs'][0]
    g.add_edge(fix(src), fix(info['class']))
g = g.subgraph(nx.node_connected_component(g.to_undirected(as_view=True), 'monoid')).copy()
g.remove_node('has_distrib_neg')
to_keep = ['has_one', 'has_zero', 'has_add', 'has_mul', 'has_neg', 'has_inv', 'has_le']
g = g.subgraph(set.union(
    *[{n} | nx.ancestors(g, n) for n in to_keep])).copy()
g.remove_nodes_from({'has_le'} | nx.ancestors(g, 'has_le'))
gt = nx.transitive_reduction(g)
gt.add_nodes_from(g.nodes(data=True))
gt.add_edges_from((u, v, g.edges[u, v]) for u, v in gt.edges)
g = gt

interesting = nx.DiGraph()
interesting.add_edge('add_comm_monoid', 'add_monoid')
interesting.add_edge('add_comm_group', 'add_group')
interesting.add_edge('semiring', 'add_comm_monoid')
interesting.add_edge('ring', 'add_comm_group')
interesting.add_edge('add_group', 'add_monoid')
interesting.add_edge('add_comm_group', 'add_comm_monoid')
interesting.add_edge('ring', 'semiring')
for i in interesting.nodes():
    g.nodes()[i]['class'] = 'interesting'
for t,f in interesting.edges():
    p = nx.shortest_path(g, t, f)
    for e in zip(p,p[1:]):
        print(t, f, e)
        g.edges()[e]['class'] = 'interesting'
        g.edges()[e]['weight'] = 2

from networkx.drawing.nx_agraph import write_dot
print(g)
# print(nx.to_latex(g))
write_dot(g, "graph.dot")
"""
nodesep=0.1;
{rank=sink; has_one; has_zero; has_add; has_neg; has_inv; has_mul }
{rank=same; mul_zero_class; mul_one_class; add_zero_class; }
"""
