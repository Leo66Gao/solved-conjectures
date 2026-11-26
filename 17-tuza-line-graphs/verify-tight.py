"""Exact packing, covering, and open-wedge checks on the NetworkX graph atlas."""

from functools import cache
from itertools import combinations

import networkx as nx


def triangle_problem(graph):
    edge_bits = {frozenset(edge): 1 << i for i, edge in enumerate(graph.edges)}
    triangles = []
    for triple in combinations(graph, 3):
        pairs = tuple(combinations(triple, 2))
        if all(graph.has_edge(*edge) for edge in pairs):
            triangles.append(sum(edge_bits[frozenset(edge)] for edge in pairs))
    triangles = tuple(triangles)

    @cache
    def pack(state):
        if not state:
            return 0
        pivot = state[0] & -state[0]
        return max(
            pack(tuple(tri for tri in state if not tri & pivot)),
            1 + max(pack(tuple(tri for tri in state if not tri & take))
                    for take in state if take & pivot),
        )

    @cache
    def cover(state):
        if not state:
            return 0
        first = state[0]
        return 1 + min(
            cover(tuple(tri for tri in state if not tri & (1 << i)))
            for i in range(first.bit_length()) if first & (1 << i)
        )

    return triangles, edge_bits, pack, cover


def check(graph):
    triangles, edge_bits, pack, cover = triangle_problem(graph)
    maximum = pack(triangles)
    if not maximum or cover(triangles) != 2 * maximum:
        return False, 0

    triangle_graph = nx.Graph()
    triangle_graph.add_nodes_from(triangles)
    triangle_graph.add_edges_from((a, b) for a, b in combinations(triangles, 2) if a & b)
    for component in nx.connected_components(triangle_graph):
        mask = 0
        for triangle in component:
            mask |= triangle
        edges = [edge for edge, bit in edge_bits.items() if mask & bit]
        order = len(set().union(*edges))
        assert order in (4, 5) and len(edges) == order * (order - 1) // 2

    wedges = 0
    for middle in graph:
        for a, b in combinations(graph[middle], 2):
            if graph.has_edge(a, b):
                continue
            forbidden = edge_bits[frozenset((a, middle))] | edge_bits[frozenset((b, middle))]
            assert pack(tuple(tri for tri in triangles if not tri & forbidden)) == maximum
            wedges += 1
    return True, wedges


if __name__ == "__main__":
    atlas = nx.graph_atlas_g()
    tight = wedges = 0
    for graph in atlas:
        found, checked = check(graph)
        tight += found
        wedges += checked
    assert (len(atlas), tight, wedges) == (1253, 44, 250)
    print(f"Atlas graphs: {len(atlas)}")
    print(f"Nontrivial tight graphs, all with standard triangle structure: {tight}")
    print(f"Open wedges avoidable by a maximum packing: {wedges}")
