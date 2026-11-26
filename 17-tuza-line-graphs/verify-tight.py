"""Exact packing, covering, and triangle restoration checks on the graph atlas."""

from collections import Counter
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


def packing_and_covering(graph):
    triangles, _, pack, cover = triangle_problem(graph)
    return pack(triangles), cover(triangles)


def check_restorations(graph, totals):
    m, cover = packing_and_covering(graph)
    for triple in combinations(graph, 3):
        missing = tuple(combinations(triple, 2))
        if any(graph.has_edge(*edge) for edge in missing):
            continue
        totals["triples"] += 1
        profile = {}
        for size in (1, 2, 3):
            for restored in combinations(missing, size):
                augmented = graph.copy()
                augmented.add_edges_from(restored)
                profile[restored] = packing_and_covering(augmented)
        if all(profile[(edge,)][1] == cover + 1 for edge in missing):
            totals["single cover"] += 1
            if all(profile[(edge,)][0] == m + 1 for edge in missing):
                totals["single cover and packing"] += 1
        if all(profile[edges][1] == cover + 2 for edges in combinations(missing, 2)):
            totals["double cover"] += 1
        if all(value == (m + 1, cover + len(edges)) for edges, value in profile.items()):
            totals["full profile"] += 1


def check_avoidance_counterexample():
    graph = nx.complete_graph(4)
    first = ((0, 4), (0, 1))
    second = ((2, 5), (2, 3))
    graph.add_edges_from(((0, 4), (2, 5)))
    assert packing_and_covering(graph) == (1, 2)
    for forbidden, expected in ((first, 1), (second, 1), (first + second, 0)):
        residual = graph.copy()
        residual.remove_edges_from(forbidden)
        assert packing_and_covering(residual)[0] == expected


if __name__ == "__main__":
    atlas = nx.graph_atlas_g()
    tight = wedges = 0
    totals = Counter()
    for graph in atlas:
        found, checked = check(graph)
        tight += found
        wedges += checked
        if found:
            check_restorations(graph, totals)

    assert (len(atlas), tight, wedges) == (1253, 44, 250)
    assert totals == {"triples": 167, "single cover": 5, "single cover and packing": 5}
    check_avoidance_counterexample()
    print(f"Atlas graphs: {len(atlas)}")
    print(f"Nontrivial tight graphs, all with standard triangle structure: {tight}")
    print(f"Open wedges individually avoidable by a maximum packing: {wedges}")
    print(f"Independent triples tested: {totals['triples']}")
    print(f"All single restorations raise the cover: {totals['single cover']}")
    print(f"All single restorations raise the cover and packing: {totals['single cover and packing']}")
    print(f"All double restorations raise the cover by two: {totals['double cover']}")
    print(f"Full minimal-counterexample restoration profiles: {totals['full profile']}")
    print("Simultaneous two-wedge avoidance counterexample verified.")
