"""Build and check exact triangle packing and covering certificates."""

from itertools import combinations
from math import comb
from random import Random

import networkx as nx

EQUALITY_DEGREES = {0, 1, 2, 4, 5}


def edges(graph):
    return {tuple(sorted(edge)) for edge in graph.edges}


def triangle_edges(triangle):
    return {frozenset(pair) for pair in combinations(triangle, 2)}


def triangles(graph):
    for a in graph:
        for b in graph[a]:
            if b > a:
                for c in graph[a].keys() & graph[b].keys():
                    if c > b:
                        yield a, b, c


def local_cover_size(degree):
    return comb(degree, 2) - degree**2 // 4


def local_packing(incident, avoid=()):
    order = len(incident)
    half = (order + 1) // 2
    incident = sorted(incident - set(avoid)) + list(avoid)
    left, right = incident[:half], incident[half:]
    packing = []
    for i, j in combinations(range(half), 2):
        color = (i + j) % half
        if order % 2 == 0:
            packing.append((left[i], left[j], right[color]))
        elif color:
            packing.append((left[i], left[j], right[color - 1]))
    if len(right) >= 3:
        packing.append(tuple(right[:3]))
    return packing


def edge_colors(component):
    graph = component.copy()
    odd = [v for v, degree in graph.degree if degree % 2]
    auxiliary = max(graph) + 1
    if odd:
        graph.add_edges_from((auxiliary, v) for v in odd)
    if graph.number_of_edges() == 0:
        return {}
    start = auxiliary if odd else min(graph)
    return {
        tuple(sorted((a, b))): index % 2
        for index, (a, b) in enumerate(nx.eulerian_circuit(graph, source=start))
        if auxiliary not in (a, b)
    }


def check(graph):
    line = nx.Graph()
    line.add_nodes_from(edges(graph))
    incident = {v: {tuple(sorted(e)) for e in graph.edges(v)}
                for v in graph}
    for root_edges in incident.values():
        line.add_edges_from(combinations(root_edges, 2))
    available = {frozenset(pair) for pair in nx.line_graph(graph).edges}
    assert available == {frozenset(pair) for pair in line.edges}

    cover, pack = set(), []
    root_triangle_count = 0
    for nodes in nx.connected_components(graph):
        component = graph.subgraph(nodes)
        triangle = next(triangles(component), None)
        avoid = {}
        if triangle:
            root_triangle_count += 1
            if all(graph.degree(v) in EQUALITY_DEGREES for v in nodes):
                cycle = list(combinations(triangle, 2))
                avoid = {v: tuple(edge for edge in cycle if v in edge) for v in triangle}
                pack.append(cycle)
            colors = edge_colors(component)
            cover.update(frozenset((a, b)) for v in nodes for a, b in combinations(incident[v], 2)
                         if colors[a] == colors[b])
        else:
            for v in nodes:
                ordered = sorted(incident[v])
                half = len(ordered) // 2
                for group in (ordered[:half], ordered[half:]):
                    cover.update(frozenset(pair) for pair in combinations(group, 2))
        for v in nodes:
            pack.extend(local_packing(incident[v], avoid.get(v, ())))

    used = set()
    for triangle in pack:
        packed_edges = triangle_edges(triangle)
        assert packed_edges <= available and not packed_edges & used
        used |= packed_edges
    assert cover <= available
    assert all(triangle_edges(triangle) & cover for triangle in triangles(line))
    s = sum(local_cover_size(degree) for _, degree in graph.degree)
    defects = sum(
        part.number_of_edges() % 2 == 1 and all(deg % 2 == 0 for _, deg in part.degree)
        for part in (graph.subgraph(nodes) for nodes in nx.connected_components(graph))
    )
    assert s <= len(cover) <= s + defects
    predicted_equality = root_triangle_count == 0 and all(d in EQUALITY_DEGREES for _, d in graph.degree)
    assert (2 * len(pack) == len(cover)) if predicted_equality else (2 * len(pack) > len(cover))
    return predicted_equality


if __name__ == "__main__":
    for degree in range(201):
        incident = {(0, j + 1) for j in range(degree)}
        packed = [edge for triangle in local_packing(incident) for edge in triangle_edges(triangle)]
        assert len(packed) == len(set(packed))
        assert 2 * (len(packed) // 3) >= local_cover_size(degree)
        assert (2 * (len(packed) // 3) == local_cover_size(degree)) == (degree in EQUALITY_DEGREES)
    atlas = nx.graph_atlas_g()
    equality = sum(check(graph) for graph in atlas)
    print(f"Exact certificates passed on all {len(atlas)} atlas graphs ({equality} predicted equality cases).")
    random = Random(261126)
    for _ in range(100):
        check(nx.gnp_random_graph(random.randrange(8, 25), random.random(), seed=random))
    print("Exact certificates passed on 100 seeded random graphs and local degrees 0–200.")
