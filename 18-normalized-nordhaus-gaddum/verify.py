"""Numerical checks of the row bound on small graphs and the sharpness family."""

from math import isqrt, sqrt

import networkx as nx
import numpy as np


def check_atlas():
    checked = 0
    for graph in nx.graph_atlas_g():
        if len(graph) < 4:
            continue
        complement = nx.complement(graph)
        if not nx.is_connected(graph) or not nx.is_connected(complement):
            continue
        adjacency = nx.to_numpy_array(graph)
        other = nx.to_numpy_array(complement)
        n = len(graph)
        degrees = adjacency.sum(axis=1)
        design = np.column_stack([np.ones(n), degrees])
        projection = np.eye(n) - design @ np.linalg.pinv(design)

        matrices = []
        for matrix in (adjacency, other):
            degree = matrix.sum(axis=1)
            normalized = matrix / np.sqrt(np.outer(degree, degree))
            eigenvalue = np.linalg.eigvalsh(normalized)[-2]
            matrices.append((matrix, degree, eigenvalue))
        k = 1 + (n - 1) * sum(eigenvalue for _, _, eigenvalue in matrices)
        for matrix, degree, eigenvalue in matrices:
            s = degree.sum()
            psd = (
                eigenvalue * np.diag(degree)
                + (1 - eigenvalue) * np.outer(degree, degree) / s
                - matrix
            )
            assert np.linalg.eigvalsh(psd)[0] >= -1e-10
            lhs = np.sum((matrix @ projection)**2, axis=1) / degree
            rhs = 2 * eigenvalue**2 * degree + 2 * k * (eigenvalue + degree / s)
            assert np.all(lhs <= rhs + 1e-10)
        checked += 1
    print(f"PSD and row inequalities passed on {checked} graph-atlas entries (tolerance 1e-10).")


def sharpness(n):
    # The contrast subspaces contribute one two-by-two block in each graph.
    # The remaining eigenvalues are on the normalized indicators of the three
    # classes: matched clique vertices, unmatched clique vertices, and leaves.
    m = isqrt(n)
    k = n - m
    r = k - m
    block = np.array([
        [(m - 1) / k, sqrt(m * r / (k * (k - 1))), 1 / sqrt(k)],
        [sqrt(m * r / (k * (k - 1))), (r - 1) / (k - 1), 0],
        [1 / sqrt(k), 0, 0],
    ])
    other = np.array([
        [0, 0, sqrt((m - 1) / (n - 2))],
        [0, 0, sqrt(r / (n - 2))],
        [sqrt((m - 1) / (n - 2)), sqrt(r / (n - 2)), (m - 1) / (n - 2)],
    ])
    a = max(np.linalg.eigvalsh(block)[-2], 2 / (sqrt(1 + 4 * k) + 1))
    b = max(np.linalg.eigvalsh(other)[-2], 2 / (sqrt((m - 1)**2 + 4 * (m - 1) * (n - 2)) + m - 1))
    return sqrt(n) * (a + b)


if __name__ == "__main__":
    check_atlas()
    for n in (20, 100, 500, 1000, 10_000, 1_000_000):
        deficit = sharpness(n)
        assert 1 - 1 / sqrt(n) <= deficit
        assert deficit <= sqrt(n) * (1 / sqrt(n - isqrt(n)) + 1 / sqrt((isqrt(n) - 1) * (n - 2)))
        print(f"n={n:>7}: scaled deficit {deficit:.9f}")
