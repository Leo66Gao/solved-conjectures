"""Exact closed-threshold prefix audit for posets of range at most four."""

from itertools import combinations
from fractions import Fraction
from collections import Counter

def children(pred, deg, D):
    j = len(pred)
    full = (1 << j) - 1
    B = 2 * D - 1

    for i in range(1 << min(j, B)):
        inc = i << max(0, j - B)

        if inc.bit_count() > D:
            continue

        p = full ^ inc

        # The predecessors of the new element
        # must form an order ideal.
        if any(
            (p >> a & 1) and (pred[a] & inc)
            for a in range(j)
        ):
            continue

        if any(
            (inc >> a & 1) and deg[a] == D
            for a in range(j)
        ):
            continue

        yield (
            pred + (p,),
            tuple(
                deg[a] + (inc >> a & 1)
                for a in range(j)
            ) + (inc.bit_count(),)
        )

def pairs_of(pred):
    return [
        (a, b)
        for b in range(len(pred))
        for a in range(b)
        if not pred[b] >> a & 1
    ]

def matrix(pred, pairs, k):
    n = len(pred)

    # Each state stores its extension count and
    # the counts witnessing each reversal.
    by = {0: [1] + [0] * len(pairs)}

    for _ in range(k):
        new = {}

        for mask, v in by.items():
            for b in range(n):
                if mask >> b & 1:
                    continue
                if pred[b] & mask != pred[b]:
                    continue

                nxt = mask | (1 << b)
                w = new.setdefault(nxt, [0] * len(v))

                for i, x in enumerate(v):
                    w[i] += x

                for t, (a, z) in enumerate(pairs, 1):
                    if z == b and not mask >> a & 1:
                        w[t] += v[0]

        by = new

    return list(by.values())

def certificate(pred, pairs, D):
    k = len(pred) - D

    if k <= 0 or not pairs:
        return False

    V = matrix(pred, pairs, k)

    columns = [
        tuple(3 * v[t + 1] - v[0] for v in V)
        for t in range(len(pairs))
    ]

    # A single comparison suffices.
    if any(min(c) >= 0 for c in columns):
        return True

    # Search exactly for a nonnegative rational
    # combination of two comparison columns.
    for a, b in combinations(columns, 2):
        lo = Fraction(0)
        hi = None

        # Require r*a + b >= 0 in every state.
        for x, y in zip(a, b):
            if x == 0:
                if y < 0:
                    break
            elif x > 0:
                lo = max(lo, Fraction(-y, x))
            else:
                r = Fraction(-y, x)
                hi = r if hi is None else min(hi, r)

            if hi is not None and (hi < lo or hi <= 0):
                break
        else:
            if hi is None or (hi >= lo and hi > 0):
                return True

    return False

def audit(D, maxn):
    survivors = [((), ())]
    finite_cases = 0

    for n in range(1, maxn + 1):
        new = []
        ct = Counter()

        for p, d in survivors:
            for pred, deg in children(p, d, D):
                pairs = pairs_of(pred)

                # Reject cuts which no future
                # incomparable pair can cross.
                if any(
                    not any(a < c <= b for a, b in pairs)
                    for c in range(
                        1, n - (2 * D - 1) + 1
                    )
                ):
                    ct["cut"] += 1
                    continue

                ct["checked"] += 1

                if certificate(pred, pairs, D):
                    ct["certified"] += 1
                    continue

                new.append((pred, deg))

                # Check the finite poset itself whenever
                # its incomparability graph is connected.
                if n >= 2 and all(
                    any(a < c <= b for a, b in pairs)
                    for c in range(1, n)
                ):
                    v = matrix(pred, pairs, n)[0]

                    assert any(
                        3 * x >= v[0] for x in v[1:]
                    ), (pred, pairs, v)

                    ct["finite"] += 1

        survivors = new
        finite_cases += ct["finite"]

        print(n, dict(ct), len(survivors))

        if not survivors:
            return n, finite_cases

    raise AssertionError("Prefix branches remain at the requested depth")


def check_equality_example():
    incomparable = {(0, 1), (1, 2), (2, 4), (3, 4)}
    pred = tuple(sum(1 << a for a in range(b) if (a, b) not in incomparable) for b in range(6))
    pairs = pairs_of(pred)
    assert pairs == sorted(incomparable, key=lambda pair: (pair[1], pair[0]))
    assert sorted(matrix(pred, pairs, 4)) == [[3, 1, 1, 0, 0], [5, 2, 1, 2, 5]]
    assert certificate(pred, pairs, 2)
    print("Equality example: exact prefix counts and closed certificate verified.")


if __name__ == "__main__":
    check_equality_example()
    depth, finite_cases = audit(4, 10)
    assert (depth, finite_cases) == (10, 5692)
    print(f"All range-four branches closed by depth {depth}; {finite_cases} shorter connected cases checked.")
