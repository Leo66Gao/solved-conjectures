"""Exact gap-insertion checks on naturally labelled posets of orders 2–6."""

from itertools import combinations, permutations

def verify(n):
    pairs = list(combinations(range(n), 2))
    index = {pair: k for k, pair in enumerate(pairs)}

    transitivity = [
        (
            (1 << index[a, b]) | (1 << index[b, c]),
            1 << index[a, c]
        )
        for a, b, c in combinations(range(n), 3)
    ]

    perms = []

    for perm in permutations(range(n)):
        rank = [0] * n
        for i, v in enumerate(perm):
            rank[v] = i

        forward = sum(
            1 << k for k, (a, b) in enumerate(pairs)
            if rank[a] < rank[b]
        )

        gap = sum(
            1 << k for k, (a, b) in enumerate(pairs)
            if rank[b] - rank[a] >= 2
        )

        perms.append((forward, gap))

    posets = checks = equalities = 0

    for mask in range(1 << len(pairs)):

        if any(
            mask & ab == ab and not mask & ac
            for ab, ac in transitivity
        ):
            continue

        posets += 1
        degrees = [0] * n

        for k, (a, b) in enumerate(pairs):
            if not (mask >> k & 1):
                degrees[a] += 1
                degrees[b] += 1

        D = max(degrees)

        extensions = [
            gap for forward, gap in perms
            if forward & mask == mask
        ]

        total = len(extensions)

        for k, (a, b) in enumerate(pairs):

            if not (mask >> k & 1):
                continue

            separated = sum(
                gap >> k & 1 for gap in extensions
            )

            if separated:
                checks += 1

                assert separated * (D + 1) >= total

                if separated * (D + 1) == total:
                    equalities += 1

    return posets, checks, equalities

if __name__ == "__main__":
    totals = [0, 0, 0]
    for n in range(2, 7):
        row = verify(n)
        totals = [a + b for a, b in zip(totals, row)]
        print(f"Order {n}: {row[0]} posets, {row[1]} applicable checks, {row[2]} equalities")
    assert totals == [5230, 32899, 583]
    print(f"Total: {totals[0]} posets, {totals[1]} exact gap checks, {totals[2]} equalities")
