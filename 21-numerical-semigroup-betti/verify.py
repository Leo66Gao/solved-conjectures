"""Compare the cone-homology formula with the tangent-cone Koszul differential."""

EXAMPLES = {
    (2, 3): (1, 1, 0),
    (3, 4, 5): (1, 3, 2, 0),
    (5, 6, 19): (1, 4, 4, 1),
    (5, 21, 69): (1, 3, 2, 0),
    (5, 31, 99): (1, 3, 2, 0),
    (8, 9, 10, 12, 23): (1, 8, 16, 14, 6, 1),
    (8, 81, 90, 108, 207): (1, 8, 16, 13, 4, 0),
}


def rank(columns, prime):
    pivots = {}
    for column in columns:
        column = {i: value % prime for i, value in column.items() if value % prime}
        while column:
            lead = min(column)
            if lead not in pivots:
                scale = pow(column[lead], -1, prime)
                pivots[lead] = {i: value * scale % prime for i, value in column.items()}
                break
            scale = column[lead]
            for i, value in pivots[lead].items():
                residue = (column.get(i, 0) - scale * value) % prime
                if residue:
                    column[i] = residue
                else:
                    column.pop(i, None)
    return len(pivots)


def homology(faces, boundary, dimension, prime):
    grouped = [[f for f in faces if f.bit_count() == degree] for degree in range(dimension + 2)]
    ranks = [rank((boundary(f) for f in group), prime) for group in grouped]
    return tuple(len(grouped[i]) - ranks[i] - ranks[i + 1] for i in range(dimension + 1))


def deletions(face):
    remaining = face
    sign = 1
    while remaining:
        bit = remaining & -remaining
        yield face ^ bit, bit.bit_length() - 1, sign
        remaining ^= bit
        sign = -sign


def verify(gens, prime):
    size = len(gens)
    bound = (gens[0] - 1) * gens[-1] + sum(gens)
    orders = [0]
    for weight in range(1, bound):
        longest_prefix = max((orders[weight - g] for g in gens if g <= weight), default=-1)
        orders.append(longest_prefix + 1 if longest_prefix >= 0 else -1)
    face_weights = {f: sum(g for i, g in enumerate(gens) if f & (1 << i))
                    for f in range(1 << size)}
    apex = 1 << size
    totals = [0] * (size + 1)
    checked = 0

    for s in range(bound):
        if orders[s] < 0:
            continue
        residual = {f: s - w for f, w in face_weights.items() if w <= s and orders[s - w] >= 0}
        levels = {f: orders[w] + f.bit_count() for f, w in residual.items()}
        for j in range(s // gens[0] + 1):
            cone = {f for f, level in levels.items() if level >= j}
            cone |= {f | apex for f, level in levels.items() if level > j}
            if not cone:
                continue

            def simplicial_boundary(face):
                return {sub: sign for sub, _, sign in deletions(face)}

            koszul = {f for f, w in residual.items() if orders[w] == j - f.bit_count()}

            def multiplication_boundary(face):
                w = residual[face]
                return {sub: sign for sub, index, sign in deletions(face)
                        if orders[w + gens[index]] == orders[w] + 1}

            observed = homology(cone, simplicial_boundary, size, prime)
            expected = homology(koszul, multiplication_boundary, size, prime)
            assert observed == expected, (gens, prime, s, j, observed, expected)
            totals = [a + b for a, b in zip(totals, observed)]
            checked += 1
    return tuple(totals), checked


if __name__ == "__main__":
    for prime in (2, 3, 101):
        count = 0
        for generators, expected in EXAMPLES.items():
            observed, strands = verify(generators, prime)
            assert observed == expected, (generators, prime, observed)
            count += strands
            print(f"GF({prime:>3}) {str(generators):>25}: {observed}")
        print(f"{count} cone and Koszul strands agreed over GF({prime}).")
