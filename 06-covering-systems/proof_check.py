"""Independently verify the scoped covering-system claims using integers only."""
from collections import defaultdict
from itertools import product
from pathlib import Path
import json
import math
import random


def exists_bounded_completion(U, tail, W, target):
    """Can some residue choice per modulus leave <= target points of U uncovered?"""
    U = tuple(U)
    W = set(W)
    assert len(set(U)) == len(U) and W <= set(U)
    assert all(d > 0 for d in tail) and target >= 0
    count = len(U)
    U_mask = (1 << count) - 1
    W_mask = sum(1 << i for i, u in enumerate(U) if u in W)
    singleton_count = 0
    groups = []

    for d in tail:
        by_residue = defaultdict(int)
        for i, u in enumerate(U):
            by_residue[u % d] |= 1 << i
        choices = tuple(by_residue.values())
        if max((x.bit_count() for x in choices), default=0) <= 1:
            singleton_count += 1
        else:
            groups.append(choices)

    failed = set()
    nodes = 0

    def visit(todo, covered):
        nonlocal nodes
        nodes += 1
        if covered.bit_count() + target + singleton_count >= count:
            return True  # each singleton-capacity modulus can cover any residual point
        if not todo or (todo, covered) in failed:
            return False
        remainder = U_mask ^ covered
        remaining_witness = W_mask & remainder
        choices_for_branch = []
        upper_witness = upper_all = 0

        for j in range(len(groups)):
            if (todo >> j) & 1:
                choices = tuple({x & remainder for x in groups[j]} - {0}) or (0,)
                mw = max((x & remaining_witness).bit_count() for x in choices)
                ma = max(x.bit_count() for x in choices)
                choices_for_branch.append((j, choices, mw, ma))
                upper_witness += mw
                upper_all += ma

        slack_w = upper_witness + singleton_count + target - remaining_witness.bit_count()
        slack_a = upper_all + singleton_count + target - remainder.bit_count()
        if min(slack_w, slack_a) < 0:
            return False

        updated = []
        for j, choices, mw, ma in choices_for_branch:
            choices = tuple(x for x in choices if
                            (x & remaining_witness).bit_count() >= mw - slack_w and
                            x.bit_count() >= ma - slack_a)
            if not choices:
                return False
            updated.append((len(choices), -mw, -ma, j, choices))
        _, _, _, j, choices = min(updated)
        for choice in choices:
            if visit(todo ^ (1 << j), covered | choice):
                return True
        failed.add((todo, covered))
        return False

    feasible = visit((1 << len(groups)) - 1, 0)
    return feasible, nodes


def direct_holes(L, assignment):
    return sum(all(n % d != r for d, r in assignment.items()) for n in range(L))


def weights_certificate(U, tail, weight):
    """Check lower bound on holes via integer weighted set-cover dual."""
    assert weight and len(weight) == len(set(weight)) and set(weight) <= set(U)
    assert all(w > 0 and isinstance(w, int) for w in weight.values())
    cap = 0
    for d in tail:
        by_residue = defaultdict(int)
        for u, w in weight.items():
            by_residue[u % d] += w
        cap += max(by_residue.values())
    excess = max(0, sum(weight.values()) - cap)
    maximum_weight = max(weight.values())
    return (excess + maximum_weight - 1) // maximum_weight, cap


def read_cert(L, K, assignment, D):
    f = Path(__file__).parent / f'witness-{L}-{K}.json'
    cert = json.loads(f.read_text())
    P = dict(cert["fixed_classes"])
    assert cert['L'] == L and list(P) == D[:K] and all(assignment[d] == r for d, r in P.items())
    U = [n for n in range(L) if all(n % d != r for d, r in P.items())]
    W = dict(cert["weighted_witness"])
    assert len(W) == len(cert["weighted_witness"])
    return U, W, D[K:]


def cases():
    directory = Path(__file__).parent
    for L, seed, small_K, strong_K, expected in [(10080, 11, 25, 35, 84), (15120, 12, 32, 44, 68)]:
        rows = [tuple(map(int, ln.split())) for ln in (directory / f'best-{L}-{seed}.txt').read_text().splitlines()]
        a = dict(rows)
        D = [d for d in range(8, L + 1) if L % d == 0]
        assert sorted(a) == D and len(a) == len(rows)
        assert math.lcm(*D) == L and min(D) == 8 and all(0 <= r < d for d, r in a.items())
        h = direct_holes(L, a)
        assert h == expected
        for K in [small_K, strong_K]:
            U, W, tail = read_cert(L, K, a, D)
            lb, cap = weights_certificate(U, tail, W)
            assert lb > 0
            print(f'L={L}, fixed={K}, tail={len(tail)}, initial holes={len(U)}, '
                  f'witness elements={len(W)}, weight={sum(W.values())}, '
                  f'capacity={cap}, max weight={max(W.values())}: at least {lb} holes')
            if K == strong_K:
                assert set(W.values()) == {1}
                feasible, nodes = exists_bounded_completion(U, tail, W, expected - 1)
                assert not feasible
                print(f'Exact conditional optimum={expected} holes; proof nodes={nodes}')


def fuzz():
    rng = random.Random(173)
    for _ in range(500):
        U = [x for x in range(11) if rng.randrange(3)]
        W = {x for x in U if rng.randrange(2)}
        tail = rng.sample(range(2, 9), rng.randrange(5))
        t = rng.randrange(0, len(U) + 1)
        brute = any(sum(all(x % d != r for d, r in zip(tail, R)) for x in U) <= t
                    for R in product(*(range(d) for d in tail)))
        got, _ = exists_bounded_completion(U, tail, W, t)
        assert got == brute, (U, tail, W, t, got, brute)
    print('Exhaustive oracle agrees on 500 seeded small instances.')


if __name__ == '__main__':
    fuzz()
    cases()
