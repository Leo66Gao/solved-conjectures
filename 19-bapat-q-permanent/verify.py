"""Check arithmetic bounds and the endpoint identity on small real Gram matrices."""

from collections import defaultdict
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, factorial, prod
from random import Random


def check_bounds():
    radius, grid, angles = 100, 100_000, 10**14
    order = 100 * grid * angles**2
    row_bound = 1 + radius**2
    anchor = Fraction(1, 100)
    delta = Fraction(1, 10**5)
    inner_radius = Fraction(1, 10**17)
    gap = Fraction(1, 10**13)
    assert order == 10**35
    assert 2 * row_bound < 150**2
    discretization = Fraction(1, radius) + Fraction(radius, grid) + Fraction(32, angles)
    assert discretization < Fraction(12, 1000)
    gini = (1 - anchor)**2 * Fraction(314, 400) + anchor * (1 - anchor) - Fraction(12, 1000)
    assert gini > Fraction(767, 1000)
    eta = 150 * delta
    error = (2 * eta + eta**2) / (1 - eta)**2
    assert error < Fraction(4, 1000)
    assert Fraction(767, 1000) - 2 * error > Fraction(3, 4)
    # Upper-bound log(2) by 1 in the outer-tube estimate.
    assert anchor * delta**2 / 2 - Fraction(4, angles) > gap
    assert 300 * inner_radius < gap / 10
    assert gap * order > 400 and 800 * 10**102 < 2**400
    assert Fraction(99, 100) * Fraction(9, 16) * order**4 > (
        Fraction(11, 10) * comb(order, 2) * (order + 3) * (order + 2)
    )
    assert Fraction(1, 20) - Fraction(1, 1000 * (row_bound + 1)) > Fraction(1, 25)
    assert Fraction(1, 25) - Fraction(1, 100) > 0


def polynomial_product(rows, rank):
    coefficients = {(0,) * rank: 1}
    for row in rows:
        next_coefficients = defaultdict(int)
        for power, coefficient in coefficients.items():
            for axis, entry in enumerate(row):
                exponent = list(power)
                exponent[axis] += 1
                next_coefficients[tuple(exponent)] += coefficient * entry
        coefficients = next_coefficients
    return coefficients


def factorial_norm(coefficients):
    return sum(value**2 * prod(map(factorial, power)) for power, value in coefficients.items())


def check_identity(rows):
    order, rank = len(rows), len(rows[0])
    pairs = list(combinations(range(order), 2))
    gram = [[sum(a * b for a, b in zip(x, y)) for y in rows] for x in rows]
    permanent = derivative = 0
    for sigma in permutations(range(order)):
        term = prod(gram[i][j] for i, j in enumerate(sigma))
        permanent += term
        derivative += term * sum(sigma[i] > sigma[j] for i, j in pairs)
    assert factorial_norm(polynomial_product(rows, rank)) == permanent
    exterior_norm = 0
    for a, b in combinations(range(rank), 2):
        coefficients = defaultdict(int)
        for i, j in pairs:
            wedge = rows[i][a] * rows[j][b] - rows[i][b] * rows[j][a]
            factors = [row for k, row in enumerate(rows) if k not in (i, j)]
            for power, coefficient in polynomial_product(factors, rank).items():
                coefficients[power] += wedge * coefficient
        exterior_norm += factorial_norm(coefficients)
    assert 2 * derivative == len(pairs) * permanent - exterior_norm


if __name__ == "__main__":
    check_bounds()
    print("Exact rational bounds passed.")
    random = Random(261126)
    for order in range(2, 8):
        for rank in range(2, 5):
            for _ in range(4):
                check_identity([[random.randrange(-3, 4) for _ in range(rank)] for _ in range(order)])
    print("Endpoint identity matched direct permutation sums on 72 exact integer Gram matrices.")
