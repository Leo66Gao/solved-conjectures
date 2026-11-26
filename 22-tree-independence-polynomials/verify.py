from math import comb

D = 98

def mul(a, b):
    c = [0] * min(D + 1, len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b[:len(c)-i]):
            c[i+j] += x * y
    return c

def power(a, n):
    r = [1]
    while n:
        if n & 1:
            r = mul(r, a)
        n //= 2
        if n:
            a = mul(a, a)
    return r

def linear(c, n):
    # Coefficients of (c+y)^n
    return [
        comb(n, j) * c**(n-j)
        for j in range(min(n, D)+1)
    ]

def accumulate(dst, src, shift=0):
    for j, a in enumerate(src[:len(dst)-shift]):
        dst[j+shift] += a

m, n, k, h = 46, 96, 51, 16

# H_k(y) = (1+y)^k + y(2+y)^k
H = [0] * (k+2)
accumulate(H, linear(1, k))
accumulate(H, linear(2, k), 1)

R = [0] * (D+1)

# Neither central vertex selected
accumulate(
    R,
    mul(mul(power(H, m+n), linear(2, h)),
        linear(1, 2))
)

# Vertex u selected
accumulate(
    R,
    mul(mul(power(H, n), linear(2, k*m)),
        linear(1, h+2)),
    m-1
)

# Vertex v selected
accumulate(
    R,
    mul(power(H, m), linear(2, k*n+h)),
    n+1
)

assert all(
    R[j-1] * R[j+1] > R[j]**2
    for j in range(90, 98)
)

print("Verified: eight consecutive violations.")


def construct_tree():
    parents = [-1, 0]

    def add(parent):
        parents.append(parent)
        return len(parents) - 1

    for root, stars in ((0, m), (1, n)):
        for _ in range(stars):
            center = add(root)
            for _ in range(k):
                add(add(center))
    for _ in range(h):
        add(add(0))
    add(1)
    add(1)
    return parents


def add_polynomials(first, second):
    # Each pair records the true degree and the highest retained coefficients.
    top = max(first[0], second[0])
    coefficients = [0] * (D + 1)
    for degree, values in (first, second):
        accumulate(coefficients, values, top - degree)
    return top, coefficients


def tree_dp(parents):
    children = [[] for _ in parents]
    for child, parent in enumerate(parents[1:], 1):
        children[parent].append(child)
    states = [None] * len(parents)
    for v in reversed(range(len(parents))):
        omit_degree, take_degree = 0, 1
        omit, take = [1], [1]
        for child in children[v]:
            child_omit, child_take = states[child]
            total_degree, total = add_polynomials(child_omit, child_take)
            omit_degree += total_degree
            omit = mul(omit, total)
            take_degree += child_omit[0]
            take = mul(take, child_omit[1])
            states[child] = None
        states[v] = ((omit_degree, omit), (take_degree, take))
    return add_polynomials(*states[0])


parents = construct_tree()
degree, coefficients = tree_dp(parents)
assert len(parents) == 14662 and degree == 7402
assert coefficients == R
print(f"Rooted-tree dynamic program agrees on degree {degree} and the top {D + 1} coefficients.")
