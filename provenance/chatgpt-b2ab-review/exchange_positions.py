"""Finite positional check of the proposed exchange repair; not a Lean proof.

All positions may have the same formula label. Integer tags distinguish fixed
occurrences; RETAINED denotes the single identified selected class.
"""

from collections import Counter

RETAINED = "retained"
counts = Counter()

for size in range(2, 8):
    for a in range(size + 1):
        for b in range(size - a + 1):
            for c in range(size - a - b + 1):
                prefix = list(range(a))
                left = list(range(a, a + b))
                right = list(range(a + b, a + b + c))
                suffix = list(range(a + b + c, size))
                before = prefix + left + right + suffix
                after = prefix + right + left + suffix
                for mask in range(1 << size):
                    selected = {i for i in before if (mask >> i) & 1}
                    if len(selected) < 2:
                        continue

                    def erase(xs):
                        return [x for x in xs if x not in selected]

                    def lower(xs):
                        chosen = [x for x in xs if x in selected]
                        assert chosen
                        return [
                            RETAINED if x == chosen[-1] else x
                            for x in xs
                            if x not in selected or x == chosen[-1]
                        ]

                    k0, k1 = lower(before), lower(after)
                    g0, x0, y0 = erase(prefix), erase(left), erase(right)
                    if selected.intersection(suffix):
                        assert k0 == g0 + x0 + y0 + lower(suffix)
                        repair = g0 + y0 + x0 + lower(suffix)
                        regime = "selected suffix"
                    elif selected.intersection(left) and selected.intersection(right):
                        last_x = max(selected.intersection(left))
                        last_y = max(selected.intersection(right))
                        lx = [x for x in left if x < last_x and x not in selected]
                        rx = [x for x in left if x > last_x]
                        ly = [y for y in right if y < last_y and y not in selected]
                        ry = [y for y in right if y > last_y]
                        assert k0 == g0 + lx + rx + ly + [RETAINED] + ry + suffix
                        first_exchange = g0 + ly + [RETAINED] + ry + lx + rx + suffix
                        assert first_exchange == g0 + lower(right) + x0 + suffix
                        repair = g0 + ly + ry + lx + [RETAINED] + rx + suffix
                        regime = "two selected blocks"
                    elif selected.intersection(left):
                        assert k0 == g0 + lower(left) + right + suffix
                        repair = g0 + right + lower(left) + suffix
                        regime = "only X"
                    elif selected.intersection(right):
                        assert k0 == g0 + left + lower(right) + suffix
                        repair = g0 + lower(right) + left + suffix
                        regime = "only Y"
                    else:
                        assert k0 == lower(prefix) + left + right + suffix
                        repair = lower(prefix) + right + left + suffix
                        regime = "only prefix"

                    assert repair == k1
                    assert len(set(k0)) == len(k0) and set(k0) == set(k1)
                    q0 = {x: k0.index(RETAINED if x in selected else x) for x in before}
                    q1 = {x: k1.index(RETAINED if x in selected else x) for x in after}
                    exit_map = {i: k1.index(tag) for i, tag in enumerate(k0)}
                    assert all(q1[x] == exit_map[q0[x]] for x in before)
                    counts[regime] += 1

assert sum(counts.values()) == 21119
print({"positional_cases": sum(counts.values()), "regimes": dict(counts)})
print("PASS: finite tagged-list model only; general Lean proof remains open.")
