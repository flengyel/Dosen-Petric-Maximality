"""Finite toy check of v5 Appendix A.2; not a proof of the general statement."""
from itertools import product

cases = points = empty_sources = empty_selected_blocks = 0
for k in range(3):
    for m in range(4):
        for mu in product(range(k), repeat=m):
            for ls in product(range(3), repeat=k):
                for ns in product(range(3), repeat=k):
                    maps = [list(product(range(l), repeat=n)) for l, n in zip(ls, ns)]
                    for nus in product(*maps):
                        source_offsets = [0]
                        target_offsets = [0]
                        for i in mu:
                            source_offsets.append(source_offsets[-1] + ns[i])
                        for l in ls:
                            target_offsets.append(target_offsets[-1] + l)
                        D = [(r, j) for r in range(m) for j in range(1, ns[mu[r]] + 1)]
                        C = [(i, j) for i in range(k) for j in range(1, ls[i] + 1)]
                        assert sorted(source_offsets[r] + j for r, j in D) == list(
                            range(1, source_offsets[-1] + 1)
                        )
                        assert sorted(target_offsets[i] + j for i, j in C) == list(
                            range(1, target_offsets[-1] + 1)
                        )
                        for r, j in D:
                            x = source_offsets[r] + j
                            b = min(i for i in range(1, m + 1) if x <= source_offsets[i])
                            fibre_value = target_offsets[mu[r]] + nus[mu[r]][j - 1] + 1
                            book_value = (
                                nus[mu[b - 1]][x - source_offsets[b - 1] - 1]
                                + 1
                                + target_offsets[mu[b - 1]]
                            )
                            assert fibre_value == book_value
                            assert 1 <= fibre_value <= target_offsets[-1]
                            points += 1
                        cases += 1
                        empty_sources += not D
                        empty_selected_blocks += any(ns[i] == 0 for i in mu)
print({
    "cases": cases,
    "points": points,
    "empty_sources": empty_sources,
    "cases_with_empty_selected_blocks": empty_selected_blocks,
    "status": "all assertions passed",
})
