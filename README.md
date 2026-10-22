# Došen–Petrić maximality in Lean

Development for Florian Lengyel's *Maximality of the Došen–Petrić Boolean Category*, manuscript v4.

The target is maximality of the free zero-identity Boolean category under substitution congruences. The first checkpoint develops preliminary occurrence and zero-arrow lemmas. Contextual collapse, occurrence isolation, and maximality remain open.

## Intended workspace

`/home/flengyel/src/Dosen-Petric-Maximality` in WSL2, on the Linux filesystem.

Lean is pinned to `leanprover/lean4:v4.35.0`. Initial modules use only Lean's core library. The compatible Mathlib release is recorded at full commit `56a005855ea17e0b0958f73ec801ae140b0a1679`; it is not yet a dependency.

## Scope

1. Contextual collapse relative to explicit structural and faithful-interpretation data.
2. Maximality relative to explicit coherence, normalization, presentation, and substitution inputs.
3. Maximality for the actual Došen–Petrić presentation, after those inputs are formally established.

No milestone is claimed merely by assuming its conclusion. Coherence applies in the original category, not in a congruence quotient.

The repository is private. Palomar publication, a public repository, and a distribution license require later decisions. No registry submission has been made.
