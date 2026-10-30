p=rc/'README.md';t=p.read_text();needle='## Current complete full-paper formalization (29 October 2026)'
assert needle in t and '## Palomar registration release candidate' not in t
insert='''## Palomar registration release candidate (30 October 2026)

The private candidate packages five statements in `DosenPetric.Palomar`: both
actual-source maximality proofs, their congruence dichotomy, a nonzero variable
identity and the empty top-to-bottom hom-set. The independent
[Challenge](Challenge.lean) contains the concrete presentation and five theorem
proof holes; [Solution](Solution.lean) imports the proved production declarations.
[The correspondence account](docs/PALOMAR_STATEMENT_CORRESPONDENCE.md) gives the
raw/quotient relation and derived-negation proofs. The complete-paper scope below
is preserved separately from this five-statement selection.

Use the pinned Lean 4.35.0 toolchain. `lake build Solution` checks the production
proof package. `lake build Challenge` compiles the independent statement; its five
intentional proof warnings are confined to that library. Production checking
retains `warningAsError = true`. `bash scripts/verify.sh` runs the strict build
and transitive axiom audit. The public configuration is [comparator.json](comparator.json).
Protected local comparison and independent-kernel outcomes are recorded in
[the registration report](docs/PALOMAR_REGISTRATION_LOCAL_REPORT.md), with exact
commands, inputs and diagnostics under `provenance/wsl-palomar-registration-20261030/`.

The root metadata, license text and manual-only full-preflight workflow form a
release proposal on this private candidate branch. Apache-2.0, including the
contained original manuscript, and public release of the substantive repository
await the author's concrete decision. The main branch's license and visibility
have not been changed. Official full preflight, service verification, editorial
review and registration remain separate pending stages.

'''
p.write_text(t.replace(needle,insert+needle,1))
p=rc/'scripts/verify.sh';t=p.read_text();t=t.replace("echo 'PASS: build and transitive axiom audit. Palomar verification has not run.'", "echo 'PASS: build and transitive axiom audit. See the registration report for separate Comparator/kernel and official preflight statuses.'");p.write_text(t)
print('Candidate README and strict verification status wording updated')
