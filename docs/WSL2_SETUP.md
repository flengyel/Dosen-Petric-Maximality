# WSL2 checkout

Use the existing WSL2 Linux account `flengyel`. This project does not alter the
FailureOfComposition checkout, its toolchain, or any synchronization mirror.

With GitHub SSH authentication configured:

```bash
mkdir -p /home/flengyel/src
git clone git@github.com:flengyel/Dosen-Petric-Maximality.git /home/flengyel/src/Dosen-Petric-Maximality
cd /home/flengyel/src/Dosen-Petric-Maximality
bash scripts/setup-wsl.sh
```

If the target directory already exists, inspect its Git status and origin
before updating it; do not clone over it or reset local work. Fetch and push
through the existing SSH origin without force.

The setup installs the exact project toolchain with Elan and runs the build
and transitive axiom audit. It does not change Elan's global default, install
Foundation, or copy dependencies from another project. Expected prerequisites
are Git, Python 3, Elan, and `flock` from util-linux. The existing Lean projects
are expected to have supplied Elan; missing prerequisites stop the script.

Initial modules import only Lean core. The matching Mathlib pin is recorded
in `provenance/pins.json`. Add it as an actual Lake dependency when needed,
generate and commit the exact manifest closure, and verify the resulting
project. No Mathlib build or cache is presently required.

GitHub CI compilation, local WSL2 validation and independent kernel checks
are separate evidence records. See docs/VALIDATION.md for current outcomes.

After setup, start Codex in this directory and use `docs/CODEX_NEXT_SESSION.txt`.
Keep one heavy verification process active at a time. Inspect available RAM
and swap before introducing official Comparator replay.
