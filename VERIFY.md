# Verifying the proof with `lake comparator --paranoid`

`Challenge.lean` states the theorem using Mathlib only, and leaves it as `sorry`:

```lean
theorem schoenfeld_strict_bound_iff_riemannHypothesis :
    (∀ x : ℝ, 73.2 ≤ x → |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi)) ↔
      RiemannHypothesis
```

`Solution.lean` proves it. `comparator.json` names the theorem and permits only the axioms
`propext`, `Quot.sound` and `Classical.choice`. `lake comparator` builds and exports both modules inside a
bubblewrap sandbox with no network. It then checks that the solution states exactly the challenge's
theorem and uses no other axioms. With `--paranoid`, the export is replayed by Lean's kernel and by the
five external checkers bundled with the toolchain: `leanchecker-paranoid`, `lean4lean`, `nanoda`,
`con-leche` and `con-ron`.

## Prerequisites

- x86_64 Linux, `git`, `curl`, about 15 GB free disk and 16 GB RAM (more cores make the build faster).
- A **non-root** user.
- `bubblewrap` with working unprivileged user namespaces. Test it with
  `bwrap --ro-bind / / --dev /dev --proc /proc --unshare-all true && echo ok`.

## Commands

```sh
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
source ~/.elan/env
cd <this repository>                       # lean-toolchain selects leanprover/lean4:v4.35.0 automatically
lake exe cache get                         # Mathlib 56a00585 and its dependencies per lake-manifest.json, with the build cache
ulimit -s unlimited
PATH="$(dirname "$(elan which lean)"):$PATH" lake comparator --paranoid     # reads comparator.json
echo "exit code: $?"                       # 0 = accepted, 1 = rejected, 2 = could not start
```

`lake comparator` looks for the bundled checkers on the `PATH`, which is why the toolchain's `bin` directory is added.

A passing run ends with

```
Lean default kernel accepts the solution
Your solution is okay!
```

The outputs of independent runs on this repository are published at <https://math.mit.edu/~drew/shortgrh/>.
