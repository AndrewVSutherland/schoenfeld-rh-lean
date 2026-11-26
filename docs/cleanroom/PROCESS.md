# The clean-room re-proof (2026-11-26)

## Why

The first complete version of this project depended on code from
[senamakel/erdos-985](https://github.com/senamakel/erdos-985) @ `9538edb7`, a repository without a licence:

- 16 vendored files (2,030 lines): the function ξ and its basic properties, growth and zeros; Hadamard factorization in
  logarithmic-derivative form; Mellin/Perron lemmas; the digamma series. 30 declarations of these files were used
  (32 with their closure).
- erdos-985's modified copy of the Hadamard library of PrimeNumberTheoremAnd (36 modules).
- Five of the project's own files (`Explicit/{Weighted,Formula,LogDeriv,Kernel}.lean`, `ZeroSum/Basic.lean`) had been
  written by agents that were told to study erdos-985; between 4% and 45% of their lines were identical to lines of it.

The request was to re-prove everything used from erdos-985, with provers that get the statements and Mathlib and do not
use the internet.

## What was specified

The project lead (Claude Fable 5.2, who had read erdos-985 and had designed the overall argument) wrote a
statement-only specification: the declarations that the retained part of the proof consumes, each with its proof replaced
by `sorry`. Internal lemmas of the old proofs were deleted, not specified. Where the old interface was an erdos-985
internal one (its general Perron profile `prof`, its `gammaLogDeriv`, its real digamma `rD`), the statement was replaced
by one in Mathlib's terms. The specification was checked two ways: every statement follows from the old development (so
it is true), and the retained files compile against the stubs.

| Prover | File | Statements |
|---|---|---|
| p1 | `Base/Xi.lean` | `differentiable_xiZeta`, `xiZeta_eq`, `xiZeta_zero`, `xiZeta_one`, `deriv_xiZeta_zero`, `deriv_xiZeta_one`, `xiZeta_zero_re_mem`, `countable_xiZeta_zeros`, `logDeriv_riemannZeta_eq` |
| p1 | `Base/Constants.lean` | `re_two_mul_completedRiemannZeta₀_one`, `two_add_eulerMascheroni_sub_log_lt` |
| p2 | `Base/Growth.lean` | `xiZeta_growth` |
| p3 | `Base/Hadamard.lean` | `hadamard_logDeriv` |
| p4 | `Base/Digamma.lean` | `hasSum_digamma`, `digamma_ofReal`, `realDigamma_bounds` (def `realDigamma`) |
| p5 | `ZeroSum/Basic.lean` | `xiZeta_zero_re_of_RH`, `xiZeta_ne_zero_of_RH`, `xiZeta_zero_ne_zero`, `norm_sq_of_re_eq_half`, `norm_sq_shift_sub`, `hasSum_hadamard_xiZeta`, `hasSum_zero_inv_norm_sq`, `summable_zero_inv_norm_sq`, `tsum_zero_inv_norm_sq_le`, `hasSum_poisson`, `zeroSumW_term_nonneg`, `summable_zeroSumW`, `zeroSumW_nonneg` |
| p6 | `Explicit/Kernel.lean` | `integrable_kappa`, `perron_kernel`, `pair_mul_kappa`, `integral_pairK`, `integral_norm_pairK_le` (defs `pairK`, `pairE`) |
| p7 | `Explicit/Weighted.lean` | `integrable_Kmu`, `integral_Kmu`, `perron_weighted_mu` (def `Kmu`) |
| p7 | `Explicit/LogDeriv.lean` | `trivZero_re`, `trivZero_ne_zero`, `norm_trivZero`, `hasSum_trivZero`, `neg_logDeriv_zeta_eq` (def `trivZero`) |
| p8 | `Explicit/Formula.lean` | `explicit_formula_mu` |
| p9 | `ZeroSum/RealAxis.lean` | `re_logDeriv_xiZeta_le` (added after the audit, see below) |

That is 44 theorem statements and 5 definitions in 11 files. `Base/XiDef.lean` (the one-line definition of `xiZeta`) was
written by the lead and is the standard normalization; it is the same line as in erdos-985.

The Hadamard library was not re-proved: the 36 modules were taken, byte-identical, from the true upstream
[AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) @ `a4fb6989`
(Apache-2.0). They build unchanged on Lean/Mathlib v4.36.0.

## How the provers were isolated

- A fresh cloud VM, set up by an infrastructure agent whose instructions allowed only Lean, Mathlib (with its
  dependencies) and PrimeNumberTheoremAnd to be fetched. No file of erdos-985 or schoenfeld-rh was ever put on it.
- Each prover was a Claude Opus 5.5 agent started with exactly five tools: `read`, `write`, `edit`, `glob`, `grep`.
  It had no shell and therefore no way to reach the network or to run a program.
- Each prover had its own copy of the project (statements as stubs, Mathlib sources, the PrimeNumberTheoremAnd files).
  A compile daemon compiled the files a prover wrote and put the compiler's output next to them; a `grep` on a named
  pipe served as "wait for the compile to finish".
- Each prover received `briefs/clean-common.md` plus its own brief (`briefs/clean-pN.md`). The briefs of p1–p8 contain
  the lead's mathematical notes: proof sketches in words and names of relevant Mathlib theorems, no Lean proofs. p9 got
  no mathematical notes (`briefs/clean-p9.md` is its complete brief).
- Only the files a prover owned (`owners.tsv`) were collected from its workspace.

Limits of this isolation, stated plainly:

- The tool restriction is a restriction of the agent interface, not an operating-system jail.
- The lead had read erdos-985, and the specification keeps the architecture of the old proof: the statements, and the
  notes in the briefs, are not independent of it. What is new is every proof.
- The workspaces of p1–p8 also contained the retained files of the project. One of them, `ZeroSum/Bound.lean`, then
  still began with the passage that the audit later flagged (below). The recorded tool calls show that no prover opened
  that file.
- The infrastructure agent had a shell and network access. It wrote no proofs; an independent replay of the provers'
  recorded writes and edits reproduces the collected proof files byte for byte.
- Nobody can exclude that a language model has seen any public repository during its training.

## What was checked afterwards

By the lead:

- All statements and definitions in the collected files are identical to the specification (also compared as elaborated
  types on the VM); the retained files are unchanged; `Challenge.lean` is unchanged.
- `lake build Solution`: no error, no `sorry`; `#print axioms` gives `propext`, `Classical.choice`, `Quot.sound` for the
  two final theorems and for every specified statement.
- The provers' transcripts: only the five tools were used, every path was inside the prover's own workspace, and no
  transcript mentions an excluded source.
- Line overlap of the new files with erdos-985 (non-comment lines of at least 30 characters that also occur anywhere in
  erdos-985): 61 of 2,520 lines (2.4%), mostly the specified statement lines; before the re-proof `Explicit/Weighted.lean`
  alone was at 45%.
- `lake comparator --paranoid` on the result (see `VERIFY.md`).

By an independent GPT-6.2 Astra agent (`AUDIT-D.md`, with an addendum for p9):

- 320 recorded tool calls of p1–p8: all within the assigned workspaces; no forbidden source fetched or read.
- Replay of every successful write and edit from the stub commit: all 13 proof files byte-identical to the collected
  commit.
- The 36 PrimeNumberTheoremAnd files and the licence: identical to the upstream blobs at the pinned commit.
- File-by-file comparison of the new proofs with the old ones and with erdos-985: verdicts "independent" or
  "convergent" (same standard mathematics and Mathlib API, different proof text); a few two- or three-line coincidences
  are listed in the report.
- **One adverse finding, in a file that had been retained:** the first two lemmas of `ZeroSum/Bound.lean` (the sign of
  ζ′/ζ on the real axis and the resulting bound for ξ′/ξ) had been written earlier by an agent that had read the
  corresponding file of the GPL-3 project [senamakel/schoenfeld-rh](https://github.com/senamakel/schoenfeld-rh), and a
  six-line passage agreed with it up to the name of one variable.

## The follow-up (p9)

The flagged passage was removed. The one statement the rest of `ZeroSum/Bound.lean` needs, `re_logDeriv_xiZeta_le`,
was moved to a stub file `ZeroSum/RealAxis.lean`. Before the ninth prover started, the old workspaces and every
plain-text copy of the removed proof were deleted from the VM (the infrastructure agent searched the filesystem for
the removed lines). p9 was told which files it may open (its own, `Base/XiDef.lean`, `Base/Xi.lean`,
`Base/Digamma.lean`, Mathlib) and got no mathematical notes.

p9 proved it in 25 tool calls, all on the allowed files. Its proof gets the sign of ζ′/ζ from the nonnegativity of the
von Mangoldt L-series in the order on ℂ, and reduces the estimate to one rational inequality whose difference has
numerator proportional to β² − 25/4. The auditor's follow-up (`AUDIT-D-p9.md`) replayed p9's edits (byte-identical),
checked the clean-up of the VM from the infrastructure agent's transcript, and compared the new file with the removed
passage, with schoenfeld-rh and with erdos-985: one arithmetic line (`1/(2β)/2 = 1/(4β)`, proved by `field_simp; ring`)
is identical to a line of the removed proof, which p9 could not read; the long matching run that had been flagged
is absent. Verdict: pass for the source tree, no further re-proof recommended.

For orientation, the line overlap of the final tree with the two excluded repositories (non-comment lines of at least 30
characters that occur anywhere in the other repository, `Converse/PsiBigO.lean` and the generated data file excluded):
59 of 2,216 lines (2.7%) for erdos-985 and 55 of 2,216 (2.5%) for schoenfeld-rh. For schoenfeld-rh these are import
lines and one-line idioms such as `have hx0 : 0 < x := by linarith`; the rate is the same in files written by provers
that never had access to it, so it is the background rate of Mathlib-style Lean, not a sign of copying. For erdos-985
they are mostly the specified statement lines in `Base/Xi.lean` and `Base/Hadamard.lean`.

The published history of this repository starts after this step, so it contains neither the erdos-985 files nor the
removed passage.

## Files here

- `briefs/clean-common.md`, `briefs/clean-p1.md` … `clean-p8.md`: the briefs (each prover got common + its own).
- `briefs/clean-p9.md`: the complete brief of p9.
- `owners.tsv`: which paths each prover owned.
- `AUDIT-D.md`: the independent audit. The few lines of third-party code that the report quoted have been replaced by
  a marked omission.
- `AUDIT-D-p9.md`: the auditor's check of the follow-up.
