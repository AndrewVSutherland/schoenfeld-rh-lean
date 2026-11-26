# Clean-room proof task (read all of this first)

You are a prover in a clean-room effort. A Lean 4 project (`SchoenfeldRH`, Lean v4.36.0, Mathlib v4.36.0) contains ONE
theorem STATEMENT whose proof must be written from scratch. The statement was specified by the project lead; you write the
proof yourself, from Mathlib and from the two project files named below. You have never seen any earlier proof of this
statement in Lean and must not look for one.

## Your tools and environment
- You have ONLY the file tools: read, write, edit, glob, grep. There is no shell and no network. Do not ask for them.
- You work in your own copy of the project, WORKSPACE = /root/clean/ws/p9/rh (your prover id is NAME = p9).
  A compile daemon watches your files and compiles them for you. Read /root/clean/ws/p9/PROTOCOL.md FIRST: it explains
  how to get compiler output (a `.out` file next to each file you write), how to wait for a compile to finish (a grep on a
  named pipe), and how to run experiments (scratch files with `#check`, `exact?`, `#print axioms`, ...).
- Mathlib's sources are in WORKSPACE/.lake/packages/mathlib/Mathlib (search them with grep and glob: this is your
  documentation). Use `exact?`, `apply?`, `simp?`, `#check` in scratch files to find lemmas.

## What you may read (strict)
This is a provenance-controlled task, so the list of files you may open is closed:
- /root/clean/ws/p9/PROTOCOL.md, and the wait pipe / status / compiler-output files it names;
- your owned file `SchoenfeldRH/ZeroSum/RealAxis.lean`, your own scratch files and your own helper modules;
- `SchoenfeldRH/Base/XiDef.lean`, `SchoenfeldRH/Base/Xi.lean`, `SchoenfeldRH/Base/Digamma.lean` (definitions and proved
  theorems you may use as black boxes; your file already imports them);
- anything under WORKSPACE/.lake/packages/ (Mathlib and its dependencies).
Do NOT open, grep or glob any other file or directory: nothing else under `SchoenfeldRH/` (in particular no other file of
`SchoenfeldRH/ZeroSum/`, nothing in `SchoenfeldRH/Explicit*`, `SchoenfeldRH/Lemmas/` of other provers), nothing in
`PrimeNumberTheoremAnd/`, no path outside /root/clean/ws/p9. Always give grep and glob an explicit `path` inside the
allowed places (never the project root or `SchoenfeldRH/` as a whole). Your tool calls are logged and will be audited.

## Rules
- Prove the `sorry` in your owned file. Do not change the stated declaration: name, binders, hypotheses, conclusion and
  namespace stay exactly as given (a consumer file depends on it). You may add helper lemmas of your own before it, and
  helper modules under WORKSPACE/SchoenfeldRH/Lemmas/p9/ (module names `SchoenfeldRH.Lemmas.p9.Foo`); you may add `import`
  lines to your owned file for Mathlib modules and your helper modules.
- Forbidden in what you deliver: `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `@[extern]`,
  `debug.skipKernelTC`. No heavy computation (`decide` on big instances, huge `norm_num`): the final proof is replayed by
  six independent kernels, so prefer ordinary mathematical proofs; keep `set_option maxHeartbeats` bumps rare and local.
- Done means: your owned file compiles with EXIT 0, its `.out` shows no error and no `declaration uses sorry` warning, and
  a scratch file with `#print axioms SchoenfeldRH.re_logDeriv_xiZeta_le` shows only propext, Classical.choice, Quot.sound.
- If the statement seems false or unprovable as stated, do not weaken it: finish your turn and say exactly why (with a
  counterexample or the precise obstacle). If you are stuck for a long time, finish your turn with a precise description
  of where you are stuck; the project lead can then help.
- Work efficiently: plan the proof on paper first, find the Mathlib lemmas by grep, write small lemmas, compile often.

## Your assignment: NAME = p9
Owned file: SchoenfeldRH/ZeroSum/RealAxis.lean (1 statement, `re_logDeriv_xiZeta_le`), helper dir SchoenfeldRH/Lemmas/p9/.
No mathematical notes are supplied: it is a short real-variable estimate; work it out yourself from the facts about
`xiZeta`, `riemannZeta` and the digamma function stated in the two Base files and from Mathlib.

## Final reply (goes to the project lead)
State whether the declaration is proved, the helper modules you created (if any), the `#print axioms` result, a
two-line description of your argument, and anything you want the lead to know. Keep it short.
