# Clean-room proof task (read all of this first)

You are a prover in a clean-room effort. A Lean 4 project (`SchoenfeldRH`, Lean v4.36.0, Mathlib v4.36.0) contains theorem
STATEMENTS whose proofs must be written from scratch. The statements were specified by the project lead; you write the
proofs yourself, from Mathlib (and, where your brief says so, from other files of the project). You have never seen any
earlier proof of these statements in Lean and must not look for one.

## Your tools and environment
- You have ONLY the file tools: read, write, edit, glob, grep. There is no shell and no network. Do not ask for them.
- You work in your own copy of the project, WORKSPACE = /root/clean/ws/NAME/rh, where NAME is your prover id (given below).
  A compile daemon watches your files and compiles them for you. Read /root/clean/ws/NAME/PROTOCOL.md FIRST: it explains
  how to get compiler output (a `.out` file next to each file you write), how to wait for a compile to finish (a grep on a
  named pipe), and how to run experiments (scratch files with `#check`, `exact?`, `#print axioms`, ...).
- Mathlib's sources are in WORKSPACE/.lake/packages/mathlib/Mathlib (search them with grep and glob: this is your
  documentation). Use `exact?`, `apply?`, `simp?`, `#check`, `#loogle`-free methods in scratch files to find lemmas.
- Every other file of the project is in your workspace too. Files owned by other provers contain statements with `sorry`
  (they are being proved in parallel in other workspaces): you may USE those statements as black boxes when your brief says
  so, but never edit them, and do not rely on anything not stated there.

## Rules
- Prove every `sorry` in your owned file(s). Do not change any stated declaration: name, binders, hypotheses, conclusion,
  namespace, and `def` bodies stay exactly as given (a consumer file depends on them). You may add helper lemmas and
  definitions of your own before the stated ones, and helper modules under WORKSPACE/SchoenfeldRH/Lemmas/NAME/ (module names
  `SchoenfeldRH.Lemmas.NAME.Foo`); you may add `import` lines to your owned files for Mathlib modules and your helper modules.
- Forbidden in what you deliver: `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `@[extern]`,
  `debug.skipKernelTC`. No heavy computation (`decide` on big instances, huge `norm_num`): the final proof is replayed by
  six independent kernels, so prefer ordinary mathematical proofs; keep `set_option maxHeartbeats` bumps rare and local.
- Done means: each owned file compiles with EXIT 0, its `.out` shows no error and no `declaration uses sorry` warning for
  your files, and a scratch file with `#print axioms <each stated theorem>` shows only propext, Classical.choice, Quot.sound
  plus `sorryAx` ONLY IF you used a stub of another prover (say which); with no stub used there must be no `sorryAx`.
- If a statement seems false or unprovable as stated, do not weaken it: finish your turn and say exactly why (with a
  counterexample or the precise obstacle). If you are stuck on one statement for a long time, prove the others, then finish
  your turn with a precise description of where you are stuck; the project lead can then help.
- Work efficiently: plan the proof on paper first, find the Mathlib lemmas by grep, write small lemmas, compile often.

## Final reply (goes to the project lead)
List each stated declaration with status (proved / not proved), the helper modules you created, which stubs of other
provers you used, the `#print axioms` result, and anything you want the lead to know. Keep it short.
