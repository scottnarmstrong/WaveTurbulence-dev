# wt-orch Task 9 — Wave B tier B2 stages 2–3 audit; packaging check of the freeze-ready snapshot

`git merge main` first.

## 9a (when announced, priority): packaging check of `waveb-snap-4`
The drafter is making the B1 freeze set freeze-ready with semantics-neutral packaging only (CL-16+): instances as named
`@[instance, expose] def`, proof-term lemmas inlined into definitions, non-anchor lemmas moved to `WaveB1-Lemmas.lean`,
and `FREEZE-LIST.md` (every frozen declaration with kind, source lines, frozen dependencies). When I announce
`waveb-freezeready`, check against snapshot 3: the only changes are those packaging edits (no change of meaning), every
frozen declaration's dependencies are frozen or Mathlib, FREEZE-LIST is complete and correct, all files elaborate.
File `docs/campaign/orch/audits/WaveB-packaging-check.md`; `READY task9a`.

## 9b (now): refute-first audit of B2 stages 2–3
`/home/scott/wt-scratch/waveb2/` (`WaveB2-Molecules.lean`, `WaveB2-Statements.lean` + probes, `DESIGN.md` Q1–Q8): snapshot
to `/home/scott/wt-scratch/waveb2-snap-1/` (with your stage-1 files) and audit stages 2 (molecules, half-edge encoding
F40, decorations, blocks, vines/ladders F37, gaps, cuts, 𝔈/𝔄/𝔇𝔢𝔳) and 3 (B2.1 regularAsymptotics with the order range
F33, B2.2 incoherentDecay, B2.3 rigidity and its abstract hypotheses). These are not in the next freeze (B2.3 waits for
packet G8, B2.1/B2.2 for C1/C2/C5) — prioritize findings that would change the B1 carriers. File
`docs/campaign/orch/audits/WaveB2-stage23.md`; `READY task9b`.
