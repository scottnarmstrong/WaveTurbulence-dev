# Packets NT7 COUNT0 + NT8 COUNT — DH23 Lemmas A.2, A.3 (TARGET Lemmas A.8, A.9): `countLemma`, `atomCountLemma`

Read `COMMON.md` first. Blueprint packets NT7, NT8. Worktree `/home/scott/WaveTurbulence-worktrees/gausssum`; new branch
`git switch -c w/count main` (after w/minor-arcs lands). Files: `WaveTurbulence/Foundations/Counting/LatticeCount*/**` or a
new `Foundations/CountLemmas/**` (namespace `WaveTurbulence.CountLemmas`; coordinate names with wt-nt's
`Foundations/Counting/**`, which you may import but not edit).

These two are frozen-candidate Wave B statements (`countLemma` = B1.7, `atomCountLemma` = B1.8; exact drafts in
`/home/scott/wt-scratch/waveb-snap-5/WaveB1-Statements.lean`). Prove them in Foundations in exactly the drafted form
(copy the statement, under your own name; the orchestrator bridges to the frozen anchor at sealing).

Sources: DH23 `/home/scott/wave-turbulence/references/src-2301.07063/Revision_Submit.tex` L2027–L2117 (Lemmas A.1–A.3;
FINDINGS F3, F31: the annulus bound with exponent 2/3 suffices for A.2 (1),(3) and A.3; A.2 (2) needs e < 2/3 — it is
NOT part of `countLemma`'s drafted items, but prove it as well once wt-nt/wt-ansob land the exponent-pair circle bound);
TARGET L2459–L2478 (`countlem`, `atomcountlem`; F43: k ≠ 0 for ε = (+,−)). Landed inputs: wt-nt's circle/annulus/estcross
(`Foundations/Counting/**`, `Foundations/NumberTheory/**`), your three-vector count `NT.threeVec` (MINOR-ARCS), DH21
Prop 6.1 / Lemma A.9(2)-type counting (DH23 cites them; check the maps for exact forms).
Goals (do not end your turn at milestones): `atomCountLemma`; `countLemma` (items as drafted); DH23 A.2(2) when the
e < 2/3 circle bound lands. Done: `READY count`.
