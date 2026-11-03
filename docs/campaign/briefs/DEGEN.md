# Packet G0 MOLE-COUNT-BASICS (pre-freeze) — DH21 Lemmas 9.13–9.14, DH23 §10.5 degenerate atoms (F21)

Read `COMMON.md` first. Blueprint packet G0. Sources: DH21 `/home/scott/wave-turbulence/references/src-2104.11204/Inventiones-Final_Version.tex`
(Lemmas 9.13–9.14: the counting algorithm's basic steps and the bridge lemma 9.14 `cutlem`), DH23
`/home/scott/wave-turbulence/references/src-2301.07063/Revision_Submit.tex` §10.5 (degenerate atoms), TARGET
`subpro`(3) and FINDINGS F21 (degenerate decorations: k₁ = k₂ = k₃, self-loops, degree-2 atoms; "non-hinge zero-gap atoms
are tame" is new and unproved in TARGET — it is `GAP.degenerate.tame`; work it out). Maps: `maps/DH21.md` (§9),
`maps/DH23.md` (§10), `maps/T-part2.md`.
Work in untracked scratch `/home/scott/wt-scratch/degen/` against the B2 molecules draft (`/home/scott/wt-scratch/waveb2/WaveB2-Molecules.lean`
copy) and B1 snapshot 5; coordinate with wt-nt's MOLE scratch API (`/home/scott/wt-scratch/mole/`, being written now:
import it as it appears). Goals: state and prove DH21 Lemmas 9.13–9.14 in the molecule language of the drafts; the DH23
§10.5 degenerate-atom reductions; `GAP.degenerate.tame` with a written argument (report if it fails). Done: `READY degen`.
