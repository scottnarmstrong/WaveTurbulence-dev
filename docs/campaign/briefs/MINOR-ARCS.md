# Packets NT4 MINOR2 + NT11 LEMCUBIC (+ NT3 MINOR1) — minor-arc exponential sums, TARGET Lemmas 5.3 and lemcubic

Read `COMMON.md` first. Blueprint rows (packets NT4, NT11, NT3) in `/home/scott/WaveTurbulence-dev/docs/blueprint/GRAPH.md`:
`DH23.minorarcs2`, `T.lemlayer2`, `GAP.lemcubicRed`, `T.lemcubic`, `DH23.minorarcs1`, `NT.threeVec`.
Same worktree (`/home/scott/WaveTurbulence-worktrees/gausssum`); new branch `git switch -c w/minor-arcs main` (after your
w/hua lands). Files: `WaveTurbulence/Foundations/WeylSums/**` (namespace `WaveTurbulence.WeylSums`), building on your
GAUSSSUM and HUA modules and the landed `Foundations/Fourier/**`.

Note: TARGET Lemma 5.3 (`lemlayer2`) and `lemcubic` are tier-B1 Wave B statements (`quadExpSum2`, `quadExpSum3`) whose
exact Lean forms are being finalized (drafts: `/home/scott/wt-scratch/waveb-snap-2/WaveB1-Statements.lean`; audited
FAITHFUL). Prove them in Foundations under your own names in the form of those drafts (`χ₀` as in the drafts, which
equals the landed `Fourier.chi0`; finite lattice sums); the orchestrator will bridge to the frozen statements.

Goals (commit after each; do not end your turn at milestones):
1. **DH23 Lemma 6.6(2)** (`minorarcs2`, DH23 `/home/scott/wave-turbulence/references/src-2301.07063/Revision_Submit.tex`
   L1090–L1136; note your erratum: L1099 `p·ξ+y·ζ` should be `p·ξ+q·ζ`) and **TARGET Lemma 5.3** (`lemlayer2`, TARGET
   L970–L977).
2. **`lemcubic`** (TARGET L1554–L1593) with the lemcubic-specific reductions (`GAP.lemcubicRed`: the diagonalization
   (u,v,w) = (x+y, x−y, x+y−2z) for Λ = ⟨z,x+y−z⟩ and the level-set argument for Λ = ⟨x,z⟩).
3. **DH23 Lemma 6.6(1)** (`minorarcs1`, L1076–L1090) and the 3-vector count `NT.threeVec`.
Done: `READY minor-arcs`.
