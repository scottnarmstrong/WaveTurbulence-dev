/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCSource
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAdm
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCSource`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 36: `VCLadderScale` from the lg-spine ladder-gap form (R21 (2)).

`SourceLadderGaps M L w P κ` is, clause for clause, lg-spine's `sourceLadderGapScales G P L base κ` /
`CountingChoices.LadderGaps` (`SourceLadderInputs.lean`, `SourceCountingData.lean`, sha256 in `COPIED-SHA256SUMS`) with
`G.molecule := M`: an `∃` over one realisation `(u, v)` of each maximal ladder, `P S = 0 → r = 0`, `P S / 2 ≤ ‖r‖ ≤ 2 P S`
for `0 < P S < 1` and only `1 ≤ ‖r‖` at `P S = 1`.

`vcLadderScale_of_sourceAdm` derives the vine-level restriction `VCLadderScale` from it, using
(a) realisation independence (`subLadder_gap_norm`) and (b) the observation that the count needs no upper bound at
`P = 1` (`VCPair.pair_unit` uses main's `coupledPair_bound`, which needs only `c⁻¹ P ≤ ‖r‖`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

-- `SourceLadderGaps`, `ladderScaleLow_of_source`: main's (`VineCount`, family-free).

/-- **`VCLadderScale` from the canonical ladder-gap form** of lg-spine (R21 (2)), a decoration with `c = 0` at the
degree-`4` atoms, and the heredity hypotheses `hP1`, `hP2` of `FinalCount.prop94_vine_single`. -/
theorem vcLadderScale_of_sourceAdm {M : Molecule V D} (K : VineCut g M) (hMol : M.IsMolecule)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (L : ℝ) (w : Mom d) (P : Finset V → ℝ)
    (hP1 : ∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S)
    {κ : D → (Fin d → ℤ)} {c : V → Mom d} (hdec : M.IsDecoration L w c κ)
    (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) (h : SourceLadderGaps M L w P κ) : VCLadderScale K L w P κ :=
  vcLadderScale_of_low K hM L w P hP1 hP2 (ladderScaleLow_of_source hMol hdec hc h)

end WaveTurbulence.GammaLow.FinalCount.Step1
