/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCSubLadder
public import WaveTurbulence.Foundations.Spine.SourceCountingData
/-! # VINE-COUNT part 36: `VCLadderScale` from the lg-spine ladder-gap form (R21 (2)).

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
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- **The canonical ladder-gap clause of `Adm`** (lg-spine `sourceLadderGapScales` with `G.molecule := M`). -/
def SourceLadderGaps (M : Molecule V D) (L : ℝ) (w : Mom d) (P : Finset V → ℝ) (κ : D → (Fin d → ℤ)) : Prop :=
  ∀ S ∈ M.maximalLadders,
    (P S = 0 ∨ (IsDyadicScale (P S) ∧ L⁻¹ ≤ P S ∧ P S ≤ 1)) ∧
    ∃ m : ℕ, ∃ u v : Fin (m + 1) → V, ∃ hm : 1 ≤ m,
      M.IsLadder u v ∧ Molecule.ladderAtoms u v = S ∧
      ∃ r, M.IsLadderGap L w κ u v hm r ∧
        (P S = 0 → r = 0) ∧
        (0 < P S → P S < 1 → P S / 2 ≤ ‖r‖ ∧ ‖r‖ ≤ 2 * P S) ∧
        (P S = 1 → 1 ≤ ‖r‖)

/-- The `∃`-form gives the `∀`-form (lower bounds only), for decorations. -/
theorem ladderScaleLow_of_source {M : Molecule V D} {L : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {κ : D → (Fin d → ℤ)} {c : V → Mom d} (hMol : M.IsMolecule) (hdec : M.IsDecoration L w c κ)
    (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) (h : SourceLadderGaps M L w P κ) : LadderScaleLow M L w P κ := by
  intro m u v hl r hr S hS hsub
  obtain ⟨hP, n, U, W, hm, hladU, hat, R, hR, h0, h1, h2⟩ := h S hS
  have hmem : u 0 ∈ Molecule.ladderAtoms U W := by
    rw [hat]
    apply hsub
    unfold Molecule.ladderAtoms
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
  have hn := subLadder_gap_norm hMol hdec hc hladU hl hmem hR hr
  rcases hP with hP0 | ⟨⟨z, hz⟩, hlo, hhi⟩
  · left
    exact ⟨hP0, by simpa [h0 hP0] using hn⟩
  · right
    have hpos : 0 < P S := by rw [hz]; positivity
    refine ⟨hlo, hhi, ?_⟩
    rw [hn]
    rcases lt_or_eq_of_le hhi with hlt | heq
    · have := (h1 hpos hlt).1
      linarith
    · have := h2 heq
      linarith

/-- **`VCLadderScale` from the canonical ladder-gap form** of lg-spine (R21 (2)), a decoration with `c = 0` at the
degree-`4` atoms, and the heredity hypotheses `hP1`, `hP2` of `FinalCount.prop94_vine_single`. -/
theorem vcLadderScale_of_sourceAdm {M : Molecule V D} (K : VineCut M) (hMol : M.IsMolecule)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (L : ℝ) (w : Mom d) (P : Finset V → ℝ)
    (hP1 : ∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S)
    {κ : D → (Fin d → ℤ)} {c : V → Mom d} (hdec : M.IsDecoration L w c κ)
    (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) (h : SourceLadderGaps M L w P κ) : VCLadderScale K L w P κ :=
  vcLadderScale_of_low K hM L w P hP1 hP2 (ladderScaleLow_of_source hMol hdec hc h)

end WaveTurbulence.VineCount
