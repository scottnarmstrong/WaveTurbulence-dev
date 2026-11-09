/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Discharge
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepS10b
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepS10a
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepCnt4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepCountA
public import WaveTurbulence.Foundations.Stage1.Shared.SkelFacts3
import Mathlib.Tactic
/-! # The piece counts of the producer over `𝒱_γ` (packet L5a, item J)

Main's `Represents.prod_stage1Counts` (`Stage1/Represents/RepS10b.lean`) over the `𝒱_γ` producer `prodData`
(`Stage1DataG`): the `Stage1CountsG` clauses (AMEND10, R56) from L5c's class count `ClassCountStmtG` through
`pieceCount_of_rep` with the fibre bound `3^N` (`fibre_card_le`), and the `r̄`/`ḡ` bounds of `RepCnt4`. The garden
count is stated for the splice piece `Fama.stage1PieceOf`; the normalized piece has the same skeleton, layering,
`g_sk`, `b_sk` (it differs only in the collection and gap choices), so its `(ḡ, r̄)` agree definitionally. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Fama.Represents
open scoped Classical
open Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed

/-- **The producer's piece counts over `𝒱_γ`** (main's `prod_stage1Counts`, from L5c's `ClassCountStmtG`). -/
theorem prod_stage1Counts (hcc : Famc.ClassCount.ClassCountStmtG) :
    ∃ C₀ K : ℕ, 2 ≤ C₀ ∧ ∀ (P : WTParams) [hγ : Fact (P.γ ≤ 1 / 2)], K ^ (P.D + 1) ≤ P.C₂ → ∀ p, p < P.D →
      ∀ R, 1 ≤ R → ∀ N, 1 ≤ N → ∀ (kind : Bool) (A : Finset (LayeredGarden (2 * R))),
      (∀ LG ∈ A, Stage1Carries P p N LG) → ∀ (val : PcA P.γ R p kind A → ℂ),
      Stage1CountsG C₀ P R N (prodData P p kind A val) (ClA P.γ R p kind A) inferInstance (clsP P.γ) := by
  obtain ⟨C₀, K, hC₀, hmain⟩ := pieceCount_of_rep hcc
  refine ⟨C₀, K, hC₀, ?_⟩
  intro P hγ hK p hp R hR N hN kind A hA val
  have hrep : ∀ π : PcA P.γ R p kind A, (repPt P.γ π).layered.garden.order = N :=
    fun π => (hA _ (repPt_layered_mem π)).2.2.1
  refine ⟨fun π => ?_, fun π => ?_, ?_⟩
  · have hc := hA _ (repPt_layered_mem π)
    have hn1 : 1 ≤ (repPt P.γ π).prime.skeleton.order := by
      obtain ⟨-, -, h⟩ := WaveTurbulence.Represents.skelFacts_of_carries P p N hR hc (repPt P.γ π).prime
      exact h
    exact stage1Piece_rbar_bounds P.d (repPt P.γ π).prime.prime.1 (repPt P.γ π).layered (repPt P.γ π).prime.decodes
      (VineA.PrescribedPrimeGarden.totalSigma P.γ (repPt P.γ π)) hn1 (prod_piece_gsb_order P p N kind A hA π)
  · have hsz := (repPt P.γ π).prime.data.decoded_order (repPt P.γ π).prime.prime.1 (repPt P.γ π).prime.decodes
    have hord := hrep π
    exact stage1Piece_gbar_le P.d (repPt P.γ π).prime.prime.1 (repPt P.γ π).layered (repPt P.γ π).prime.decodes
      (VineA.PrescribedPrimeGarden.totalSigma P.γ (repPt P.γ π)) (by omega)
  · intro g r
    have := hmain P hγ.out hK p hp R hR N hN (prodData P p kind A val) (fun π => (repPt P.γ π).layered) (3 ^ N)
      (fun π => ⟨hA _ (repPt_layered_mem π), ?_⟩)
      (fun LG => ?_) g r
    · have h2 := this
      simp only [prodData] at h2 ⊢
      push_cast at h2
      calc _ ≤ _ := h2
        _ = _ := by ring
    · exact ⟨_, (repPt P.γ π).prime.data, (repPt P.γ π).prime.prime.1, (repPt P.γ π).prime.decodes,
        VineA.PrescribedPrimeGarden.totalSigma P.γ (repPt P.γ π), rfl, rfl⟩
    · by_cases h : ∃ π : PcA P.γ R p kind A, (repPt P.γ π).layered = LG
      · obtain ⟨π, hπ⟩ := h
        have hpl : LG.garden.IsPlain := hπ ▸ (repPt P.γ π).prime.decodes.1
        exact fibre_card_le p kind A LG hpl (by rw [← hπ]; exact hrep π)
      · refine le_trans (le_of_eq (Finset.card_eq_zero.2 ?_)) (Nat.zero_le _)
        rw [Finset.filter_eq_empty_iff]
        intro π _ hπ
        exact h ⟨π, hπ⟩

end WaveTurbulence.GammaLow.Fama.Represents
