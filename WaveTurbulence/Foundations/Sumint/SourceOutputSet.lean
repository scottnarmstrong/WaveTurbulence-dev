/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.OutputCover
public import WaveTurbulence.Foundations.Sumint.LatticeFacts

/-!
# The exact drafted sumint output family is finite

The set is the literal output set in the snapshot-5 conclusion. Its
coset, unit-ball and nonzero-difference premises give the finite output
count and the lower momentum bound used by the kernel estimates.
-/

public section
open Set
open scoped Classical
namespace WaveTurbulence.Sumint

/-- The literal output family appearing in the drafted sumint restriction norm. -/
@[expose] def sourceOutputSet {d : ℕ} (D : SumintDatum d) (L γ η : ℝ) : Set (Fin 4 → Mom d) :=
  {v | (∀ c, (∃ nv : Fin d → ℤ, v c = D.wBar+latticePoint L nv) ∧ ‖v c-D.centre c‖ ≤ 1) ∧
    v 0-v 1 = v 3-v 2 ∧ v 0 ≠ v 1 ∧ ‖v 0-v 1‖ ≤ L^(-γ+η)}

/-- Every literal allowed output lies in the explicit finite unit-ball lattice cover. -/
theorem sourceOutputSet_subset_cover {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L) (γ η : ℝ) :
    sourceOutputSet D L γ η ⊆ (outputCover D L:Set (Fin 4 → Mom d)) :=
  fun _ hv => mem_outputCover D hL _ hv.1

/-- The exact source output set is finite. -/
theorem finite_sourceOutputSet {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L) (γ η : ℝ) :
    (sourceOutputSet D L γ η).Finite :=
  (outputCover D L).finite_toSet.subset (sourceOutputSet_subset_cover D hL γ η)

/-- Every nonzero literal output difference satisfies both native source momentum bounds. -/
theorem sourceOutputSet_momentum_bounds {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L) (γ η : ℝ)
    (v : sourceOutputSet D L γ η) : 1/L ≤ ‖v.1 0-v.1 1‖ ∧ ‖v.1 0-v.1 1‖ ≤ L^(-γ+η) := by
  refine ⟨?_,v.2.2.2.2⟩
  simpa only [one_div] using inv_le_norm_coset_difference hL (v.2.1 0).1 (v.2.1 1).1 v.2.2.2.1

/-- The cardinality of the exact source output family is bounded by the four unit-ball lattice counts. -/
theorem card_sourceOutputSet_le {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 1 ≤ L) (γ η : ℝ)
    [Fintype (sourceOutputSet D L γ η)] :
    (Fintype.card (sourceOutputSet D L γ η):ℝ) ≤ (3*L)^(4*d) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hi : Function.Injective (fun v : sourceOutputSet D L γ η =>
      (⟨v.1,sourceOutputSet_subset_cover D hLp γ η v.2⟩ : (outputCover D L:Set (Fin 4 → Mom d)))) := by
    intro v w h
    exact Subtype.ext (congrArg (fun q : (outputCover D L:Set (Fin 4 → Mom d)) => q.1) h)
  have hc := Fintype.card_le_of_injective _ hi
  have hr : (Fintype.card (sourceOutputSet D L γ η):ℝ) ≤ (outputCover D L).card := by
    have hc' : Fintype.card (sourceOutputSet D L γ η) ≤ (outputCover D L).card := by
      have hcard : Fintype.card (outputCover D L:Set (Fin 4 → Mom d)) = (outputCover D L).card :=
        Fintype.card_of_finset' (outputCover D L) (fun _ => Iff.rfl)
      exact hc.trans_eq hcard
    exact_mod_cast hc'
  exact hr.trans (card_outputCover_le D hL)

end WaveTurbulence.Sumint
