/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftExpansionFinite
/-! The independent attached-kernel sum and its exact proper-garden summation carrier. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def lowerKernelSum {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (p N : ℕ) (n : Fin w → (Fin d → ℤ)) : ℂ :=
  ∑ D : LowerGraftData sig p N, KG L γ δ F D.low p n

theorem isCanonG_plain {w p : ℕ} {LG : LayeredGarden w} (h : IsCanonG p LG) : LG.garden.IsPlain := by
  cases p with
  | zero => exact False.elim h
  | succ p => exact h.2.1

theorem isCanonG_width {w p : ℕ} {LG : LayeredGarden w} (h : IsCanonG p LG) : 4 ≤ w := by
  cases p with
  | zero => exact False.elim h
  | succ p => exact h.1

theorem LowerGraftData.isCanonG {w p N : ℕ} {sig : Fin w → ℤˣ} (D : LowerGraftData sig p N)
    (hw : 4 ≤ w) : IsCanonG p D.low := by
  rcases D.component with h | h
  · exact h
  · omega

noncomputable def lowerGraftProperEquiv {w p : ℕ} (sig : Fin w → ℤˣ) (N : ℕ) (hw : 4 ≤ w) :
    LowerGraftData sig p N ≃
      {LG : LayeredGarden w // IsCanonG p LG ∧ LG.garden.sig = sig ∧ LG.garden.order ≤ N} :=
  Equiv.ofBijective (fun D => ⟨D.low, D.isCanonG hw, D.sign, D.order_le⟩) (by
    constructor
    · intro D E he
      exact LowerGraftData.low_injective (congrArg Subtype.val he)
    · rintro ⟨LG, hG, hs, ho⟩
      exact ⟨⟨LG, hs, isCanonG_plain hG, Or.inl hG, ho⟩, rfl⟩)

theorem lowerKernelSum_eq_proper_finsum {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (p N : ℕ) (hw : 4 ≤ w) (n : Fin w → (Fin d → ℤ)) :
    lowerKernelSum L γ δ F sig p N n =
      ∑ᶠ LG : {LG : LayeredGarden w // IsCanonG p LG ∧ LG.garden.sig = sig ∧ LG.garden.order ≤ N},
        KG L γ δ F LG.1 p n := by
  have he := finsum_comp_equiv (lowerGraftProperEquiv (p := p) sig N hw)
    (f := fun LG => KG L γ δ F LG.1 p n)
  exact (finsum_eq_sum_of_fintype (fun D : LowerGraftData sig p N => KG L γ δ F D.low p n)).symm.trans he

end WaveTurbulence.Induct
