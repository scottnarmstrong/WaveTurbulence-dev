/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LowerOrderKernelSum
public import WaveTurbulence.Foundations.XChain.ProperTruncSumCarrier
/-! Exact-order attached proper-garden sums are the literal sums controlled by AnsatzAt. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def lowerOrderProperEquiv {w p Natt : ℕ} (sig : Fin w → ℤˣ)
    (N : Fin (Natt + 1)) (hw : 4 ≤ w) :
    {D : LowerGraftData sig p Natt // D.low.garden.order = N.1} ≃
      {LG : LayeredGarden w // IsCanonG p LG ∧ LG.garden.sig = sig ∧ LG.garden.order = N.1} :=
  Equiv.ofBijective (fun D => ⟨D.1.low, D.1.isCanonG hw, D.1.sign, D.2⟩) (by
    constructor
    · intro D E h
      apply Subtype.ext
      exact LowerGraftData.low_injective (congrArg Subtype.val h)
    · rintro ⟨LG, hG, hs, ho⟩
      exact ⟨⟨⟨LG, hs, isCanonG_plain hG, Or.inl hG,
        ho.trans_le (Nat.le_of_lt_succ N.2)⟩, ho⟩, rfl⟩)

theorem lowerOrderKernelSum_eq_proper_finsum {w d p Natt : ℕ} (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ) (N : Fin (Natt + 1)) (hw : 4 ≤ w)
    (n : Fin w → (Fin d → ℤ)) :
    lowerOrderKernelSum L γ δ F sig p Natt N n =
      ∑ᶠ LG : {LG : LayeredGarden w // IsCanonG p LG ∧ LG.garden.sig = sig ∧ LG.garden.order = N.1},
        KG L γ δ F LG.1 p n := by
  classical
  have hsum := (finsum_eq_sum_of_fintype (fun D : LowerGraftData sig p Natt =>
    if D.low.garden.order = N.1 then KG L γ δ F D.low p n else 0)).symm
  have hsub := (finsum_subtype_eq_finsum_cond
    (f := fun D : LowerGraftData sig p Natt => KG L γ δ F D.low p n)
    (fun D => D.low.garden.order = N.1)).symm
  have he := finsum_comp_equiv (lowerOrderProperEquiv (p := p) sig N hw)
    (f := fun LG => KG L γ δ F LG.1 p n)
  have hi : (∑ᶠ D : LowerGraftData sig p Natt,
      if D.low.garden.order = N.1 then KG L γ δ F D.low p n else 0) =
      ∑ᶠ (D : LowerGraftData sig p Natt) (_ : D.low.garden.order = N.1), KG L γ δ F D.low p n := by
    apply finsum_congr
    intro D
    rw [finsum_eq_if]
  exact hsum.trans (hi.trans (hsub.trans he))

theorem lowerOrderKernelSum_eq_truncSum (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    {w : ℕ} (sig : Fin w → ℤˣ) (p : ℕ) (N : Fin (P.N p + 1)) (hw : 4 ≤ w)
    (n : Fin w → (Fin P.d → ℤ)) :
    lowerOrderKernelSum P.L P.γ P.δ F sig p (P.N p) N n = truncSum P F p N.1 p sig n := by
  exact (lowerOrderKernelSum_eq_proper_finsum P.L P.γ P.δ F sig N hw n).trans
    (truncSum_eq_proper_order_finsum P F (Nat.le_of_lt_succ N.2) hw p sig n).symm

end WaveTurbulence.Induct
