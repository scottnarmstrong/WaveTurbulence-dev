/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LowerKernelSum
public import WaveTurbulence.Foundations.XChain.FiniteOrderSums
/-! The lower proper-garden sum is precisely the order sum in the source induction hypothesis. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem isCanonGC_iff_G_of_four_le {w : ℕ} (q : ℕ) (LG : LayeredGarden w) (hw : 4 ≤ w) :
    IsCanonGC q LG ↔ IsCanonG q LG := by
  cases q with
  | zero => rfl
  | succ p =>
    constructor
    · rintro ⟨hp, h | h, hc⟩
      · exact ⟨hw, hp, h.2, hc⟩
      · omega
    · rintro ⟨_, hp, hi, hc⟩
      exact ⟨hp, Or.inl ⟨hw, hi⟩, hc⟩

theorem truncSum_eq_proper_order_finsum (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    {q N w : ℕ} (hN : N ≤ P.N q) (hw : 4 ≤ w) (t : ℝ)
    (sig : Fin w → ℤˣ) (n : Fin w → (Fin P.d → ℤ)) :
    truncSum P F q N t sig n =
      ∑ᶠ LG : {LG : LayeredGarden w // IsCanonG q LG ∧ LG.garden.sig = sig ∧ LG.garden.order = N},
        KG P.L P.γ P.δ F LG.1 t n := by
  rw [truncSum_untruncated P F hN]
  have he : (∑ᶠ (LG : LayeredGarden w) (_ : IsCanonGC q LG ∧ LG.garden.sig = sig ∧ LG.garden.order = N),
      KG P.L P.γ P.δ F LG t n) =
      ∑ᶠ (LG : LayeredGarden w) (_ : IsCanonG q LG ∧ LG.garden.sig = sig ∧ LG.garden.order = N),
        KG P.L P.γ P.δ F LG t n := by
    apply finsum_congr
    intro LG
    exact finsum_congr_Prop (propext (and_congr_left (fun _ => isCanonGC_iff_G_of_four_le q LG hw))) (fun _ => rfl)
  exact he.trans (finsum_subtype_eq_finsum_cond
    (f := fun LG => KG P.L P.γ P.δ F LG t n)
    (fun LG => IsCanonG q LG ∧ LG.garden.sig = sig ∧ LG.garden.order = N)).symm

theorem lowerKernelSum_eq_sum_truncSum (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    {w : ℕ} (sig : Fin w → ℤˣ) (q : ℕ) (hw : 4 ≤ w) (n : Fin w → (Fin P.d → ℤ)) :
    lowerKernelSum P.L P.γ P.δ F sig q (P.N q) n =
      ∑ N ∈ range (P.N q + 1), truncSum P F q N q sig n := by
  rw [lowerKernelSum_eq_proper_finsum P.L P.γ P.δ F sig q (P.N q) hw]
  have hf : {LG : LayeredGarden w | (IsCanonG q LG ∧ LG.garden.sig = sig) ∧ LG.garden.order ≤ P.N q}.Finite :=
    (Canon.finite_canonG q (P.N q) w).subset (fun LG h => ⟨h.1.1, h.2⟩)
  have hs := finsum_boundedOrder_eq_sum_orders (fun LG : LayeredGarden w => IsCanonG q LG ∧ LG.garden.sig = sig)
    (fun LG => LG.garden.order) (P.N q) hf (fun LG => KG P.L P.γ P.δ F LG q n)
  have hi : (∑ᶠ LG : {LG : LayeredGarden w // IsCanonG q LG ∧ LG.garden.sig = sig ∧ LG.garden.order ≤ P.N q},
      KG P.L P.γ P.δ F LG.1 q n) =
      ∑ N : Fin (P.N q + 1), truncSum P F q N.1 q sig n := by
    have hleft : (∑ᶠ LG : {LG : LayeredGarden w // IsCanonG q LG ∧ LG.garden.sig = sig ∧ LG.garden.order ≤ P.N q},
        KG P.L P.γ P.δ F LG.1 q n) =
        ∑ᶠ LG : {LG : LayeredGarden w // (IsCanonG q LG ∧ LG.garden.sig = sig) ∧ LG.garden.order ≤ P.N q},
          KG P.L P.γ P.δ F LG.1 q n := by
      exact finsum_eq_of_bijective (fun LG => ⟨LG.1, ⟨LG.2.1, LG.2.2.1⟩, LG.2.2.2⟩)
        ⟨(fun a b h => Subtype.ext (congrArg (fun LG : {LG : LayeredGarden w //
          (IsCanonG q LG ∧ LG.garden.sig = sig) ∧ LG.garden.order ≤ P.N q} => LG.1) h)),
          (fun LG => ⟨⟨LG.1, LG.2.1.1, LG.2.1.2, LG.2.2⟩, rfl⟩)⟩ (fun _ => rfl)
    refine hleft.trans (hs.trans ?_)
    apply sum_congr rfl
    intro N _
    have hN : N.1 ≤ P.N q := Nat.le_of_lt_succ N.2
    have hc := truncSum_eq_proper_order_finsum P F hN hw q sig n
    have he : (∑ᶠ LG : {LG : LayeredGarden w // (IsCanonG q LG ∧ LG.garden.sig = sig) ∧ LG.garden.order = N.1},
        KG P.L P.γ P.δ F LG.1 q n) =
        ∑ᶠ LG : {LG : LayeredGarden w // IsCanonG q LG ∧ LG.garden.sig = sig ∧ LG.garden.order = N.1},
          KG P.L P.γ P.δ F LG.1 q n := by
      exact finsum_eq_of_bijective (fun LG => ⟨LG.1, LG.2.1.1, LG.2.1.2, LG.2.2⟩)
        ⟨(fun a b h => Subtype.ext (congrArg (fun LG : {LG : LayeredGarden w //
          IsCanonG q LG ∧ LG.garden.sig = sig ∧ LG.garden.order = N.1} => LG.1) h)),
          (fun LG => ⟨⟨LG.1, ⟨LG.2.1, LG.2.2.1⟩, LG.2.2.2⟩, rfl⟩)⟩ (fun _ => rfl)
    exact he.trans hc.symm
  exact hi.trans (Fin.sum_univ_eq_sum_range (fun N => truncSum P F q N q sig n) (P.N q + 1))

end WaveTurbulence.Induct
