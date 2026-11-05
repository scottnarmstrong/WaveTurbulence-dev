/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.FiniteSubtypeOrderSum
public import WaveTurbulence.Foundations.XChain.ProperTruncSumCarrier
public import WaveTurbulence.Foundations.XChain.TruncatedGraftFinite
/-! Every exact total-order slice of the full source truncated proper class is the literal truncSum. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem truncSum_eq_full_truncated_order_finsum (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    {w : ℕ} (hw : 4 ≤ w) (sig : Fin w → ℤˣ) (p N : ℕ) (t : ℝ)
    (n : Fin w → (Fin P.d → ℤ)) :
    truncSum P F (p + 1) N t sig n =
      ∑ᶠ LG : {LG : LayeredGarden w //
        (IsCanonG (p + 1) LG ∧ LG.garden.sig = sig ∧ LG.IsTrunc p (P.N (p + 1)) (P.N p)) ∧
          LG.garden.order = N}, KG P.L P.γ P.δ F LG.1 t n := by
  unfold truncSum
  simp only [Nat.add_sub_cancel_right]
  refine Eq.trans ?_ (finsum_subtype_eq_finsum_cond
    (f := fun LG : LayeredGarden w => KG P.L P.γ P.δ F LG t n)
    (fun LG => (IsCanonG (p + 1) LG ∧ LG.garden.sig = sig ∧
      LG.IsTrunc p (P.N (p + 1)) (P.N p)) ∧ LG.garden.order = N)).symm
  apply finsum_congr
  intro LG
  have hiff : (IsCanonGC (p + 1) LG ∧ LG.IsTrunc p (P.N (p + 1)) (P.N p) ∧
      LG.garden.sig = sig ∧ LG.garden.order = N) ↔
      ((IsCanonG (p + 1) LG ∧ LG.garden.sig = sig ∧
        LG.IsTrunc p (P.N (p + 1)) (P.N p)) ∧ LG.garden.order = N) := by
    rw [isCanonGC_iff_G_of_four_le (p + 1) LG hw]
    constructor
    · rintro ⟨hG, ht, hs, ho⟩
      exact ⟨⟨hG, hs, ht⟩, ho⟩
    · rintro ⟨⟨hG, hs, ht⟩, ho⟩
      exact ⟨hG, ht, hs, ho⟩
  exact finsum_congr_Prop (propext hiff) (fun _ => rfl)

theorem full_truncated_proper_sum_eq_sum_orders_add_tail (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    {w : ℕ} (hw : 4 ≤ w) (sig : Fin w → ℤˣ) (p M : ℕ) (t : ℝ)
    (n : Fin w → (Fin P.d → ℤ)) :
    (∑ᶠ LG : {LG : LayeredGarden w // IsCanonG (p + 1) LG ∧ LG.garden.sig = sig ∧
      LG.IsTrunc p (P.N (p + 1)) (P.N p)}, KG P.L P.γ P.δ F LG.1 t n) =
      (∑ N ∈ range (M + 1), truncSum P F (p + 1) N t sig n) +
        ∑ᶠ LG : {LG : LayeredGarden w // IsCanonG (p + 1) LG ∧ LG.garden.sig = sig ∧
          LG.IsTrunc p (P.N (p + 1)) (P.N p)},
          if M < LG.1.garden.order then KG P.L P.γ P.δ F LG.1 t n else 0 := by
  classical
  let Q : LayeredGarden w → Prop := fun LG => IsCanonG (p + 1) LG ∧ LG.garden.sig = sig ∧
    LG.IsTrunc p (P.N (p + 1)) (P.N p)
  have hf : {LG : LayeredGarden w | Q LG}.Finite :=
    (finite_canonG_truncated w p (P.N (p + 1)) (P.N p)).subset (fun LG h => ⟨h.1, h.2.2⟩)
  haveI : Finite {LG : LayeredGarden w // Q LG} := hf.to_subtype
  letI : Fintype {LG : LayeredGarden w // Q LG} := Fintype.ofFinite _
  simp only [finsum_eq_sum_of_fintype]
  have he := sum_eq_sum_orders_add_tail (fun LG : {LG : LayeredGarden w // Q LG} => LG.1.garden.order)
    (fun LG => KG P.L P.γ P.δ F LG.1 t n) M
  refine he.trans (congrArg (fun z : ℂ => z +
    ∑ LG : {LG : LayeredGarden w // Q LG},
      if M < LG.1.garden.order then KG P.L P.γ P.δ F LG.1 t n else 0) ?_)
  apply sum_congr rfl
  intro N _
  exact (sum_subtype_ite_order_eq_finsum Q (fun LG => LG.garden.order)
    (fun LG => KG P.L P.γ P.δ F LG t n) N).trans
      (truncSum_eq_full_truncated_order_finsum P F hw sig p N t n).symm

end WaveTurbulence.Induct
