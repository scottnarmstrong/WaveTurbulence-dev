/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.FiniteSubtypeOrderSum
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Trunc
public import WaveTurbulence.Foundations.XChain.ProperTruncSumCarrier
public import WaveTurbulence.Foundations.XChain.TruncatedGraftFinite
/-! Every exact total-order slice of the full source truncated couple class is the literal truncSum. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem truncSum_couple_eq_full_truncated_order_finsum (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (p N : ℕ) (t : ℝ)
    (n : Fin 2 → (Fin P.d → ℤ)) :
    truncSum P F (p + 1) N t ![1, -1] n =
      ∑ᶠ LG : {LG : LayeredGarden 2 //
        (IsCanonC (p + 1) LG ∧ LG.IsTrunc p (P.N (p + 1)) (P.N p)) ∧
          LG.garden.order = N}, KG P.L P.γ P.δ F LG.1 t n := by
  unfold truncSum
  simp only [Nat.add_sub_cancel_right]
  refine Eq.trans ?_ (finsum_subtype_eq_finsum_cond
    (f := fun LG : LayeredGarden 2 => KG P.L P.γ P.δ F LG t n)
    (fun LG => (IsCanonC (p + 1) LG ∧
      LG.IsTrunc p (P.N (p + 1)) (P.N p)) ∧ LG.garden.order = N)).symm
  apply finsum_congr
  intro LG
  have hiff : (IsCanonGC (p + 1) LG ∧ LG.IsTrunc p (P.N (p + 1)) (P.N p) ∧
      LG.garden.sig = ![1, -1] ∧ LG.garden.order = N) ↔
      ((IsCanonC (p + 1) LG ∧ LG.IsTrunc p (P.N (p + 1)) (P.N p)) ∧ LG.garden.order = N) := by
    constructor
    · rintro ⟨hG, ht, _, ho⟩
      exact ⟨⟨(Canon.isCanonGC_iff_isCanonC (p + 1) LG).mp hG, ht⟩, ho⟩
    · rintro ⟨⟨hG, ht⟩, ho⟩
      exact ⟨(Canon.isCanonGC_iff_isCanonC (p + 1) LG).mpr hG, ht,
        (Canon.isCouple_of_isCanonC hG).2, ho⟩
  exact finsum_congr_Prop (propext hiff) (fun _ => rfl)

theorem full_truncated_couple_sum_eq_sum_orders_add_tail (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (p M : ℕ) (t : ℝ)
    (n : Fin 2 → (Fin P.d → ℤ)) :
    (∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧
      LG.IsTrunc p (P.N (p + 1)) (P.N p)}, KG P.L P.γ P.δ F LG.1 t n) =
      (∑ N ∈ range (M + 1), truncSum P F (p + 1) N t ![1, -1] n) +
        ∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧
          LG.IsTrunc p (P.N (p + 1)) (P.N p)},
          if M < LG.1.garden.order then KG P.L P.γ P.δ F LG.1 t n else 0 := by
  classical
  let Q : LayeredGarden 2 → Prop := fun LG => IsCanonC (p + 1) LG ∧
    LG.IsTrunc p (P.N (p + 1)) (P.N p)
  have hf : {LG : LayeredGarden 2 | Q LG}.Finite :=
    (finite_canonC_truncated p (P.N (p + 1)) (P.N p)).subset (fun LG h => h)
  haveI : Finite {LG : LayeredGarden 2 // Q LG} := hf.to_subtype
  letI : Fintype {LG : LayeredGarden 2 // Q LG} := Fintype.ofFinite _
  simp only [finsum_eq_sum_of_fintype]
  have he := sum_eq_sum_orders_add_tail (fun LG : {LG : LayeredGarden 2 // Q LG} => LG.1.garden.order)
    (fun LG => KG P.L P.γ P.δ F LG.1 t n) M
  refine he.trans (congrArg (fun z : ℂ => z +
    ∑ LG : {LG : LayeredGarden 2 // Q LG},
      if M < LG.1.garden.order then KG P.L P.γ P.δ F LG.1 t n else 0) ?_)
  apply sum_congr rfl
  intro N _
  exact (sum_subtype_ite_order_eq_finsum Q (fun LG => LG.garden.order)
    (fun LG => KG P.L P.γ P.δ F LG t n) N).trans
      (truncSum_couple_eq_full_truncated_order_finsum P F p N t n).symm

end WaveTurbulence.Induct
