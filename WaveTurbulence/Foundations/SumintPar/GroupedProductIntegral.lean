/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.GroupedTimeBoxes
public import WaveTurbulence.Foundations.SumintPar.BoxProductIntegral

/-!
# Separating pair and normal integrals with linear times fixed

The pair factors may depend on all distinguished linear times. Exact
finite-product Fubini separates their time tuples before the linear
times are integrated, retaining the middle-time parameter in case (a).
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal

namespace WaveTurbulence.SumintPar

/-- Exact grouped product integration, allowing distinguished-time dependence in every pair. -/
theorem lintegral_grouped_product_eq (S : SumintShape) (lo hi : S.TVar → ℝ)
    (F : Fin S.I → ℝ → ℝ≥0∞)
    (G : (Fin S.I → ℝ) → (Σ i : Fin S.I, Fin (S.m i)) → (ℝ × ℝ) → ℝ≥0∞)
    (H : {i : Fin S.I // S.nor i = true} → (Fin 3 → ℝ) → ℝ≥0∞)
    (hG : ∀ u a, Measurable (G u a)) (hH : ∀ i, Measurable (H i)) :
    (∫⁻ u in linearFamilyBox S lo hi,
      ∫⁻ p in pairFamilyBox S lo hi,
        ∫⁻ n in normalFamilyBox S lo hi,
          (∏ i, F i (u i))*(∏ a, G u a (p a))*(∏ i, H i (n i))) =
    ∫⁻ u in linearFamilyBox S lo hi,
      (∏ i, F i (u i)) *
      (∏ a : Σ i : Fin S.I, Fin (S.m i),
        ∫⁻ z in Icc (lo (.inl ⟨a.1,a.2.succ⟩),lo (.inr (.inl a)))
          (hi (.inl ⟨a.1,a.2.succ⟩),hi (.inr (.inl a))), G u a z) *
      (∏ i : {i : Fin S.I // S.nor i = true},
        ∫⁻ z in Icc (fun j => lo (.inr (.inr ⟨i,j⟩)))
          (fun j => hi (.inr (.inr ⟨i,j⟩))), H i z) := by
  have hHN : Measurable (fun n : {i : Fin S.I // S.nor i = true} → Fin 3 → ℝ =>
      ∏ i, H i (n i)) := Finset.measurable_prod _ (fun i _ => (hH i).comp (measurable_pi_apply i))
  have hGN (u : Fin S.I → ℝ) :
      Measurable (fun p : (Σ i : Fin S.I, Fin (S.m i)) → ℝ × ℝ => ∏ a, G u a (p a)) :=
    Finset.measurable_prod _ (fun a _ => (hG u a).comp (measurable_pi_apply a))
  apply lintegral_congr
  intro u
  have he (p : (Σ i : Fin S.I, Fin (S.m i)) → ℝ × ℝ) :
      (∫⁻ n in normalFamilyBox S lo hi,
        (∏ i, F i (u i))*(∏ a, G u a (p a))*(∏ i, H i (n i))) =
      (∏ i, F i (u i))*(∏ a, G u a (p a))*
        (∏ i : {i : Fin S.I // S.nor i = true},
          ∫⁻ z in Icc (fun j => lo (.inr (.inr ⟨i,j⟩)))
            (fun j => hi (.inr (.inr ⟨i,j⟩))), H i z) := by
    rw [lintegral_const_mul _ hHN]
    have hn : (∫⁻ n in normalFamilyBox S lo hi, ∏ i, H i (n i)) =
        ∏ i : {i : Fin S.I // S.nor i = true},
          ∫⁻ z in Icc (fun j => lo (.inr (.inr ⟨i,j⟩)))
            (fun j => hi (.inr (.inr ⟨i,j⟩))), H i z := by
      change (∫⁻ n in Icc (fun i j => lo (.inr (.inr ⟨i,j⟩)))
          (fun i j => hi (.inr (.inr ⟨i,j⟩))), ∏ i, H i (n i)) = _
      exact lintegral_fintype_prod_Icc _ _ H hH
    rw [hn]
  simp_rw [he]
  let NM := ∏ i : {i : Fin S.I // S.nor i = true},
    ∫⁻ z in Icc (fun j => lo (.inr (.inr ⟨i,j⟩)))
      (fun j => hi (.inr (.inr ⟨i,j⟩))), H i z
  have hmul : (∫⁻ p in pairFamilyBox S lo hi,
      ((∏ i, F i (u i))*(∏ a, G u a (p a)))*NM) =
      (∫⁻ p in pairFamilyBox S lo hi, (∏ i, F i (u i))*(∏ a, G u a (p a)))*NM :=
    lintegral_mul_const NM ((measurable_const (a := ∏ i, F i (u i))).mul (hGN u))
  have hconst : (∫⁻ p in pairFamilyBox S lo hi,
      (∏ i, F i (u i))*(∏ a, G u a (p a))) =
      (∏ i, F i (u i))*(∫⁻ p in pairFamilyBox S lo hi, ∏ a, G u a (p a)) :=
    lintegral_const_mul _ (hGN u)
  rw [hmul,hconst]
  have hp : (∫⁻ p in pairFamilyBox S lo hi, ∏ a, G u a (p a)) =
      ∏ a : Σ i : Fin S.I, Fin (S.m i),
        ∫⁻ z in Icc (lo (.inl ⟨a.1,a.2.succ⟩),lo (.inr (.inl a)))
          (hi (.inl ⟨a.1,a.2.succ⟩),hi (.inr (.inl a))), G u a z := by
    change (∫⁻ p in Icc (fun a => (lo (.inl ⟨a.1,a.2.succ⟩),lo (.inr (.inl a))))
        (fun a => (hi (.inl ⟨a.1,a.2.succ⟩),hi (.inr (.inl a)))), ∏ a, G u a (p a)) = _
    exact lintegral_fintype_prod_Icc _ _ (G u) (hG u)
  rw [hp]

end WaveTurbulence.SumintPar
