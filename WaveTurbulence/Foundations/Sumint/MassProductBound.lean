/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.GroupedTimeBoxes
public import WaveTurbulence.Foundations.Sumint.BoxProductIntegral

/-!
# Inserting uniform factor bounds before the last linear integration

This is a generic nonnegative product-integral inequality. Its local
pair and normal bounds must be supplied by the separately proved source
window estimates; it makes no source oscillatory-gain claim on its own.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- Uniform pair and normal bounds separate from the remaining independent linear integrals. -/
theorem lintegral_linear_family_product_le (S : SumintShape) (lo hi : S.TVar → ℝ)
    (F : Fin S.I → ℝ → ℝ≥0∞) (hF : ∀ i, Measurable (F i))
    (P : (Fin S.I → ℝ) → (Σ i : Fin S.I, Fin (S.m i)) → ℝ≥0∞)
    (B : (Σ i : Fin S.I, Fin (S.m i)) → ℝ≥0∞)
    (N C : {i : Fin S.I // S.nor i = true} → ℝ≥0∞)
    (hP : ∀ u ∈ linearFamilyBox S lo hi, ∀ a, P u a ≤ B a) (hN : ∀ i, N i ≤ C i) :
    (∫⁻ u in linearFamilyBox S lo hi,
      (∏ i, F i (u i))*(∏ a, P u a)*(∏ i, N i)) ≤
      (∏ i : Fin S.I, ∫⁻ s in Icc (lo (.inl ⟨i,0⟩)) (hi (.inl ⟨i,0⟩)), F i s)*
        (∏ a, B a)*(∏ i, C i) := by
  have hm : Measurable (fun u : Fin S.I → ℝ => ∏ i, F i (u i)) :=
    Finset.measurable_prod _ (fun i _ => (hF i).comp (measurable_pi_apply i))
  have hlast : (∫⁻ u in linearFamilyBox S lo hi,
      ((∏ i, F i (u i))*(∏ a, B a))*(∏ i, C i)) =
      (∫⁻ u in linearFamilyBox S lo hi, (∏ i, F i (u i))*(∏ a, B a))*(∏ i, C i) :=
    lintegral_mul_const _ (hm.mul measurable_const)
  have hmiddle : (∫⁻ u in linearFamilyBox S lo hi, (∏ i, F i (u i))*(∏ a, B a)) =
      (∫⁻ u in linearFamilyBox S lo hi, ∏ i, F i (u i))*(∏ a, B a) := lintegral_mul_const _ hm
  have hfirst : (∫⁻ u in linearFamilyBox S lo hi, ∏ i, F i (u i)) =
      ∏ i : Fin S.I, ∫⁻ s in Icc (lo (.inl ⟨i,0⟩)) (hi (.inl ⟨i,0⟩)), F i s :=
    lintegral_fintype_prod_Icc _ _ F hF
  calc
    _ ≤ ∫⁻ u in linearFamilyBox S lo hi, (∏ i, F i (u i))*(∏ a, B a)*(∏ i, C i) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (show MeasurableSet (linearFamilyBox S lo hi) from measurableSet_Icc)] with u hu
      have hp := Finset.prod_le_prod (fun a (_ : a ∈ Finset.univ) => hP u hu a)
      have hn := Finset.prod_le_prod (fun i (_ : i ∈ Finset.univ) => hN i)
      exact mul_le_mul' (mul_le_mul' le_rfl hp) hn
    _ = _ := by rw [hlast,hmiddle,hfirst]

end WaveTurbulence.Sumint
