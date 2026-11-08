/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FlCoef.Cutoff

/-!
# FL-COEF: multiplication of symbols by a Gevrey-2 multiplier

Supplement Lemma 8.1 in main's normalization. For a multiplier `F(α)` with
`‖D^k F‖ ≤ gev N_F A k` on `ℓ¹`, the symbol `F · m` satisfies the weighted Leibniz bound
`∫∫ w ‖D^k (F m)‖ ≤ Σ_j C(k,j) gev N_F A j · ∫∫ w ‖D^{k-j} m‖`, hence class `J`/`R` bounds with
the *same* radius `A` and constant `4 N_F N`. (The supplement's `(4k)!` is implied: `(2k)! ≤ (4k)!`.)
-/

@[expose] public section

set_option autoImplicit false

namespace WaveTurbulence.Flower.FlCoef

open WaveTurbulence.ClassJR MeasureTheory Finset
open scoped ContDiff ENNReal

section Generic

variable {ι : Type*} [Fintype ι] {Γ : Type*} [MeasureSpace Γ]

/-- The symbol `α, γ ↦ F α * m α γ`. -/
def mulSym (F : (ι → ℝ) → ℂ) (m : (ι → ℝ) → Γ → ℂ) : (ι → ℝ) → Γ → ℂ :=
  fun α γ => F α * m α γ

/-- The `ℓ¹` derivative of a multiplier, as an extended real. -/
noncomputable def FD (k : ℕ) (F : (ι → ℝ) → ℂ) (α : ι → ℝ) : ℝ≥0∞ :=
  ‖iteratedFDeriv ℝ k (fun β : L1 ι => F (WithLp.ofLp β)) (WithLp.toLp 1 α)‖ₑ

theorem contDiff_liftF {F : (ι → ℝ) → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun β : L1 ι => F (WithLp.ofLp β)) :=
  hF.comp (PiLp.continuousLinearEquiv 1 ℝ (fun _ : ι => ℝ)).contDiff

/-- Leibniz bound for `dnorm`. -/
theorem dnorm_mulSym_le {F : (ι → ℝ) → ℂ} {m : (ι → ℝ) → Γ → ℂ} (hF : ContDiff ℝ ∞ F)
    {γ : Γ} (hm : ContDiff ℝ ∞ (fun α => m α γ)) (k : ℕ) (α : ι → ℝ) :
    dnorm k (mulSym F m) α γ ≤
      ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * FD j F α * dnorm (k - j) m α γ :=
  enorm_iteratedFDeriv_mul_le (contDiff_liftF hF) (contDiff_lift1 hm) (WithLp.toLp 1 α) k

theorem symReg_mulSym {F : (ι → ℝ) → ℂ} {m : (ι → ℝ) → Γ → ℂ} {N A : ℝ}
    (hF : ContDiff ℝ ∞ F) (hFb : ∀ k α, FD k F α ≤ gev N A k) (hm : SymReg m)
    [SFinite (volume : Measure Γ)] :
    SymReg (mulSym F m) where
  smooth γ := hF.mul (hm.smooth γ)
  meas := (hF.continuous.stronglyMeasurable.comp_measurable measurable_fst).mul hm.meas
  dom k := by
    have hle : ∀ γ, supD k (mulSym F m) γ ≤
        ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * gev N A j * supD (k - j) m γ := fun γ =>
      iSup_le fun α => (dnorm_mulSym_le hF (hm.smooth γ) k α).trans
        (Finset.sum_le_sum fun j _ => by
          gcongr
          · exact hFb j α
          · exact dnorm_le_supD _ _ _ _)
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
    rw [lintegral_finsetSum' _ fun j _ =>
      (measurable_supD hm.smooth hm.meas (k - j)).const_mul _ |>.aemeasurable]
    refine ENNReal.sum_ne_top.2 fun j _ => ?_
    rw [lintegral_const_mul _ (measurable_supD hm.smooth hm.meas (k - j))]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
      (hm.dom _)

/-- **Weighted Leibniz bound.** For a measurable weight `w`, the weighted `L¹` norm of the `k`-th
derivative of `F m` is controlled by the lower-order weighted norms of `m`, with the Gevrey-2 bound of
`F`. -/
theorem lintegral_dnorm_mulSym_le {F : (ι → ℝ) → ℂ} {m : (ι → ℝ) → Γ → ℂ} {N A : ℝ}
    (hF : ContDiff ℝ ∞ F) (hFb : ∀ k α, FD k F α ≤ gev N A k)
    (hms : ∀ γ, ContDiff ℝ ∞ (fun α => m α γ)) (hm : StronglyMeasurable (Function.uncurry m))
    [SFinite (volume : Measure Γ)] (w : (ι → ℝ) → Γ → ℝ≥0∞)
    (hw : Measurable (Function.uncurry w)) (k : ℕ) :
    ∫⁻ α, ∫⁻ γ, w α γ * dnorm k (mulSym F m) α γ ≤
      ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * gev N A j *
        ∫⁻ α, ∫⁻ γ, w α γ * dnorm (k - j) m α γ := by
  have hmeas : ∀ j, Measurable (Function.uncurry fun α γ => w α γ * dnorm (k - j) m α γ) :=
    fun j => hw.mul (measurable_dnorm hms hm (k - j))
  calc ∫⁻ α, ∫⁻ γ, w α γ * dnorm k (mulSym F m) α γ
      ≤ ∫⁻ α, ∫⁻ γ, ∑ j ∈ range (k + 1),
          (k.choose j : ℝ≥0∞) * gev N A j * (w α γ * dnorm (k - j) m α γ) := by
        refine lintegral_mono fun α => lintegral_mono fun γ => ?_
        calc w α γ * dnorm k (mulSym F m) α γ
            ≤ w α γ * ∑ j ∈ range (k + 1),
              (k.choose j : ℝ≥0∞) * gev N A j * dnorm (k - j) m α γ := by
              gcongr
              refine (dnorm_mulSym_le hF (hms γ) k α).trans (Finset.sum_le_sum fun j _ => ?_)
              gcongr
              exact hFb j α
          _ = _ := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∫⁻ α, ∑ j ∈ range (k + 1), ∫⁻ γ,
          (k.choose j : ℝ≥0∞) * gev N A j * (w α γ * dnorm (k - j) m α γ) := by
        refine lintegral_congr fun α => ?_
        rw [lintegral_finsetSum']
        exact fun j _ => (((hmeas j).of_uncurry_left).const_mul _).aemeasurable
    _ = ∑ j ∈ range (k + 1), ∫⁻ α, ∫⁻ γ,
          (k.choose j : ℝ≥0∞) * gev N A j * (w α γ * dnorm (k - j) m α γ) := by
        rw [lintegral_finsetSum']
        exact fun j _ => (((hmeas j).const_mul _).lintegral_prod_right').aemeasurable
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have hc : (k.choose j : ℝ≥0∞) * gev N A j ≠ ⊤ :=
          ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
        rw [← lintegral_const_mul' _ _ hc]
        refine lintegral_congr fun α => ?_
        rw [lintegral_const_mul _ ((hmeas j).of_uncurry_left)]

end Generic

end WaveTurbulence.Flower.FlCoef
