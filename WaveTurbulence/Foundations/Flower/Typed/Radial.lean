/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Typed.Jets
public import WaveTurbulence.Foundations.FC23.RadialMeasure
public import WaveTurbulence.Foundations.FC23.FrozenRadialBridge
public import WaveTurbulence.Foundations.Fourier.Chi0
public import WaveTurbulence.Foundations.Spine.WeightedSmoothMultiplier
/-! # FL-TYPED: scale-uniform derivative bounds of the radial cutoff `x ↦ χ₀(‖x‖/s)`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.Typed
open WaveTurbulence.NormBridgeScratch Finset

variable {d : ℕ}

/-- The radial cutoff at scale `s`. -/
def Rc (s : ℝ) (x : Mom d) : ℝ := chi0 (‖x‖ / s)

theorem Rc_nonneg (s : ℝ) (x : Mom d) : 0 ≤ Rc s x := by
  unfold Rc; rw [FC23.frozen_chi0_eq]; exact Fourier.chi0_nonneg _

theorem Rc_le_one (s : ℝ) (x : Mom d) : Rc s x ≤ 1 := by
  unfold Rc; rw [FC23.frozen_chi0_eq]; exact Fourier.chi0_le_one _

theorem Rc_eq_one {s : ℝ} (hs : 0 < s) {x : Mom d} (hx : ‖x‖ ≤ s / 2) : Rc s x = 1 := by
  unfold Rc; rw [FC23.frozen_chi0_eq]
  apply Fourier.chi0_eq_one
  rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hs.le), div_le_iff₀ hs]
  linarith

theorem Rc_cast_eq {s : ℝ} (hs : 0 < s) :
    (fun x : Mom d => ((Rc s x : ℝ) : ℂ)) = fun x => FC23.radialCut (s⁻¹ • x) := by
  funext x
  unfold Rc FC23.radialCut
  rw [FC23.frozen_chi0_eq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le), div_eq_inv_mul]

theorem Rc_contDiff {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Mom d => ((Rc s x : ℝ) : ℂ)) := by
  rw [Rc_cast_eq hs]
  exact FC23.radialCut_smooth.comp (contDiff_const_smul _)

theorem radial_jets (N : ℕ) : ∃ γ : ℕ → ℝ, (∀ k, 0 ≤ γ k) ∧ γ 0 = 1 ∧
    ∀ s : ℝ, 0 < s → JetW N (fun k _ => γ k * (s⁻¹) ^ k) (fun x : Mom d => ((Rc s x : ℝ) : ℂ)) := by
  refine ⟨fun k => if k = 0 then 1 else SchwartzMap.seminorm ℝ 0 k (FC23.radialSchwartz (V := Mom d)),
    fun k => ?_, by simp, fun s hs l hl x => ?_⟩
  · show 0 ≤ (if k = 0 then (1:ℝ) else _)
    split_ifs
    · exact zero_le_one
    · exact apply_nonneg _ _
  · by_cases h0 : l.length = 0
    · have : l = [] := List.length_eq_zero_iff.mp h0
      subst this
      simp only [wordD, List.length_nil, ite_true, pow_zero, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      rw [abs_of_nonneg (Rc_nonneg s x)]
      exact Rc_le_one s x
    · simp only [h0, ite_false]
      have hc : ContDiff ℝ (l.length : WithTop ℕ∞) (fun x : Mom d => ((Rc s x : ℝ) : ℂ)) :=
        (Rc_contDiff hs).of_le (by exact_mod_cast le_top)
      have e1 : wordD l (fun x : Mom d => ((Rc s x : ℝ) : ℂ)) =
          Fourier.momentumDerivative (fun i : Fin l.length => l.get i)
            (fun x : Mom d => ((Rc s x : ℝ) : ℂ)) := by
        rw [momentumDerivative_eq_wordD _ hc, List.ofFn_get]
      rw [e1]
      refine (LGSpine.norm_momentumDerivative_le_frechet _ _ x).trans ?_
      rw [Rc_cast_eq hs, iteratedFDeriv_comp_const_smul s⁻¹ (FC23.radialCut_smooth.of_le (by exact_mod_cast le_top)),
        norm_smul, norm_pow, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
      have := SchwartzMap.le_seminorm ℝ 0 l.length (FC23.radialSchwartz (V := Mom d)) (s⁻¹ • x)
      simp only [pow_zero, one_mul] at this
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right this (pow_nonneg (inv_nonneg.mpr hs.le) _)

end WaveTurbulence.Flower.Typed
