/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.BilinearFractionalWindow
public import WaveTurbulence.Foundations.Sumint.BilinearTimeSign
public import WaveTurbulence.Foundations.Sumint.WindowRescaleGeneral

/-!
# The case-(c) weighted pair on literal source time intervals

Fixing the outer time fixes the spatial modulations. Conjugation handles
the reversed source time difference and positive affine rescaling keeps
the exact fractional gap multiplier.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Sumint

/-- The weighted source-direction pair estimate on every contained inner interval. -/
theorem exists_bilinear_fractional_affine_window_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ Cs Cm L₀ : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ L₀ ∧
      ∀ L ≥ L₀, ∀ a b ξ ζ : Mom d, ∀ c p l u t : ℝ,
      0 < c → 0 ≤ p → p ≤ 1 → l ≤ u →
      -(T₀*L^(2*γ)) ≤ c*(l-t) → c*(u-t) ≤ T₀*L^(2*γ) →
      (∫ s in Icc l u, |t-s|^p * ‖WeylSums.bilinearLatticeSum L (c*(t-s)) a b ξ ζ‖) ≤
      c⁻¹ * (c^(-p)*Cs*L^(2*d) + (T₀*L^(2*γ)/c)^p *
        Cm*L^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) := by
  obtain ⟨Cs,Cm,L₀,hCs,hCm,hL₀,hbound⟩ :=
    exists_bilinear_fractional_window_bound d hd γ hγ η hη T₀ hT₀
  refine ⟨Cs,Cm,L₀,hCs,hCm,hL₀,?_⟩
  intro L hL a b ξ ζ c p l u t hc hp hp1 hlu hlo hhi
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (hL₀.trans hL)
  let f := fun s : ℝ => |s/c|^p*‖WeylSums.bilinearLatticeSum L s a b (-ξ) (-ζ)‖
  have hf : Continuous f := by
    apply Continuous.mul _ (WeylSums.continuous_bilinearLatticeSum hLp a b (-ξ) (-ζ)).norm
    exact (continuous_abs.comp (continuous_id.div_const c)).rpow_const (fun _ => Or.inr hp)
  have he (s : ℝ) :
      |t-s|^p*‖WeylSums.bilinearLatticeSum L (c*(t-s)) a b ξ ζ‖ = f (c*(s-t)) := by
    have hneg : c*(t-s) = -(c*(s-t)) := by ring
    have hdiv : c*(s-t)/c = s-t := by field_simp
    dsimp [f]
    rw [hneg,norm_bilinearLatticeSum_time_neg,hdiv,abs_sub_comm t s]
  simp_rw [he]
  have hi : IntegrableOn f (Icc (-(T₀*L^(2*γ))) (T₀*L^(2*γ))) := hf.integrableOn_Icc
  calc
    _ ≤ c⁻¹ * ∫ s in Icc (-(T₀*L^(2*γ))) (T₀*L^(2*γ)), f s :=
      integral_Icc_affine_le_symmetric f hc hlu t hi
        (fun s => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (norm_nonneg _)) hlo hhi
    _ ≤ _ := by
      have hb := hbound L hL a b (-ξ) (-ζ) c p hc hp hp1
      rw [abs_window_eq_Icc] at hb
      exact mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hc.le)

end WaveTurbulence.Sumint
