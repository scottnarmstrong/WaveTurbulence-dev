/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.BilinearSplitIntegral
public import WaveTurbulence.Foundations.Sumint.BilinearTimeSign
public import WaveTurbulence.Foundations.Sumint.NonnegativeTimeRescale

/-!
# The physical-time large-region pair bound

The large-region Weyl reserve survives affine time rescaling and
integration of the outer time, uniformly in its spatial modulations.
This is used when ordering or incoherence strips are discarded only in
the large region.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- The large-region physical pair bound before bad-block exponent reserves are spent. -/
theorem exists_bilinear_minor_physical_window_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ 2 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ (a b : Mom d) (ξ ζ : ℝ → Mom d) (c v w : ℝ), 0 < c → v ≤ w →
      (∫⁻ t in Icc v w, ∫⁻ s : ℝ,
        if L ≤ |c*(s-t)| ∧ |c*(s-t)| ≤ T₀*L^(2*γ) then
          ‖WeylSums.bilinearLatticeSum L (c*(t-s)) a b (ξ t) (ζ t)‖ₑ else 0) ≤
      ENNReal.ofReal ((w-v)*c⁻¹*C*L^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) := by
  obtain ⟨Cs,C,L₀,hCs,hC,hL₀,hbound⟩ :=
    exists_bilinear_split_integral_bound d hd γ hγ η hη T₀ hT₀
  refine ⟨C,L₀,hC,hL₀,?_⟩
  intro L hL a b ξ ζ c v w hc hvw
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (hL₀.trans hL)
  let T := {u : ℝ | L ≤ |u| ∧ |u| ≤ T₀*L^(2*γ)}
  have hT : MeasurableSet T := by dsimp [T]; measurability
  have hb (t : ℝ) :
      (∫⁻ s : ℝ, if L ≤ |c*(s-t)| ∧ |c*(s-t)| ≤ T₀*L^(2*γ) then
        ‖WeylSums.bilinearLatticeSum L (c*(t-s)) a b (ξ t) (ζ t)‖ₑ else 0) ≤
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal (C*L^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) := by
    let F := fun u : ℝ => ‖WeylSums.bilinearLatticeSum L u a b (-(ξ t)) (-(ζ t))‖
    have hcont : Continuous F := (WeylSums.continuous_bilinearLatticeSum hLp a b (-(ξ t)) (-(ζ t))).norm
    have hi : IntegrableOn F T := by
      apply hcont.integrableOn_Icc.mono_set
      intro s hs
      exact abs_le.mp hs.2
    have hn : (∫⁻ u in T, ENNReal.ofReal (F u)) ≤
        ENNReal.ofReal (C*L^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun u => norm_nonneg _))]
      exact ENNReal.ofReal_le_ofReal (hbound L hL a b (-(ξ t)) (-(ζ t))).2
    have he (s : ℝ) :
        (if L ≤ |c*(s-t)| ∧ |c*(s-t)| ≤ T₀*L^(2*γ) then
          ‖WeylSums.bilinearLatticeSum L (c*(t-s)) a b (ξ t) (ζ t)‖ₑ else 0) =
        (T.indicator (fun u => ENNReal.ofReal (F u))) (c*(s-t)) := by
      have hneg : c*(t-s) = -(c*(s-t)) := by ring
      have hnorm : ‖WeylSums.bilinearLatticeSum L (c*(t-s)) a b (ξ t) (ζ t)‖ₑ =
          ENNReal.ofReal (F (c*(s-t))) := by
        rw [← ofReal_norm,hneg,norm_bilinearLatticeSum_time_neg]
      simp only [indicator_apply,mem_ofPred_eq,T,hnorm]
    simp_rw [he]
    rw [lintegral_comp_affine_pos _ hc,lintegral_indicator hT]
    exact mul_le_mul' le_rfl hn
  calc
    _ ≤ ∫⁻ _t in Icc v w, ENNReal.ofReal c⁻¹ *
        ENNReal.ofReal (C*L^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) := lintegral_mono hb
    _ = _ := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end WaveTurbulence.Sumint
