/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ScalarFourierMass
public import WaveTurbulence.Foundations.Fourier.Chi0

/-!
# Explicit smooth compact inverse-exponential multiplier

The scalar plateau has radius 2(N+1), so it equals one throughout the
actual sheared output coordinates of magnitude at most N. Its signs
are +1 in the first coordinate and -1 in the other two coordinates.
All resulting scalar Fourier constants depend only on N.
-/

public section
open MeasureTheory Set
open scoped Classical ContDiff
namespace WaveTurbulence.Sumint

/-- A compact scalar exponential agreeing with exp(sigma*t) throughout the source output range. -/
@[expose] noncomputable def timeInverseExpScalar (N : ℕ) (σ t : ℝ) : ℂ :=
  (Fourier.chi0 (t/(2*((N:ℝ)+1))):ℂ)*(Real.exp (σ*t):ℂ)

/-- The actual scalar inverse-exponential profile is ordinarily smooth. -/
theorem contDiff_timeInverseExpScalar (N : ℕ) (σ : ℝ) : ContDiff ℝ ∞ (timeInverseExpScalar N σ) := by
  unfold timeInverseExpScalar
  apply ContDiff.mul
  · exact Complex.ofRealCLM.contDiff.comp (Fourier.chi0_contDiff.comp (by fun_prop))
  · have he : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (σ*t)) :=
      Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
    exact Complex.ofRealCLM.contDiff.comp he

/-- The actual scalar inverse-exponential profile has compact support. -/
theorem hasCompactSupport_timeInverseExpScalar (N : ℕ) (σ : ℝ) : HasCompactSupport (timeInverseExpScalar N σ) := by
  let R : ℝ := 2*((N:ℝ)+1)
  have hR : 0 < R := by dsimp [R]; positivity
  apply HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R))
  intro t ht
  have hab : R ≤ |t| := by
    by_contra! hn
    exact ht ⟨(abs_lt.mp hn).1.le,(abs_lt.mp hn).2.le⟩
  have hlarge : 1 ≤ |t/R| := by
    rw [abs_div,abs_of_pos hR]
    exact (le_div_iff₀ hR).mpr (by simpa only [one_mul] using hab)
  change (Fourier.chi0 (t/R):ℂ)*(Real.exp (σ*t):ℂ) = 0
  rw [Fourier.chi0_eq_zero hlarge,Complex.ofReal_zero,zero_mul]

/-- The compact scalar profile is the exact exponential on all actual source output coordinates. -/
theorem timeInverseExpScalar_eq_exp (N : ℕ) (σ : ℝ) {t : ℝ} (ht : |t| ≤ N) :
    timeInverseExpScalar N σ t = (Real.exp (σ*t):ℂ) := by
  have hR : 0 < 2*((N:ℝ)+1) := by positivity
  have hab : |t/(2*((N:ℝ)+1))| ≤ 1/2 := by
    rw [abs_div,abs_of_pos hR]
    apply (div_le_iff₀ hR).mpr
    linarith only [ht]
  rw [timeInverseExpScalar,Fourier.chi0_eq_one hab,Complex.ofReal_one,one_mul]

/-- The fixed compact inverse-exponential multiplier in the three original shear coordinates. -/
@[expose] noncomputable def inverseExponentialCutoff (N : ℕ) (z : Fin 3 → ℝ) : ℂ :=
  ∏ j, timeInverseExpScalar N (if j = 0 then 1 else -1) (z j)

/-- The fixed inverse-exponential multiplier is ordinarily smooth. -/
theorem contDiff_inverseExponentialCutoff (N : ℕ) : ContDiff ℝ ∞ (inverseExponentialCutoff N) := by
  apply contDiff_prod
  intro j _
  exact (contDiff_timeInverseExpScalar N _).comp (by fun_prop)

/-- The fixed inverse-exponential multiplier is compactly supported in all three time coordinates. -/
theorem hasCompactSupport_inverseExponentialCutoff (N : ℕ) : HasCompactSupport (inverseExponentialCutoff N) := by
  apply HasCompactSupport.intro (isCompact_univ_pi (fun j : Fin 3 =>
    hasCompactSupport_timeInverseExpScalar N (if j = 0 then 1 else -1)))
  intro z hz
  have hj : ∃ j : Fin 3, z j ∉ tsupport (timeInverseExpScalar N (if j = 0 then 1 else -1)) := by
    simpa only [Set.mem_pi,Set.mem_univ,forall_const,not_forall] using hz
  obtain ⟨j,hj⟩ := hj
  exact Finset.prod_eq_zero (Finset.mem_univ j) (image_eq_zero_of_notMem_tsupport hj)

/-- The fixed multiplier restores exactly the source inverse exponential on its whole sheared output range. -/
theorem inverseExponentialCutoff_eq_exp (N : ℕ) (z : Fin 3 → ℝ) (hz : ∀ j, |z j| ≤ N) :
    inverseExponentialCutoff N z = (Real.exp (z 0-z 1-z 2):ℂ) := by
  unfold inverseExponentialCutoff
  simp_rw [timeInverseExpScalar_eq_exp N _ (hz _)]
  rw [Fin.prod_univ_three]
  norm_num only [Fin.isValue,ite_true,show (1:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 0 by decide,ite_false,
    one_mul,neg_one_mul]
  rw [← Complex.ofReal_mul,← Complex.ofReal_mul,← Real.exp_add,← Real.exp_add]
  congr 2

end WaveTurbulence.Sumint
