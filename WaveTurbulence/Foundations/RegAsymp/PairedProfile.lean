/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.InverseProfile
public import WaveTurbulence.Foundations.ClassJR.MCSRep

/-! # The source two-time inverse profile in its original frequency measure

The source uses e^(πi(λ1*t+λ2*s)). Its ordinary Fourier frequency is λ/2.
A bilinear Fourier identity retains the original λ measure throughout;
no additional inverse-Fourier hypothesis or Jacobian convention is used.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory WaveTurbulence.Fourier ClassJR
open scoped ENNReal

/-- The actual Fourier frequency of the source π-normalized character. -/
def pairedTimeFrequency (lam : ℝ × ℝ) : Fin 2 → ℝ := ![lam.1/2,lam.2/2]

/-- Negative half-pairing, for the positive source inverse profile. -/
def pairedProfilePairing : (Fin 2 → ℝ) →ₗ[ℝ] (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun t :=
    { toFun := fun lam => -(t 0*lam.1/2+t 1*lam.2/2)
      map_add' := by intro a b; simp only [Prod.fst_add,Prod.snd_add]; ring
      map_smul' := by intro c a; simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,RingHom.id_apply]; ring }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro lam
    change -((a 0+b 0)*lam.1/2+(a 1+b 1)*lam.2/2) =
      -(a 0*lam.1/2+a 1*lam.2/2) + -(b 0*lam.1/2+b 1*lam.2/2)
    ring
  map_smul' := by
    intro c a
    apply LinearMap.ext
    intro lam
    change -((c*a 0)*lam.1/2+(c*a 1)*lam.2/2) = c * -(a 0*lam.1/2+a 1*lam.2/2)
    ring

/-- The half-pairing in scalar coordinates. -/
theorem timePairing_pairedTimeFrequency (t : Fin 2 → ℝ) (lam : ℝ × ℝ) :
    timePairing 2 t (pairedTimeFrequency lam) = (lam.1*t 0+lam.2*t 1)/2 := by
  change (∑ i, t i*(pairedTimeFrequency lam i)) = _
  simp only [Fin.sum_univ_two,pairedTimeFrequency,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

theorem pairedProfilePairing_apply (t : Fin 2 → ℝ) (lam : ℝ × ℝ) :
    pairedProfilePairing t lam = -timePairing 2 t (pairedTimeFrequency lam) := by
  change -(t 0*lam.1/2+t 1*lam.2/2) = _
  rw [timePairing_pairedTimeFrequency]
  ring

@[fun_prop] theorem continuous_pairedTimeFrequency : Continuous pairedTimeFrequency := by
  unfold pairedTimeFrequency
  fun_prop

/-- The source and the bilinear Fourier character agree exactly. -/
theorem e2_eq_pairedTimeFrequency (lam : ℝ × ℝ) (t : Fin 2 → ℝ) :
    e2 lam (t 0) (t 1) = (Real.fourierChar (timePairing 2 t (pairedTimeFrequency lam)) : ℂ) := by
  rw [e2,Real.fourierChar_apply]
  congr 1
  rw [timePairing_pairedTimeFrequency]
  push_cast
  ring

/-- A cutoff source inverse profile is convolution with its actual λ-density. -/
theorem timeFourier_mul_pairedProfile {f : (Fin 2 → ℝ) → ℂ} {A : (ℝ × ℝ) → ℂ}
    (hf : Integrable f) (hA : Integrable A) (ξ : Fin 2 → ℝ) :
    timeFourier (fun t => f t*(∫ lam, A lam*e2 lam (t 0) (t 1))) ξ =
      ∫ lam, timeFourier f (ξ-pairedTimeFrequency lam)*A lam := by
  let fξ := fun t => Real.fourierChar (-timePairing 2 t ξ) • f t
  have hp : Continuous (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => timePairing 2 p.1 p.2) := by
    change Continuous (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => ∑ i, p.1 i*p.2 i)
    fun_prop
  have hL : Continuous (fun p : (Fin 2 → ℝ) × (ℝ × ℝ) => pairedProfilePairing p.1 p.2) := by
    simp only [pairedProfilePairing]
    fun_prop
  have hfξ : Integrable fξ :=
    (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar hp ξ).mpr hf
  have hd := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (L := pairedProfilePairing) (μ := volume) (ν := volume)
    (ContinuousLinearMap.mul ℂ ℂ) Real.continuous_fourierChar hL hfξ hA
  have hl (lam : ℝ × ℝ) :
      VectorFourier.fourierIntegral Real.fourierChar volume pairedProfilePairing fξ lam =
        timeFourier f (ξ-pairedTimeFrequency lam) := by
    unfold VectorFourier.fourierIntegral timeFourier
    apply integral_congr_ae
    exact ae_of_all _ (fun t => by
      dsimp only [fξ]
      rw [pairedProfilePairing_apply,neg_neg,smul_smul,← AddChar.map_add_eq_mul]
      have he : timePairing 2 t (pairedTimeFrequency lam)+ -timePairing 2 t ξ =
          -timePairing 2 t (ξ-pairedTimeFrequency lam) := by rw [map_sub]; ring
      rw [he])
  have hr (t : Fin 2 → ℝ) :
      VectorFourier.fourierIntegral Real.fourierChar volume pairedProfilePairing.flip A t =
        ∫ lam, A lam*e2 lam (t 0) (t 1) := by
    unfold VectorFourier.fourierIntegral
    apply integral_congr_ae
    exact ae_of_all _ (fun lam => by
      simp only [LinearMap.flip_apply,pairedProfilePairing_apply,neg_neg,e2_eq_pairedTimeFrequency,
        Circle.smul_def,smul_eq_mul,mul_comm])
  simp_rw [hl,hr] at hd
  change (∫ lam, timeFourier f (ξ-pairedTimeFrequency lam)*A lam) =
    ∫ t, fξ t*(∫ lam, A lam*e2 lam (t 0) (t 1)) at hd
  rw [hd]
  change (∫ t, Real.fourierChar (-timePairing 2 t ξ) •
    (f t*(∫ lam, A lam*e2 lam (t 0) (t 1)))) = _
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by simp only [fξ,Circle.smul_def,smul_eq_mul,mul_assoc])

end WaveTurbulence.RegAsymp
