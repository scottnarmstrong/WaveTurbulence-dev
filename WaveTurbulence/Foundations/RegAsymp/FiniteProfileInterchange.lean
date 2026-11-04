/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.PhiProfile
import WaveTurbulence.Foundations.ClassJR.MCCase1

/-! # Temporal Fourier interchange for a genuinely finite localized lattice sum -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR ApproxNT WithLp

/-- A fixed energy profile of a regular source coefficient is integrable
in its time frequencies. No spatial compactness or moment premise enters. -/
theorem integrable_resProfile_e2 {n : ℕ} (J : Finset (Fin n))
    {C : ({j // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C)
    (Ω : Fin n → ℝ) (t s : ℝ) :
    Integrable (fun lam => resProfile J (fun α => C (ofLp α) lam) Ω*e2 lam t s) := by
  have hi := (hC.integrable (fun j => Ω j.val)).const_mul
    (∏ j ∈ J, ((Fourier.chiInfinity (Ω j)/(Ω j) : ℝ):ℂ))
  apply hi.mul_bdd (c := 1)
  · exact (show Continuous (fun lam : ℝ × ℝ => e2 lam t s) by unfold e2; fun_prop).aestronglyMeasurable
  · exact ae_of_all _ (fun lam => (norm_e2 lam t s).le)

/-- The actual finite support of a localized amplitude justifies moving
its lattice sum through the temporal Fourier integral. -/
theorem tsum_integral_resProfile_e2 {ι : Type} [DecidableEq ι] {n : ℕ}
    (S : Finset ι) (W : ι → ℂ) (hW : ∀ i ∉ S, W i = 0)
    (J : Finset (Fin n)) {C : ({j // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : SymReg C) (Ω : ι → Fin n → ℝ) (t s : ℝ) :
    (∑' i, W i*(∫ lam, resProfile J (fun α => C (ofLp α) lam) (Ω i)*e2 lam t s)) =
      ∫ lam, (∑' i, W i*resProfile J (fun α => C (ofLp α) lam) (Ω i))*e2 lam t s := by
  have hout : (∑' i, W i*(∫ lam, resProfile J (fun α => C (ofLp α) lam) (Ω i)*e2 lam t s)) =
      ∑ i ∈ S, W i*(∫ lam, resProfile J (fun α => C (ofLp α) lam) (Ω i)*e2 lam t s) :=
    tsum_eq_sum (fun i hi => by rw [hW i hi,zero_mul])
  have hin (lam : ℝ × ℝ) : (∑' i, W i*resProfile J (fun α => C (ofLp α) lam) (Ω i)) =
      ∑ i ∈ S, W i*resProfile J (fun α => C (ofLp α) lam) (Ω i) :=
    tsum_eq_sum (fun i hi => by rw [hW i hi,zero_mul])
  rw [hout]
  simp_rw [hin,Finset.sum_mul]
  rw [integral_finsetSum S (fun i _ => by
    simpa only [mul_assoc] using (integrable_resProfile_e2 J hC (Ω i) t s).const_mul (W i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun _ => (mul_assoc _ _ _).symm)

end WaveTurbulence.RegAsymp
