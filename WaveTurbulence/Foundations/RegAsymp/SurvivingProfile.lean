/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.SurvivingEnergyCoordinates
public import WaveTurbulence.Foundations.ApproxNT.Statement

/-! # Exact resonant profiles after deletion of zero-energy links -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset ClassJR ApproxNT WithLp

/-- The coefficient trace agrees with the literal original coefficient
when all removed energies vanish. -/
theorem survivingTraceCoefficient_eq_of_zero {n : ℕ} (T J : Finset (Fin n))
    (h : Disjoint T J) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (Ω : Fin n → ℝ) (hΩ : ∀ j ∈ T, Ω j = 0) (lam : ℝ × ℝ) :
    survivingTraceCoefficient T J h C
      (fun i => Ω ((survivingEnergyEquiv T).symm i.val).val) lam =
      C (fun j => Ω j.val) lam := by
  rw [survivingTraceCoefficient]
  have he : (fun j : {j : Fin n // j ∉ T ∧ j ∉ J} =>
      Ω ((survivingEnergyEquiv T).symm ((survivingActiveEquiv T J).symm j).val).val) =
      fun j => Ω j.val := by
    funext j
    simp [survivingActiveEquiv]
  rw [he]
  exact energyTraceCoefficient_eq_of_zero T J h C Ω hΩ lam

/-- Special scalar factors reindex exactly, because none was removed. -/
theorem prod_survivingSpecial {n : ℕ} (T J : Finset (Fin n)) (h : Disjoint T J)
    (f : Fin n → ℂ) :
    (∏ i ∈ survivingSpecial T J, f ((survivingEnergyEquiv T).symm i).val) = ∏ j ∈ J, f j := by
  classical
  apply prod_bij (fun i _ => ((survivingEnergyEquiv T).symm i).val)
  · intro i hi
    exact (mem_filter.mp hi).2
  · intro i hi j hj hij
    exact (survivingEnergyEquiv T).symm.injective (Subtype.ext hij)
  · intro j hj
    have ht : j ∉ T := fun hT => disjoint_left.mp h hT hj
    refine ⟨survivingEnergyEquiv T ⟨j,ht⟩,?_,?_⟩
    · simp [survivingSpecial,hj]
    · simp
  · intro i _
    rfl

/-- The full resonant source profile is the lower-dimensional NT profile
of the actual simultaneous trace, including every chi-infinity factor. -/
theorem resProfile_survivingTraceCoefficient {n : ℕ} (T J : Finset (Fin n))
    (h : Disjoint T J) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (Ω : Fin n → ℝ) (hΩ : ∀ j ∈ T, Ω j = 0) (lam : ℝ × ℝ) :
    resProfile (survivingSpecial T J)
      (fun β => survivingTraceCoefficient T J h C (ofLp β) lam)
      (fun i => Ω ((survivingEnergyEquiv T).symm i).val) =
      resProfile J (fun β => C (ofLp β) lam) Ω := by
  unfold resProfile
  rw [prod_survivingSpecial T J h (fun j => ((Fourier.chiInfinity (Ω j)/Ω j : ℝ):ℂ))]
  congr 1
  exact survivingTraceCoefficient_eq_of_zero T J h C Ω hΩ lam

end WaveTurbulence.RegAsymp
