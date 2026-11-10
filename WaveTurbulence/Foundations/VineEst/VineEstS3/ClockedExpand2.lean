/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockedExpand

/-! # The interchange theorem for a clocked `sumint` expression (engine step EXP) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.FS Finset
  MeasureTheory
open scoped ENNReal

variable {d : ℕ} {D : SumintDatum d}

/-- Pointwise: the clocked integrand is the sum of its mode terms. -/
theorem clockedIntegrand_hasSum (cr : ClockedRows D) (c : Row D → (Fin 2 → ℤ) → Mom d → ℂ)
    (S : Row D → (Fin 2 → ℤ) → ℝ) (Dec : Row D → Mom d → ℝ)
    (hS : ∀ ρ, Summable (S ρ)) (hcS : ∀ ρ m k, ‖c ρ m k‖ ≤ S ρ m * Dec ρ k)
    (coreFirstSign coreSign : Fin D.S.I → ℤˣ) (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ))
    (E : Fin 4 → Mom d) (tt : Fin 3 → ℝ) (τ : D.S.TVar → ℝ)
    (hser : ∀ ρ k, HasSum (fun m => c ρ m k * fsPhase m (cr.clock τ tt ρ)) (cr.W ρ (cr.clock τ tt ρ) k)) :
    HasSum (fun m : Row D → Fin 2 → ℤ => modeTerm cr c coreFirstSign coreSign L γ δ η x E tt m τ)
      (clockedIntegrand cr coreFirstSign coreSign L γ δ η x E tt τ) := by
  set a : Row D → (Fin 2 → ℤ) → ℂ := fun ρ m => c ρ m (rowMom D L x E ρ) * fsPhase m (cr.clock τ tt ρ) with ha
  have hsa : ∀ ρ, Summable fun m => ‖a ρ m‖ := by
    intro ρ
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      ((hS ρ).mul_right (Dec ρ (rowMom D L x E ρ)))
    rw [ha]
    simp only [norm_mul, norm_fsPhase, mul_one]
    exact hcS _ _ _
  obtain ⟨-, hP⟩ := hasSum_pi_prod a hsa
  have hq : ∀ ρ, ∑' m, a ρ m = cr.W ρ (cr.clock τ tt ρ) (rowMom D L x E ρ) := fun ρ =>
    (hser ρ _).tsum_eq
  simp only [hq] at hP
  have := hP.mul_left (signedPhase D coreFirstSign coreSign L γ δ η x (E 0 - E 1) (tt 0) τ)
  unfold clockedIntegrand
  convert this using 1
  funext m
  unfold modeTerm
  rw [Finset.prod_mul_distrib]


theorem integrand_modeTerm (cr : ClockedRows D) (c : Row D → (Fin 2 → ℤ) → Mom d → ℂ)
    (coreFirstSign coreSign : Fin D.S.I → ℤˣ) (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ))
    (E : Fin 4 → Mom d) (tt : Fin 3 → ℝ) (m : Row D → Fin 2 → ℤ) (τ : D.S.TVar → ℝ) :
    modeTerm cr c coreFirstSign coreSign L γ δ η x E tt m τ =
      outFactor (modeFreq D cr.slot m) tt * ((∏ ρ, c ρ (m ρ) (rowMom D L x E ρ)) *
        (signedPhase D coreFirstSign coreSign L γ δ η x (E 0 - E 1) (tt 0) τ *
          paramFactor D (modeParam D cr.slot m) τ)) := by
  unfold modeTerm
  have := prod_fsPhase_clock D cr.slot m τ tt
  have h2 : ∏ ρ, fsPhase (m ρ) (cr.clock τ tt ρ) =
      paramFactor D (modeParam D cr.slot m) τ * outFactor (modeFreq D cr.slot m) tt := this
  rw [h2]
  ring

end WaveTurbulence.VineEstS3.Eng
