/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzInterface
/-! G8, SEAL-PLAN B.4: deterministic a-mass bound on the actual ansatz event. -/
public section
namespace WaveTurbulence.MainGlue
open MeasureTheory Set
variable {P : WTParams} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {g : (Fin P.d → ℤ) → Ω → ℂ} {a : Ω → ℝ → (Fin P.d → ℤ) → ℂ}
  {Fev : ℕ → Set Ω} {R : ℕ → Mom P.d → ℝ} {E : ℕ → (Fin P.d → ℤ) → ℝ}
  {Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ}

/-- G8, TARGET proofmain: on Fev p each squared a-coordinate is bounded by the initial mass.
No Gaussian, independence or rapid-decay premise is needed; the solution class supplies summability. -/
theorem ansatz_norm_sq_le_initial_mass {p : ℕ}
    (hA : AnsatzAt P μ g a Fev R E Et p) (hL : 0 < P.L)
    (hφ : ∀ k, 0 ≤ P.φin k) {ω : Ω} (hω : ω ∈ Fev p)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) p) (n : Fin P.d → ℤ) :
    ‖a ω t n‖ ^ 2 ≤ ∑' m, P.φin (latticePoint P.L m) * ‖g m ω‖ ^ 2 := by
  have ha := ansatz_isAkSolution hA hω
  have hs := ha.summable_norm hL ht
  have hs2 : Summable (fun m => ‖a ω t m‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun m => ?_) (hs.mul_right (∑' m, ‖a ω t m‖))
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (hs.le_tsum m (fun _ _ => norm_nonneg _)) (norm_nonneg _)
  calc
    _ ≤ ∑' m, ‖a ω t m‖ ^ 2 := hs2.le_tsum n (fun _ _ => sq_nonneg _)
    _ = ∑' m, ‖initialCoeff P.L P.φin g ω m‖ ^ 2 := ha.tsum_normSq_eq hL ht
    _ = _ := by
      apply tsum_congr
      intro m
      rw [initialCoeff, norm_mul, mul_pow, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hφ _)]

end WaveTurbulence.MainGlue
