/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LayerLink
public import WaveTurbulence.Foundations.WeylSums.FiniteTensorSeries

/-!
# Exact factorization of the actual finite link lattice sum

TARGET (incohproof9–10). The free coordinate array is reindexed as pairs
per link, and the literal compactly supported lattice terms factor.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Actual regrouping of the two free lattice momenta of each link. -/
@[expose] def linkLatticeArrayEquiv (I V : Type*) :
    ((I × Fin 2) → V) ≃ (I → V × V) where
  toFun p i := (p (i, 0), p (i, 1))
  invFun p ij := if ij.2 = 0 then (p ij.1).1 else (p ij.1).2
  left_inv p := by
    funext ⟨i, j⟩
    fin_cases j <;> simp
  right_inv p := by funext i; simp

/-- The actual compact lattice summand before summing over all links. -/
@[expose] def linkArraySummand {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (t : Fin n → Fin 2 → ℝ) (p : (Fin n × Fin 2) → Fin d → ℤ) : ℂ :=
  ∏ i, linkAmplitude L (Q i).toLinkParameters (p (i, 0), p (i, 1)) *
    WeylSums.e (linkPhase L ((((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) *
      (t i 0 - t i 1)) (Q i).toLinkParameters (p (i, 0), p (i, 1)))

/-- The source's full link lattice sum is exactly the product of the analytic link factors. -/
theorem tsum_linkArraySummand {d n : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (t : Fin n → Fin 2 → ℝ) :
    (∑' p : (Fin n × Fin 2) → Fin d → ℤ, linkArraySummand L γ δ Q t p) =
      ∏ i, linkTimeFactor L γ δ (Q i) (t i) := by
  let f := fun i : Fin n => fun p : (Fin d → ℤ) × (Fin d → ℤ) =>
    linkAmplitude L (Q i).toLinkParameters p *
      WeylSums.e (linkPhase L ((((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) *
        (t i 0 - t i 1)) (Q i).toLinkParameters p)
  have hf (i : Fin n) : (Function.support (f i)).Finite :=
    (finite_support_linkAmplitude hL (Q i).toLinkParameters).subset
      (fun p hp hz => hp (by simp only [f, hz, zero_mul]))
  calc
    _ = ∑' p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)), ∏ i, f i (p i) :=
      (linkLatticeArrayEquiv (Fin n) (Fin d → ℤ)).tsum_eq (fun p => ∏ i, f i (p i))
    _ = ∏ i, ∑' p, f i p := WeylSums.tsum_pi_prod_of_finite_support f hf
    _ = _ := rfl

end WaveTurbulence.Incoh
