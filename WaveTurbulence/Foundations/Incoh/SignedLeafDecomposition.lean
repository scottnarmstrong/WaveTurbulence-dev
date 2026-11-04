/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LocalizedLeafDecomposition
public import WaveTurbulence.Foundations.Incoh.GardenSign

/-!
# The source global sign in the exact localized momentum identity

TARGET (incohproof2), (incohproof8), audit P-3. The global unit phase
multiplies the actual source input product on both sides of the finite
link localization identity; it is not discarded in the identity.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Exact signed localized source identity, uniform in the global garden phase. -/
theorem exists_signedLeafWeight_decomposition (d : ℕ) (hd : 0 < d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n m w : ℕ, ∀ P : MomentumTreeData n m w,
      ∀ k : Mom d, ∀ c : Fin m → Fin d → ℤ,
      ∃ S : Finset ((Fin n × Fin 2) → Fin d → ℤ), (S.card : ℝ) ≤ C₀ ^ n ∧
        ∀ ζ : Circle, ∀ f : Fin m → Mom d → ℂ, ∀ x : Fin n → Fin 2 → Mom d,
          (ζ : ℂ) * P.localizedLeafWeight f c k x =
            ∑ z ∈ S, (ζ : ℂ) * P.localizedLeafWeight f c k x *
              halfCellArrayWeight z (fun p => x p.1 p.2) := by
  classical
  obtain ⟨C₀, hC₀, h⟩ := exists_localizedLeafWeight_decomposition d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro n m w P k c
  obtain ⟨S, hcard, hS⟩ := h n m w P k c
  refine ⟨S, hcard, ?_⟩
  intro ζ f x
  calc
    _ = (ζ : ℂ) * ∑ z ∈ S, P.localizedLeafWeight f c k x *
        halfCellArrayWeight z (fun p => x p.1 p.2) := congrArg ((ζ : ℂ) * ·) (hS f x)
    _ = _ := by rw [Finset.mul_sum]; simp only [mul_assoc]

end WaveTurbulence.Incoh
