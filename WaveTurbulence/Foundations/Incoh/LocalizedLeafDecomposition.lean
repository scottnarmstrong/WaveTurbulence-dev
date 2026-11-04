/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.FiniteLinkCellLocalization
public import WaveTurbulence.Foundations.Incoh.SmoothLeafCells

/-!
# Exact finite smooth decomposition of localized source inputs

TARGET (incohproof4–8): the half-width link partition is finite on each
actual leaf localization, with a dimensional exponential cardinal bound.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- The literal localized product of the source input functions. -/
@[expose] def MomentumTreeData.localizedLeafWeight {d n m w : ℕ}
    (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (k : Mom d) (x : Fin n → Fin 2 → Mom d) : ℂ :=
  ∏ a, leafCell (f a) (c a) (P.inputMomentum k x a)

/-- The actual leaf localization factors out of the source input product. -/
theorem MomentumTreeData.localizedLeafWeight_eq {d n m w : ℕ}
    (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (k : Mom d) (x : Fin n → Fin 2 → Mom d) :
    P.localizedLeafWeight f c k x =
      (∏ a, f a (P.inputMomentum k x a)) * P.inputCellWeight c k x := by
  simp only [localizedLeafWeight, leafCell, inputCellWeight, leafCellProfile,
    Finset.prod_mul_distrib]

/-- Actual source products admit a finite smooth link decomposition, uniformly exponentially
in the number of links. This is an equality everywhere, including outside all input cells. -/
theorem exists_localizedLeafWeight_decomposition (d : ℕ) (hd : 0 < d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n m w : ℕ, ∀ P : MomentumTreeData n m w,
      ∀ k : Mom d, ∀ c : Fin m → Fin d → ℤ,
      ∃ S : Finset ((Fin n × Fin 2) → Fin d → ℤ), (S.card : ℝ) ≤ C₀ ^ n ∧
        ∀ f : Fin m → Mom d → ℂ, ∀ x : Fin n → Fin 2 → Mom d,
          P.localizedLeafWeight f c k x =
            ∑ z ∈ S, P.localizedLeafWeight f c k x *
              halfCellArrayWeight z (fun p => x p.1 p.2) := by
  classical
  obtain ⟨C₀, hC₀, h⟩ := exists_finite_link_cell_localization d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro n m w P k c
  obtain ⟨S, hcard, hS⟩ := h n m w P k c
  refine ⟨S, hcard, ?_⟩
  intro f x
  by_cases hx : P.inputCellWeight c k x = 0
  · simp only [P.localizedLeafWeight_eq, hx, mul_zero, zero_mul, Finset.sum_const_zero]
  · rw [← Finset.mul_sum, sum_halfCellArrayWeight_eq_one_of_cover P k c S hS x hx,
      mul_one]

end WaveTurbulence.Incoh
