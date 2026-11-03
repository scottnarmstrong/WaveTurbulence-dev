/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicStarTargetThree
public import WaveTurbulence.Foundations.WeylSums.CubicStarTargetHigh

/-!
# TARGET lemcubic: both quadratic phases

This is the Foundations counterpart of the audited tier-B1 `quadExpSum3`
draft, with the same Boolean convention and the same quantifier order.
The chain phase is handled by cubic diagonalization and Young's inequality;
the shared-vertex phase by the zero/nonzero rational-arc product moments.
-/

public section
open MeasureTheory Set
namespace WaveTurbulence.WeylSums

theorem quadExpSum3_true_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ T₀ : ℝ, 0 < T₀ →
      ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ a b c ξ ζ ω : Mom d,
      (∫ ts : ℝ × ℝ in timeSquareWindow L (T₀*L^(2*γ)),
        ‖cubicLatticeSum L ts.1 ts.2 true a b c ξ ζ ω‖) ≤
        C*L^(3*(d : ℝ)+γ-2*min γ (1-γ))*Real.log L := by
  intro d hd γ hγ T₀ hT₀
  by_cases hd3 : d = 3
  · subst d
    exact quadExpSum3_true_bound_three γ hγ T₀ hT₀
  · exact quadExpSum3_true_bound_high d (by omega) γ hγ T₀ hT₀

/-- TARGET `lemcubic`, uniformly for both choices of the quadratic form and
all six real vector parameters. The cutoff and finite lattice carriers agree
with the audited draft through the identities in `MinorArcSums`. -/
theorem quadExpSum3_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ T₀ : ℝ, 0 < T₀ →
      ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ sel : Bool, ∀ a b c ξ ζ ω : Mom d,
      (∫ ts : ℝ × ℝ in timeSquareWindow L (T₀*L^(2*γ)),
        ‖cubicLatticeSum L ts.1 ts.2 sel a b c ξ ζ ω‖) ≤
        C*L^(3*(d : ℝ)+γ-2*min γ (1-γ))*Real.log L := by
  intro d hd γ hγ T₀ hT₀
  obtain ⟨C₀,R₀,h₀⟩ := quadExpSum3_false_bound d hd γ hγ T₀ hT₀
  obtain ⟨C₁,R₁,h₁⟩ := quadExpSum3_true_bound d hd γ hγ T₀ hT₀
  refine ⟨max C₀ C₁,max (max R₀ R₁) (Real.exp 1),?_⟩
  intro L hL sel a b c ξ ζ ω
  have hR₀ : R₀ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hR₁ : R₁ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLexp : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLexp
  have hlog : 0 ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) hLexp
    rw [Real.log_exp] at hh
    linarith
  have hmono (C : ℝ) (hC : C ≤ max C₀ C₁) :
      C*L^(3*(d : ℝ)+γ-2*min γ (1-γ))*Real.log L ≤
        max C₀ C₁*L^(3*(d : ℝ)+γ-2*min γ (1-γ))*Real.log L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hLp.le _)) hlog
  cases sel
  · exact (h₀ L hR₀ a b c ξ ζ ω).trans (hmono C₀ (le_max_left _ _))
  · exact (h₁ L hR₁ a b c ξ ζ ω).trans (hmono C₁ (le_max_right _ _))

end WaveTurbulence.WeylSums
