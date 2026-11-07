/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3CompBeta
/-! **FINALCOUNT-G3**: `CompBeta` along Steps 3 and 4 (cuts). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*} {d : ℕ}

theorem Step3.compBeta {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {s s' : St.{u} V D₀}
    (h : Step3 L γ η w κ s s') (hg : Good R s) (hC : CompBeta s) : CompBeta s' := by
  cases h with
  | cut v v₂ x₁ x₂ hcd R' kp hR hkp hε hsg hsim h3 =>
    by_cases hα : s.M.IsAlphaCut v v₂ x₁ x₂
    · have hab : (Cls.alpha R' kp).IsAB := trivial
      have := hC.cutα hcd (Cls.alpha R' kp) hab hε ((isAlphaCut_iff s.M hcd).1 hα) h3
      simpa only [if_pos hα] using this
    · have := hC.cutβ hcd .beta (Or.inl rfl)
      simpa only [if_neg hα] using this

theorem Step4.compBeta {s s' : St.{u} V D₀} (h : Step4 s s') (hC : CompBeta s) : CompBeta s' := by
  cases h with
  | cut v v₂ x₁ x₂ hcd hε hβ h3 => exact hC.cutβ hcd .beta (Or.inl rfl)

end WaveTurbulence.FinalCountG3
