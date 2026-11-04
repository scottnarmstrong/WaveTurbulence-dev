/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MomentumTreeRootInput
public import WaveTurbulence.Foundations.Incoh.RawTreeAgreement

/-! # Exact source effect of adding the temporary lone-leaf root input -/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- Append one actual input function at the root. -/
@[expose] def appendRootInput {d m : ℕ} (f : Fin m → Mom d → ℂ) (h : Mom d → ℂ) :
    Fin (m + 1) → Mom d → ℂ := Fin.lastCases h f

/-- Appending the root input multiplies the actual source leaf weight by its root value. -/
theorem MomentumTreeData.sourceLeafWeight_withRootInput {d n m w : ℕ} (P : MomentumTreeData n m w)
    (f : Fin m → Mom d → ℂ) (h : Mom d → ℂ) (k : Mom d) (x : Fin n → Fin 2 → Mom d) :
    P.withRootInput.sourceLeafWeight (appendRootInput f h) k x = P.sourceLeafWeight f k x * h k := by
  rw [MomentumTreeData.sourceLeafWeight, Fin.prod_univ_castSucc]
  simp only [appendRootInput, P.withRootInput_inputMomentum_castSucc,
    P.withRootInput_inputMomentum_last, Fin.lastCases_castSucc, Fin.lastCases_last]
  rfl

/-- The literal normalized raw lattice integrand retains this exact factor. -/
theorem MomentumTreeData.sourceTimeIntegrand_withRootInput {d n m w : ℕ} (P : MomentumTreeData n m w)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (f : Fin m → Mom d → ℂ) (h : Mom d → ℂ) (k : Mom d) (t : Fin n → Fin 2 → ℝ) :
    P.withRootInput.sourceTimeIntegrand ζ L γ δ Q (appendRootInput f h) k t =
      P.sourceTimeIntegrand ζ L γ δ Q f k t * h k := by
  unfold MomentumTreeData.sourceTimeIntegrand
  rw [← tsum_mul_right]
  apply tsum_congr
  intro p
  rw [P.sourceLeafWeight_withRootInput]
  ring

/-- The actual source integral is multiplied by the appended root value. -/
theorem MomentumTreeData.sourceIntegral_withRootInput {d n m w : ℕ} (P : MomentumTreeData n m w)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (h : Mom d → ℂ) (k : Mom d) :
    P.withRootInput.sourceIntegral ζ L γ δ Q I (appendRootInput f h) k =
      P.sourceIntegral ζ L γ δ Q I f k * h k := by
  simp only [MomentumTreeData.sourceIntegral, P.sourceTimeIntegrand_withRootInput]
  rw [integral_mul_const]
  ring

/-- The actual causal tree source kernel has exactly the same root factor. -/
theorem MomentumTreeData.sourceTreeKernel_withRootInput {d n m w : ℕ} (P : MomentumTreeData n m w)
    (ζ : Circle) (R : RootCoordinates n) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (h : Mom d → ℂ)
    (t : Fin 2 → ℝ) (k : Mom d) :
    P.withRootInput.sourceTreeKernel ζ R L γ δ Q I (appendRootInput f h) t k =
      P.sourceTreeKernel ζ R L γ δ Q I f t k * h k :=
  P.sourceIntegral_withRootInput ζ L γ δ Q (I ∩ R.causalRootCut t) f h k

end WaveTurbulence.Incoh
