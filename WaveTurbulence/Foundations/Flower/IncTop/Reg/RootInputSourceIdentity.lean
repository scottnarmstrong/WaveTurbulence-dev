/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MomentumTreeRootInput
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawTreeAgreement

/-! Ported by source from C2-B-TOP `Cut2BReg.RootInputSourceIdentity` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Exact source effect of adding the temporary lone-leaf root input -/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
/-- Append one actual input function at the root. -/
@[expose] def appendRootInputSpatial {d m : ℕ} (f : Fin m → Mom d → ℂ) (h : Mom d → ℂ) :
    Fin (m + 1) → Mom d → ℂ := Fin.lastCases h f

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Appending the root input multiplies the actual source leaf weight by its root value. -/
theorem MomentumTreeData.sourceLeafWeight_withRootInputSpatial {d n m w : ℕ} (P : MomentumTreeData n m w)
    (f : Fin m → Mom d → ℂ) (h : Mom d → ℂ) (k : Mom d) (x : Fin n → Fin 2 → Mom d) :
    P.withRootInput.sourceLeafWeight (appendRootInputSpatial f h) k x = P.sourceLeafWeight f k x * h k := by
  rw [MomentumTreeData.sourceLeafWeight, Fin.prod_univ_castSucc]
  simp only [appendRootInputSpatial, P.withRootInput_inputMomentum_castSucc,
    P.withRootInput_inputMomentum_last, Fin.lastCases_castSucc, Fin.lastCases_last]
  rfl

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The literal normalized raw lattice integrand retains this exact factor. -/
theorem MomentumTreeData.sourceTimeIntegrand_withRootInputSpatial {d n m w : ℕ} (P : MomentumTreeData n m w)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (f : Fin m → Mom d → ℂ) (h : Mom d → ℂ) (k : Mom d) (t : Fin n → Fin 2 → ℝ) :
    (MomentumTreeData.sourceTimeIntegrandSpatial (P := P.withRootInput)) ζ L γ δ Q (appendRootInputSpatial f h) k t =
      (MomentumTreeData.sourceTimeIntegrandSpatial (P := P)) ζ L γ δ Q f k t * h k := by
  unfold MomentumTreeData.sourceTimeIntegrandSpatial
  rw [← tsum_mul_right]
  apply tsum_congr
  intro p
  rw [(MomentumTreeData.sourceLeafWeight_withRootInputSpatial (P := P))]
  ring

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual source integral is multiplied by the appended root value. -/
theorem MomentumTreeData.sourceIntegral_withRootInputSpatial {d n m w : ℕ} (P : MomentumTreeData n m w)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (h : Mom d → ℂ) (k : Mom d) :
    (MomentumTreeData.sourceIntegralSpatial (P := P.withRootInput)) ζ L γ δ Q I (appendRootInputSpatial f h) k =
      (MomentumTreeData.sourceIntegralSpatial (P := P)) ζ L γ δ Q I f k * h k := by
  simp only [MomentumTreeData.sourceIntegralSpatial, (MomentumTreeData.sourceTimeIntegrand_withRootInputSpatial (P := P))]
  rw [integral_mul_const]
  ring

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual causal tree source kernel has exactly the same root factor. -/
theorem MomentumTreeData.sourceTreeKernel_withRootInputSpatial {d n m w : ℕ} (P : MomentumTreeData n m w)
    (ζ : Circle) (R : RootCoordinates n) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (h : Mom d → ℂ)
    (t : Fin 2 → ℝ) (k : Mom d) :
    (MomentumTreeData.sourceTreeKernelSpatial (P := P.withRootInput)) ζ R L γ δ Q I (appendRootInputSpatial f h) t k =
      (MomentumTreeData.sourceTreeKernelSpatial (P := P)) ζ R L γ δ Q I f t k * h k :=
  (MomentumTreeData.sourceIntegral_withRootInputSpatial (P := P)) ζ L γ δ Q (I ∩ R.causalRootCut t) f h k

end WaveTurbulence.Flower.IncTop