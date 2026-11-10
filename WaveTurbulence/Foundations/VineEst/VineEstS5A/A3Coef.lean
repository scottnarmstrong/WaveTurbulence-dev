/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Scalar
public import WaveTurbulence.Foundations.VineEst.VineEstS3.SNormAux
public import WaveTurbulence.Foundations.XChain.SNormOperations

/-! # Coefficient families of arity-3 rows: separated terms and finite sums (V5 Step 4d-A, item 2)

`coefBound θ A B c = ∑_m ⟨m/2⟩^θ sup_r ‖c m r‖_{S^{A,B}}` is the size of a mode family (the `fs_bound` field of
`ClockedModes3`).  A separated family `c m r k = ĥ_m M(r,k)` costs `(∑_m ⟨m/2⟩^θ |ĥ_m|) · sup_r ‖M(r)‖_S`, and a
finite sum of families costs at most the sum of the costs.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5A
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS3.Eng MeasureTheory Finset
open scoped ENNReal

variable {d : ℕ}

/-- The size of a family of mode coefficients (functions of `r` and of the momentum). -/
noncomputable def coefBound (θ : ℝ) (A B : ℕ) (c : (Fin 3 → ℤ) → Mom d → Mom d → ℂ) : ℝ≥0∞ :=
  ∑' m : Fin 3 → ℤ, maxBracketPow θ (half m) * ⨆ r : Mom d, SNorm A B (c m r)

/-- A separated family: time coefficients `ĥ` times a spatial function of `(r, k)`. -/
def sepCoef (h : (Fin 3 → ℤ) → ℂ) (M : Mom d → Mom d → ℂ) : (Fin 3 → ℤ) → Mom d → Mom d → ℂ :=
  fun m r k => h m * M r k

theorem coefBound_sep_le (θ : ℝ) (A B : ℕ) (h : (Fin 3 → ℤ) → ℂ) (M : Mom d → Mom d → ℂ) :
    coefBound θ A B (sepCoef h M) ≤
      (∑' m : Fin 3 → ℤ, maxBracketPow θ (half m) * ‖h m‖ₑ) * ⨆ r : Mom d, SNorm A B (M r) := by
  unfold coefBound
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun m => ?_
  rw [mul_assoc]
  refine mul_le_mul_right ?_ _
  calc ⨆ r : Mom d, SNorm A B (sepCoef h M m r)
      ≤ ⨆ r : Mom d, ‖h m‖ₑ * SNorm A B (M r) :=
        iSup_mono fun r => SNorm_smul_le A B (h m) (M r)
    _ = ‖h m‖ₑ * ⨆ r : Mom d, SNorm A B (M r) := ENNReal.mul_iSup _ _ |>.symm

end WaveTurbulence.VineEstS5A
