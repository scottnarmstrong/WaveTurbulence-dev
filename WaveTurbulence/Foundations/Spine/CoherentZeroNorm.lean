/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RegularCodeReindex
public import WaveTurbulence.Foundations.XChain.LeafPairKernel
public import WaveTurbulence.Foundations.Spine.RemainderInputs
/-! Exact high-order spatial bound for the coherent zero-order remainder. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open scoped ENNReal

theorem four_Lambda_next_le (P : WTParams) (hd : 1 ≤ P.d) {p : ℕ} (hp : p < P.D) :
    4 * P.Lambda (p + 1) ≤ P.Lambda p := by
  have he : P.D + 1 - p = (P.D + 1 - (p + 1)) + 1 := by omega
  unfold WTParams.Lambda
  rw [he, pow_succ]
  exact (Nat.mul_le_mul_right _ (by omega : 4 ≤ 40 * P.d)).trans_eq (Nat.mul_comm _ _)

end WaveTurbulence.LGSpine
