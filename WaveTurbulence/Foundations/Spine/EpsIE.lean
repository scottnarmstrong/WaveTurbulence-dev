/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ChartAff
public import WaveTurbulence.Foundations.Spine.GardenPos
/-! # Inclusion-exclusion for epsilon, and slot-difference forms (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine Finset

variable {n d : ℕ}

/-- `ε_{n₁n₂n₃} = 1 - 1[n₂ = n₁] - 1[n₂ = n₃]`. -/
theorem epsCoef_eq_sub (n₁ n₂ n₃ : Fin d → ℤ) :
    epsCoef n₁ n₂ n₃ = 1 - (if n₂ = n₁ then 1 else 0) - (if n₂ = n₃ then 1 else 0) := by
  unfold epsCoef
  split_ifs <;> simp_all <;> norm_num

/-- The sign of the slot `σ j` is `+1` for `j < 2` and `-1` otherwise. -/
lemma sg_sigma (S : ChainSigns n) (i : Fin n) (j : Fin 4) :
    S.sg i (S.σ i j) = if j.1 < 2 then 1 else -1 := by
  obtain ⟨h0, h1⟩ := S.plus i
  obtain ⟨h2, h3⟩ := S.minus i
  fin_cases j <;> simp [h0, h1, h2, h3]

end WaveTurbulence.LadderDecay
