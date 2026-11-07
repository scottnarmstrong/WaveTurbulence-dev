/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.PairProductPower
public import WaveTurbulence.Foundations.SumintPar.LocalPowerBudget

/-!
# Ordinary pair families in the common input-arity budget

Each pair carries two inputs and one reciprocal delta. The finite
family budget therefore has arity twice its cardinality. Its local
discrepancy count is retained exactly when paired with the core block.
-/

@[expose] public section
set_option autoImplicit false

open ENNReal

namespace WaveTurbulence.SumintPar

/-- A family of two-input pair budgets collects at twice its exact cardinality. -/
theorem prod_pair_arity_budget {ι : Type*} [Fintype ι]
    (P : ι → ℝ≥0∞) (χ : ι → ℕ) {C δ L b θ : ℝ}
    (hδ : 0 < δ) (hL : 0 < L)
    (hP : ∀ i, P i ≤ ENNReal.ofReal (C^2*δ⁻¹*L^(2*b-θ*(χ i:ℝ)))) :
    (∏ i, P i) ≤ ENNReal.ofReal (C^(2*Fintype.card ι)*δ^(-((2*Fintype.card ι:ℕ):ℝ)/2)*
      L^(((2*Fintype.card ι:ℕ):ℝ)*b-θ*((∑ i, χ i):ℝ))) := by
  have hb := prod_pair_power_bounds P χ (sq_nonneg C) hδ hL hP
  apply hb.trans_eq
  have hd : -((2*Fintype.card ι:ℕ):ℝ)/2 = -(Fintype.card ι:ℝ) := by push_cast; ring
  rw [← pow_mul,hd]
  congr 2
  push_cast
  ring

/-- A core block budget can be extended by any finite family of ordinary pairs. -/
theorem core_mul_pair_arity_budget {ι : Type*} [Fintype ι]
    (P : ι → ℝ≥0∞) (χ : ι → ℕ) {F : ℝ≥0∞} {C δ L b θ e : ℝ} (a : ℕ)
    (hC : 0 ≤ C) (hδ : 0 < δ) (hL : 0 < L)
    (hF : F ≤ ENNReal.ofReal (C^a*δ^(-(a:ℝ)/2)*L^e))
    (hP : ∀ i, P i ≤ ENNReal.ofReal (C^2*δ⁻¹*L^(2*b-θ*(χ i:ℝ)))) :
    F*(∏ i, P i) ≤ ENNReal.ofReal (C^(a+2*Fintype.card ι)*δ^(-((a+2*Fintype.card ι:ℕ):ℝ)/2)*
      L^(e+(((2*Fintype.card ι:ℕ):ℝ)*b-θ*((∑ i, χ i):ℝ)))) :=
  mul_local_power_envelopes a (2*Fintype.card ι) hC hδ hL hF (prod_pair_arity_budget P χ hδ hL hP)

end WaveTurbulence.SumintPar
