/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ProductPowerEnvelopes

/-!
# Products of ordinary pair envelopes

The discrepancy function is a literal finite count. This generic algebraic
helper applies to an entire pair family or to the family remaining after
removing the distinguished first pair of a bad block.
-/

@[expose] public section
set_option autoImplicit false

open ENNReal

namespace WaveTurbulence.SumintPar

/-- A finite pair family retains the sum of its local discrepancy indicators. -/
theorem prod_pair_power_bounds {ι : Type*} [Fintype ι]
    (P : ι → ℝ≥0∞) (χ : ι → ℕ) {C δ L b θ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hL : 0 < L)
    (hP : ∀ i, P i ≤ ENNReal.ofReal (C*δ⁻¹*L^(2*b-θ*(χ i:ℝ)))) :
    (∏ i, P i) ≤ ENNReal.ofReal (C^(Fintype.card ι)*δ^(-(Fintype.card ι:ℝ))*
      L^(2*(Fintype.card ι:ℝ)*b-θ*((∑ i, χ i):ℝ))) := by
  have hb := prod_local_power_envelopes_le P (fun _ => C) (fun _ => (1:ℝ))
    (fun i => 2*b-θ*(χ i:ℝ)) hδ hL (fun _ => hC)
    (by intro i; simpa only [Real.rpow_neg_one] using hP i)
  apply hb.trans_eq
  simp only [Finset.prod_const,Finset.card_univ,Finset.sum_const,nsmul_eq_mul,mul_one]
  congr 2
  rw [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum,← Nat.cast_sum]
  simp only [Finset.card_univ]
  congr 1; ring

end WaveTurbulence.SumintPar
