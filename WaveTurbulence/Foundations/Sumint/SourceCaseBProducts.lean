/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.BlockMassProducts

/-!
# The literal external case-(b) factor distributed over source blocks

The norm power in the source expression is exactly the product of one
momentum norm for each non-normal case-(b) block. This is an algebraic
identity, including zero momentum; no reciprocal norm is introduced.
-/

public section

open ENNReal
open scoped Classical

namespace WaveTurbulence.Sumint

/-- The actual external multiplier carried by a single source block. -/
@[expose] noncomputable def caseBMultiplier {d : ℕ} (D : SumintDatum d) (r : Mom d)
    (i : Fin D.S.I) : ℝ≥0∞ :=
  if D.S.nor i = false ∧ D.badKind i = 1 then ENNReal.ofReal ‖r‖ else 1

/-- The source norm power is exactly the product of its case-(b) block multipliers. -/
theorem prod_caseBMultiplier {d : ℕ} (D : SumintDatum d) (r : Mom d) :
    (∏ i, caseBMultiplier D r i) =
      ENNReal.ofReal (‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card) := by
  unfold caseBMultiplier
  rw [← Finset.prod_filter,Finset.prod_const,ENNReal.ofReal_pow (norm_nonneg r)]

/-- Distribute the literal external norm power into the original block product. -/
theorem case_b_norm_mul_block_product {d : ℕ} (D : SumintDatum d) (r : Mom d)
    (F : Fin D.S.I → ℝ≥0∞) (P : (Σ i : Fin D.S.I, Fin (D.S.m i)) → ℝ≥0∞)
    (N : {i : Fin D.S.I // D.S.nor i = true} → ℝ≥0∞) :
    ENNReal.ofReal (‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card)*
      (∏ i : Fin D.S.I, (F i*(∏ j : Fin (D.S.m i), P ⟨i,j⟩)*normalMassInBlock D.S N i)) =
      ∏ i : Fin D.S.I, ((caseBMultiplier D r i*F i)*(∏ j : Fin (D.S.m i), P ⟨i,j⟩)*normalMassInBlock D.S N i) := by
  rw [← prod_caseBMultiplier,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ac_rfl

end WaveTurbulence.Sumint
