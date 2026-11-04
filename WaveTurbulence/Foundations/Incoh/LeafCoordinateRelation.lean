/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.IntegerLeafCoordinates
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# The literal root-recovery relation in integer leaf coordinates

TARGET (incohproof1)–(3). These are consequences of the two structural
integer inverse identities supplied by C2, with no analytic hypotheses.
-/

public section
noncomputable section
open Matrix

namespace WaveTurbulence.Incoh

/-- The backward root row recovers the root from the actual leaf values. -/
theorem IntegerLeafCoordinates.recover_root {n : ℕ} (P : IntegerLeafCoordinates n)
    (u : Fin (2 * n + 1) → ℤ) : ∑ i, P.sigma i * (P.forward *ᵥ u) i = u 0 := by
  change (P.backward *ᵥ (P.forward *ᵥ u)) 0 = u 0
  rw [Matrix.mulVec_mulVec, P.backward_mul_forward, Matrix.one_mulVec]

/-- The actual translated leaf values satisfy the single source relation. -/
theorem IntegerLeafCoordinates.shifted_leaf_relation {n : ℕ} (P : IntegerLeafCoordinates n)
    (u : Fin (2 * n + 1) → ℤ) :
    ∑ i, P.sigma i * ((P.forward *ᵥ u) i - u 0) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, P.recover_root, ← Finset.sum_mul, P.sum_sigma, one_mul, sub_self]

/-- Every leaf is the root plus an actual integer combination of the `2n` link coordinates. -/
theorem IntegerLeafCoordinates.leaf_eq_root_add {n : ℕ} (P : IntegerLeafCoordinates n)
    (u : Fin (2 * n + 1) → ℤ) (i : Fin (2 * n + 1)) :
    (P.forward *ᵥ u) i = u 0 + ∑ j : Fin (2 * n), P.forward i j.succ * u j.succ := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, P.root_column, one_mul]

/-- The structural matrices give an exact bijection on all lattice coordinates. -/
@[expose] def IntegerLeafCoordinates.latticeEquiv {n : ℕ} (P : IntegerLeafCoordinates n) :
    (Fin (2 * n + 1) → ℤ) ≃ (Fin (2 * n + 1) → ℤ) where
  toFun u := P.forward *ᵥ u
  invFun v := P.backward *ᵥ v
  left_inv u := by
    change P.backward *ᵥ (P.forward *ᵥ u) = u
    rw [Matrix.mulVec_mulVec, P.backward_mul_forward, Matrix.one_mulVec]
  right_inv v := by
    change P.forward *ᵥ (P.backward *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, P.forward_mul_backward, Matrix.one_mulVec]

/-- Apply the exact integer lattice bijection independently in every spatial coordinate. -/
@[expose] def IntegerLeafCoordinates.vectorLatticeEquiv {n : ℕ} (P : IntegerLeafCoordinates n) (d : ℕ) :
    (Fin (2 * n + 1) → Fin d → ℤ) ≃ (Fin (2 * n + 1) → Fin d → ℤ) where
  toFun u i a := P.latticeEquiv (fun j => u j a) i
  invFun v i a := P.latticeEquiv.symm (fun j => v j a) i
  left_inv u := by
    funext i a
    exact congrFun (P.latticeEquiv.left_inv (fun j => u j a)) i
  right_inv v := by
    funext i a
    exact congrFun (P.latticeEquiv.right_inv (fun j => v j a)) i

/-- Reindexing the full decoration lattice introduces no multiplicity or Jacobian. -/
theorem IntegerLeafCoordinates.tsum_vectorLatticeEquiv {n d : ℕ} (P : IntegerLeafCoordinates n)
    (F : (Fin (2 * n + 1) → Fin d → ℤ) → ℂ) :
    (∑' u, F (P.vectorLatticeEquiv d u)) = ∑' v, F v :=
  (P.vectorLatticeEquiv d).tsum_eq F

end WaveTurbulence.Incoh
