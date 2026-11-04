/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.AffineFacts
import Mathlib.Tactic

/-!
# Literal affine predecessor identities in sumint hypothesis (ii)

The matrix identities in the exact datum imply the corresponding vector
identities for every lattice input and output quadruple. Integer scalar
multiplication keeps the coefficient algebra independent of coordinates.
-/

public section

open Finset

namespace WaveTurbulence.Sumint

/-- An integer affine combination of the input and output vector families. -/
@[expose] noncomputable def integerAffineMap {ι κ : Type*} [Fintype ι] [Fintype κ]
    {d : ℕ} (T : Matrix ι ι ℤ) (H : ι → κ → ℤ) (X : ι → Mom d) (E : κ → Mom d) (v : ι) : Mom d :=
  ∑ j, T v j • X j + ∑ c, H v c • E c

/-- Summing scalar multiples of matrix rows commutes with applying them to vectors. -/
theorem sum_smul_rows {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}
    (σ : ι → ℤ) (T : ι → κ → ℤ) (X : κ → Mom d) :
    (∑ v, σ v • ∑ j, T v j • X j) = ∑ j, (∑ v, σ v * T v j) • X j := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/-- Signed combinations of affine rows are computed by signed combinations of their coefficients. -/
theorem sum_smul_integerAffineMap {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}
    (σ : ι → ℤ) (T : Matrix ι ι ℤ) (H : ι → κ → ℤ) (X : ι → Mom d) (E : κ → Mom d) :
    (∑ v, σ v • integerAffineMap T H X E v) =
      (∑ j, (∑ v, σ v * T v j) • X j) + ∑ c, (∑ v, σ v * H v c) • E c := by
  simp only [integerAffineMap, smul_add, Finset.sum_add_distrib]
  exact congrArg₂ (fun u v : Mom d => u + v)
    (sum_smul_rows σ (fun v j => T v j) X) (sum_smul_rows σ H E)

/-- Subtracting the predecessor subtracts its two coefficient rows, including the root case. -/
theorem integerAffineMap_sub_predecessor {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}
    (T : Matrix ι ι ℤ) (H : ι → κ → ℤ) (X : ι → Mom d) (E : κ → Mom d) (v : ι) (p : Option ι) :
    integerAffineMap T H X E v - p.elim 0 (integerAffineMap T H X E) =
      (∑ j, (T v j - p.elim 0 (fun w => T w j)) • X j) +
        ∑ c, (H v c - p.elim 0 (fun w => H w c)) • E c := by
  cases p with
  | none => simp only [Option.elim_none, sub_zero, integerAffineMap]
  | some w =>
    simp only [Option.elim_some, integerAffineMap, sub_smul, Finset.sum_sub_distrib]
    abel

/-- The exact draft's real-scalar k-map agrees with the integer affine action. -/
theorem kVec_eq_integerAffineMap {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) (v : D.S.VIdx) :
    D.kVec L x E v = integerAffineMap D.T₁ D.H₁ (fun w => latticePoint L (x w)) E v := by
  simp only [SumintDatum.kVec, integerAffineMap, Int.cast_smul_eq_zsmul]

/-- The same agreement for the draft's alternative ℓ-map. -/
theorem lVec_eq_integerAffineMap {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) (v : D.S.VIdx) :
    D.ℓVec L x E v = integerAffineMap D.T₂ D.H₂ (fun w => latticePoint L (x w)) E v := by
  simp only [SumintDatum.ℓVec, integerAffineMap, Int.cast_smul_eq_zsmul]

/-- Hypothesis (ii) gives its literal vector identity for all inputs, rather than an extra analytic hypothesis. -/
theorem alternative_predecessor_identity {d : ℕ} (D : SumintDatum d) {A L γ η : ℝ} {Dsteps : ℕ}
    (hD : D.Admissible A L γ η Dsteps) (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d)
    (v : D.S.VIdx) :
    D.ℓVec L x E v - (D.prev v).elim 0 (fun w => D.ℓVec L x E w) =
      (∑ w, (D.σk v w : ℝ) • D.kVec L x E w) + ∑ c, (D.σe v c : ℝ) • E c := by
  obtain ⟨_, _, _, _, hT, hH⟩ := hD.1 v
  simp_rw [kVec_eq_integerAffineMap, lVec_eq_integerAffineMap, Int.cast_smul_eq_zsmul]
  rw [integerAffineMap_sub_predecessor]
  simp_rw [hT, hH, add_smul, Finset.sum_add_distrib]
  rw [sum_smul_integerAffineMap]
  abel

end WaveTurbulence.Sumint
