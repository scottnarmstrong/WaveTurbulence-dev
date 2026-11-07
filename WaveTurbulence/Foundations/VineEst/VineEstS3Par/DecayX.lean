/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockedExpr
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.DecaySum

/-! # The decay majorant of the weights is summable in the input vector (engine step EXP) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence MeasureTheory Finset
open scoped ENNReal

variable {d : ℕ}

/-- The decay majorant of a weight row: `⟨k⟩^{-N}` for `𝒦`-rows, `1` for `ℒ`-rows. -/
noncomputable def decayWt (D : SumintPar.SumintDatum d) (N : ℕ) : Row D → Mom d → ℝ :=
  Sum.elim (fun _ k => ((jbr k) ^ N)⁻¹) (fun _ _ => 1)

theorem decayWt_nonneg (D : SumintPar.SumintDatum d) (N : ℕ) (ρ : Row D) (k : Mom d) : 0 ≤ decayWt D N ρ k := by
  cases ρ with
  | inl v => exact inv_nonneg.2 (pow_nonneg (Real.sqrt_nonneg _) _)
  | inr v => exact zero_le_one

theorem summable_decayWt (D : SumintPar.SumintDatum d) {L : ℝ} (hL : 0 < L) {N : ℕ} (hN : d + 1 ≤ N)
    (E : Fin 4 → Mom d) :
    Summable fun x : D.S.VIdx → (Fin d → ℤ) => ∏ ρ, decayWt D N ρ (rowMom D L x E ρ) := by
  classical
  set s : D.S.VIdx → Mom d := fun v => ∑ c, (D.H₁ v c : ℝ) • E c with hs
  set F : (D.S.VIdx → (Fin d → ℤ)) → ℝ := fun y => ∏ v, ((jbr (latticePoint L (y v) + s v)) ^ N)⁻¹ with hF
  have hFs : Summable F := by
    have := (WaveTurbulence.VineEstS3.Eng.hasSum_pi_prod (fun (v : D.S.VIdx) (n : Fin d → ℤ) => ((jbr (latticePoint L n + s v)) ^ N)⁻¹)
      (fun v => by
        refine (summable_jbr_pow_lattice hL (s v) hN).congr fun n => ?_
        exact (Real.norm_of_nonneg (inv_nonneg.2 (pow_nonneg (Real.sqrt_nonneg _) _))).symm)).1
    refine this.congr fun y => ?_
    rw [norm_prod]
    exact Finset.prod_congr rfl fun v _ => Real.norm_of_nonneg (inv_nonneg.2 (pow_nonneg (Real.sqrt_nonneg _) _))
  have he := (actEquiv D.T₁ D.T₁inv D.T₁_mul D.T₁inv_mul).summable_iff.2 hFs
  refine he.congr fun x => ?_
  simp only [Function.comp, hF, decayWt, rowMom, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.prod_const_one, mul_one]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [kVec_eq]
  rfl

end WaveTurbulence.VineEstS3Par.Eng
