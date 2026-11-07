/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemShift

/-! # P4-W2 (R78, F-REM-ORIENT): utilities for the three-clock remainder x remainder row

* `snorm_tsum_le`: the weighted `𝔖` norm of a countable sum of smooth functions (`Mathlib.iteratedFDeriv_tsum`).
* `maxBracketPow_prod_le`: the bracket weight of the merged modes `(a₀, b₀, a₁ + b₁)` is at most `√2^θ` times the product of those of `a = (a₀,a₁)` and `b = (b₀,b₁)`.
* `fsPhase_merge`: the phase of the merged modes is the product of the phases. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS4c MeasureTheory WaveTurbulence.LGSpine
open scoped ENNReal

/-- **`𝔖` norm of a countable sum.** -/
theorem snorm_tsum_le {d A B : ℕ} {ι : Type*} (hd : 1 ≤ d) (hA : A ≠ 0) (T : ι → Mom d → ℂ) (E : ι → ℝ≥0∞)
    (hE : ∑' i, E i ≠ ⊤) (hT : ∀ i, SNorm A B (T i) ≤ E i) :
    SNorm A B (fun k => ∑' i, T i k) ≤ ENNReal.ofReal ((d : ℝ) ^ A) * ∑' i, E i := by
  have hEi : ∀ i, E i ≠ ⊤ := fun i => ne_top_of_le_ne_top hE (ENNReal.le_tsum i)
  set S : ι → ℝ := fun i => (E i).toReal with hS
  have hS0 : ∀ i, 0 ≤ S i := fun i => ENNReal.toReal_nonneg
  have hSsum : Summable S := ENNReal.summable_toReal hE
  have hTS : ∀ i, SNorm A B (T i) ≤ ENNReal.ofReal (S i) := fun i => by
    rw [hS]; simp only; rw [ENNReal.ofReal_toReal (hEi i)]; exact hT i
  have hTc : ∀ i, ContDiff ℝ A (T i) := fun i => contDiff_of_SNorm_le' hA (T i) (S i) (hTS i)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hbd : ∀ (n : ℕ) (i : ι) (x : Mom d), n ≤ A → jbr x ^ B * ‖iteratedFDeriv ℝ n (T i) x‖ ≤ (d : ℝ) ^ n * S i :=
    fun n i x hn => SNorm_frechet_pointwise (T i) (hTc i) (S i) (hS0 i) (hTS i) hn x
  have hbd' : ∀ (n : ℕ) (i : ι) (x : Mom d), n ≤ A → ‖iteratedFDeriv ℝ n (T i) x‖ ≤ (d : ℝ) ^ n * S i :=
    fun n i x hn => le_trans (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (one_le_jbr x))) (hbd n i x hn)
  have hv : ∀ n : ℕ, (n : ℕ∞) ≤ (A : ℕ∞) → Summable (fun i => (d : ℝ) ^ n * S i) := fun n _ => hSsum.mul_left _
  have hfd : ContDiff ℝ A (fun k => ∑' i, T i k) :=
    contDiff_tsum (N := (A : ℕ∞)) hTc hv (fun n i x hn => hbd' n i x (by exact_mod_cast hn))
  have hrw : ENNReal.ofReal ((d : ℝ) ^ A) * ∑' i, E i = ENNReal.ofReal ((d : ℝ) ^ A * ∑' i, S i) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_tsum_of_nonneg hS0 hSsum]
    congr 1
    refine tsum_congr fun i => ?_
    rw [hS]; simp only; rw [ENNReal.ofReal_toReal (hEi i)]
  rw [hrw]
  refine SNorm_le_of_frechet_bounds _ hfd _ fun n hn x => ?_
  rw [iteratedFDeriv_tsum_apply (N := (A : ℕ∞)) hTc hv (fun n i x hn => hbd' n i x (by exact_mod_cast hn)) (by exact_mod_cast hn)]
  have hsm : Summable (fun i => ‖iteratedFDeriv ℝ n (T i) x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hbd' n i x hn) (hv n (by exact_mod_cast hn))
  calc jbr x ^ B * ‖∑' i, iteratedFDeriv ℝ n (T i) x‖
      ≤ jbr x ^ B * ∑' i, ‖iteratedFDeriv ℝ n (T i) x‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsm) (pow_nonneg (jbr_pos x).le B)
    _ = ∑' i, jbr x ^ B * ‖iteratedFDeriv ℝ n (T i) x‖ := (tsum_mul_left).symm
    _ ≤ ∑' i, (d : ℝ) ^ n * S i := by
        refine Summable.tsum_le_tsum (fun i => hbd n i x hn) ?_ (hv n (by exact_mod_cast hn))
        exact hsm.mul_left _
    _ = (d : ℝ) ^ n * ∑' i, S i := tsum_mul_left
    _ ≤ (d : ℝ) ^ A * ∑' i, S i :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1 hn) (tsum_nonneg hS0)

/-- The merged mode of two two-clock modes `a` (clocks `c₀, c₂`) and `b` (clocks `c₁, c₂`): the shared clock `c₂` adds. -/
def mergeMode (a b : Fin 2 → ℤ) : Fin 3 → ℤ := ![a 0, b 0, a 1 + b 1]

/-- The bracket weight of the merged modes is at most `√2^θ` times the product of the weights. -/
theorem maxBracketPow_merge_le {θ : ℝ} (hθ : 0 ≤ θ) (a b : Fin 2 → ℤ) :
    maxBracketPow θ (half (mergeMode a b)) ≤
      ENNReal.ofReal (Real.sqrt 2 ^ θ) * (maxBracketPow θ (half a) * maxBracketPow θ (half b)) := by
  set Ma : ℝ := ((⨆ i, Real.sqrt (1 + (half a) i ^ 2)) ⊔ 1) with hMa
  set Mb : ℝ := ((⨆ i, Real.sqrt (1 + (half b) i ^ 2)) ⊔ 1) with hMb
  have hMa1 : 1 ≤ Ma := le_sup_right
  have hMb1 : 1 ≤ Mb := le_sup_right
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.one_le_sqrt]; norm_num
  have hMaA : ∀ i, Real.sqrt (1 + (half a) i ^ 2) ≤ Ma := fun i =>
    le_trans (le_ciSup (f := fun i => Real.sqrt (1 + (half a) i ^ 2)) (Set.finite_range _).bddAbove i) le_sup_left
  have hMbB : ∀ i, Real.sqrt (1 + (half b) i ^ 2) ≤ Mb := fun i =>
    le_trans (le_ciSup (f := fun i => Real.sqrt (1 + (half b) i ^ 2)) (Set.finite_range _).bddAbove i) le_sup_left
  have hprod : 1 ≤ Ma * Mb := one_le_mul_of_one_le_of_one_le hMa1 hMb1
  have hkey : (⨆ i, Real.sqrt (1 + (half (mergeMode a b)) i ^ 2)) ⊔ 1 ≤ Real.sqrt 2 * (Ma * Mb) := by
    refine sup_le (ciSup_le fun i => ?_) (by nlinarith)
    have hMM : Ma ≤ Real.sqrt 2 * (Ma * Mb) := by nlinarith
    have hMM' : Mb ≤ Real.sqrt 2 * (Ma * Mb) := by nlinarith
    fin_cases i
    · exact (hMaA 0).trans hMM
    · exact (hMbB 0).trans hMM'
    · simp only [half, mergeMode, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Fin.isValue]
      have h1 : Real.sqrt (1 + (((a 1 + b 1 : ℤ) : ℝ) / 2) ^ 2) ≤
          Real.sqrt 2 * (Real.sqrt (1 + (((a 1 : ℤ) : ℝ) / 2) ^ 2) * Real.sqrt (1 + (((b 1 : ℤ) : ℝ) / 2) ^ 2)) := by
        rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
        apply Real.sqrt_le_sqrt
        push_cast
        nlinarith [sq_nonneg (((a 1 : ℤ) : ℝ) / 2), sq_nonneg (((b 1 : ℤ) : ℝ) / 2), mul_nonneg (sq_nonneg (((a 1 : ℤ) : ℝ) / 2)) (sq_nonneg (((b 1 : ℤ) : ℝ) / 2)),
          sq_nonneg (((a 1 : ℤ) : ℝ) / 2 - ((b 1 : ℤ) : ℝ) / 2)]
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have ha := hMaA 1
      have hb := hMbB 1
      simp only [half, Fin.isValue] at ha hb
      exact mul_le_mul ha hb (Real.sqrt_nonneg _) (by linarith)
  unfold maxBracketPow
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((⨆ i, Real.sqrt (1 + (half (mergeMode a b)) i ^ 2)) ⊔ 1) ^ θ ≤ (Real.sqrt 2 * (Ma * Mb)) ^ θ :=
        Real.rpow_le_rpow (le_trans (by norm_num) le_sup_right) hkey hθ
    _ = Real.sqrt 2 ^ θ * (Ma ^ θ * Mb ^ θ) := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]

/-- The phase of the merged modes is the product of the phases. -/
theorem fsPhase_merge (a b : Fin 2 → ℤ) (t0 t1 t2 : ℝ) :
    fsPhase (mergeMode a b) ![t0, t1, t2] = fsPhase a ![t0, t2] * fsPhase b ![t1, t2] := by
  unfold fsPhase
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [Fourier.timePairing, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, mergeMode, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, add_zero, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk, dotProductBilin]
  push_cast
  ring


end WaveTurbulence.VineEstS5C.P4.W2
