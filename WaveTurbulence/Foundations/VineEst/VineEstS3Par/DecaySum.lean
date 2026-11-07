/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.SumintDatum

public import WaveTurbulence.Frozen.Defs.SumintDatumAdmissible

public import WaveTurbulence.Frozen.Defs.SumintDatumEllVec

public import WaveTurbulence.Frozen.Defs.SumintDatumExpr

public import WaveTurbulence.Frozen.Defs.SumintDatumKVec

public import WaveTurbulence.Frozen.Defs.SumintDatumM0

public import WaveTurbulence.Frozen.Defs.SumintDatumM1

public import WaveTurbulence.Frozen.Defs.SumintDatumPhase

public import WaveTurbulence.Frozen.Defs.SumintDatumTimeDom

public import WaveTurbulence.Frozen.Defs.SumintShape

public import WaveTurbulence.Frozen.Defs.SumintShapeLexLt

public import WaveTurbulence.Frozen.Defs.SumintShapeM

public import WaveTurbulence.Frozen.Defs.SumintShapeN

public import WaveTurbulence.Frozen.Defs.SumintShapeTVar

public import WaveTurbulence.Frozen.Defs.SumintShapeUSlot

public import WaveTurbulence.Frozen.Defs.SumintShapeVIdx

public import WaveTurbulence.Frozen.Defs.SumintShapeX0Slot

public import WaveTurbulence.Frozen.Defs.SumintShapeXSlot

public import WaveTurbulence.Frozen.Defs.SumintShapeYSlot
public import WaveTurbulence.Foundations.NTSP.LatticeSums
public import WaveTurbulence.Foundations.VineEst.VineEstS3.PiProd
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockPhase

/-! # Summability of the weight decay over the input lattice (engine step EXP)

`∑_x ∏_v ⟨k_v(x)⟩^{-N}` converges for `N ≥ d+1`: the map `x ↦ T₁ x` is a bijection of the integer lattice
(`T₁` has the integer inverse `T₁inv`), and `k_v(x) = (T₁ x)_v / L + s_v`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence MeasureTheory Finset
open scoped ENNReal

variable {d : ℕ}

/-- The lattice embedding as an additive homomorphism. -/
noncomputable def lpHom (d : ℕ) (L : ℝ) : (Fin d → ℤ) →+ Mom d where
  toFun := latticePoint L
  map_zero' := by ext j; simp [latticePoint]
  map_add' a b := by ext j; simp [latticePoint, Int.cast_add, add_div]

theorem lpHom_apply (L : ℝ) (n : Fin d → ℤ) : lpHom d L n = latticePoint L n := rfl

/-- Integer matrix action on lattice vectors indexed by `ι`. -/
def actM {ι : Type*} [Fintype ι] (M : Matrix ι ι ℤ) (x : ι → (Fin d → ℤ)) : ι → (Fin d → ℤ) :=
  fun v => ∑ v', M v v' • x v'

theorem actM_actM {ι : Type*} [Fintype ι] (M N : Matrix ι ι ℤ) (x : ι → (Fin d → ℤ)) :
    actM N (actM M x) = actM (N * M) x := by
  funext v
  simp only [actM, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v' _ => ?_
  rw [mul_smul]

theorem actM_one {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → (Fin d → ℤ)) :
    actM (1 : Matrix ι ι ℤ) x = x := by
  funext v
  simp [actM, Matrix.one_apply]

/-- The bijection `x ↦ T₁ x` of the integer lattice. -/
def actEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (T Tinv : Matrix ι ι ℤ) (h1 : T * Tinv = 1)
    (h2 : Tinv * T = 1) : (ι → (Fin d → ℤ)) ≃ (ι → (Fin d → ℤ)) where
  toFun := actM T
  invFun := actM Tinv
  left_inv x := by rw [actM_actM, h2, actM_one]
  right_inv x := by rw [actM_actM, h1, actM_one]

theorem kVec_eq {d : ℕ} (D : SumintPar.SumintDatum d) (L : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (E : Fin 4 → Mom d)
    (v : D.S.VIdx) :
    D.kVec L x E v = latticePoint L (actM D.T₁ x v) + ∑ c, (D.H₁ v c : ℝ) • E c := by
  unfold SumintPar.SumintDatum.kVec actM
  congr 1
  rw [← lpHom_apply, map_sum]
  refine Finset.sum_congr rfl fun v' _ => ?_
  rw [map_zsmul, lpHom_apply]
  exact Int.cast_smul_eq_zsmul ℝ _ _


theorem jbr_ge_mul (z : Mom d) : (1 + ‖z‖) / Real.sqrt 2 ≤ jbr z := by
  unfold jbr
  rw [div_le_iff₀ (Real.sqrt_pos.2 (by norm_num)), ← Real.sqrt_mul (by positivity)]
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith [sq_nonneg (‖z‖ - 1), norm_nonneg z]

/-- One lattice variable: `∑_n ⟨n/L + s⟩^{-N} < ∞` for `N ≥ d + 1`. -/
theorem summable_jbr_pow_lattice {L : ℝ} (hL : 0 < L) (s : Mom d) {N : ℕ} (hN : d + 1 ≤ N) :
    Summable fun n : Fin d → ℤ => ((jbr (latticePoint L n + s)) ^ N)⁻¹ := by
  set κ : ℝ := min 1 L⁻¹ / Real.sqrt 2 with hκ
  have hκpos : 0 < κ := div_pos (lt_min one_pos (inv_pos.2 hL)) (Real.sqrt_pos.2 (by norm_num))
  have hbound : ∀ n : Fin d → ℤ, ((jbr (latticePoint L n + s)) ^ N)⁻¹ ≤
      (κ ^ N)⁻¹ * ((1 + ‖NTSP.intVec n + L • s‖) ^ (d + 1))⁻¹ := by
    intro n
    set w : Mom d := NTSP.intVec n + L • s with hw
    have hz : latticePoint L n + s = L⁻¹ • w := by
      ext j
      simp [latticePoint, NTSP.intVec, hw]
      field_simp
    have hnz : ‖latticePoint L n + s‖ = L⁻¹ * ‖w‖ := by
      rw [hz, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hL.le)]
    have h1 : κ * (1 + ‖w‖) ≤ jbr (latticePoint L n + s) := by
      refine le_trans ?_ (jbr_ge_mul _)
      rw [hnz, hκ, div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg 2)
      have hm : min 1 L⁻¹ ≤ 1 := min_le_left _ _
      have hm' : min 1 L⁻¹ ≤ L⁻¹ := min_le_right _ _
      nlinarith [norm_nonneg w, mul_le_mul_of_nonneg_right hm' (norm_nonneg w)]
    have hw1 : 1 ≤ 1 + ‖w‖ := by linarith [norm_nonneg w]
    have h2 : (κ * (1 + ‖w‖)) ^ N ≤ (jbr (latticePoint L n + s)) ^ N :=
      pow_le_pow_left₀ (by positivity) h1 N
    have h3 : (1 + ‖w‖) ^ (d + 1) ≤ (1 + ‖w‖) ^ N := pow_le_pow_right₀ hw1 hN
    rw [← mul_inv]
    refine inv_anti₀ (mul_pos (pow_pos hκpos _) (pow_pos (by linarith [norm_nonneg w]) _)) ?_
    calc κ ^ N * (1 + ‖w‖) ^ (d + 1) ≤ κ ^ N * (1 + ‖w‖) ^ N :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (κ * (1 + ‖w‖)) ^ N := (mul_pow _ _ _).symm
      _ ≤ _ := h2
  refine Summable.of_nonneg_of_le (fun n => inv_nonneg.2 (pow_nonneg (Real.sqrt_nonneg _) _)) hbound ?_
  exact (NTSP.summable_lattice (L • s)).mul_left _

end WaveTurbulence.VineEstS3Par.Eng
