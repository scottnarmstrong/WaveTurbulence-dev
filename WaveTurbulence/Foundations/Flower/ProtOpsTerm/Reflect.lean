/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsTerm.ReconId
public import WaveTurbulence.Foundations.Flower.ProtOpsTerm.Weights
public import WaveTurbulence.Foundations.Fourier.Norm00V

/-! # PROT-OPS-TERM: the reflection `(t, u, s) ↦ (t, t+s-u, s)` (determinant `-1`) acting on the last three times

`blk M z = (z_spectators, M z_tail)`. For `M = R3` (an involution of determinant `-1`):
`timeFourier (h ∘ blk R3) l = timeFourier h (blk R3ᵀ l)`, and the `𝔛^{θ,0,0}` norm of `h ∘ blk R3` is at most
`2^θ` times that of `h`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier WaveTurbulence.Flower.ProtTa Matrix
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtOpsTerm

variable {r : ℕ}

def R3 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 1, -1, 1; 0, 0, 1]

theorem R3_mul : R3 * R3 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [R3, Matrix.mul_apply, Fin.sum_univ_three]

theorem R3T_mul : R3ᵀ * R3ᵀ = 1 := by
  rw [← Matrix.transpose_mul, R3_mul, Matrix.transpose_one]

theorem R3_det : |R3.det| = 1 := by
  simp [R3, Matrix.det_fin_three]

theorem R3T_det : |R3ᵀ.det| = 1 := by
  rw [Matrix.det_transpose]; exact R3_det

/-- Block action on the last three coordinates. -/
def blk (M : Matrix (Fin 3) (Fin 3) ℝ) (z : Fin (r + 3) → ℝ) : Fin (r + 3) → ℝ :=
  Fin.append (hd z) (M *ᵥ tl z)

theorem blk_blk {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M * M = 1) (z : Fin (r + 3) → ℝ) :
    blk M (blk M z) = z := by
  simp only [blk, hd_append, tl_append, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
  exact append_hd_tl z

theorem blkMP {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : |M.det| = 1) :
    MeasurePreserving (blk (r := r) M) volume volume := by
  have hdet : M.det ≠ 0 := by intro h; simp [h] at hM
  have hlin : MeasurePreserving (Matrix.toLin' M) := by
    refine ⟨(Matrix.toLin' M).continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet]
    simp only [abs_inv, hM, inv_one, ENNReal.ofReal_one, one_smul]
  have h1 := (MeasurePreserving.id (volume : Measure (Fin r → ℝ))).prod hlin
  have h := ((splitMP r 3).symm).comp (h1.comp (splitMP r 3))
  convert h using 1
  funext z
  simp only [Function.comp_apply, splitE_apply, Prod.map, id, Matrix.toLin'_apply, blk]
  rw [splitE_symm]

/-- The block action as a measurable equivalence, for an involution. -/
def blkE {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M * M = 1) (hd : |M.det| = 1) :
    (Fin (r + 3) → ℝ) ≃ᵐ (Fin (r + 3) → ℝ) where
  toFun := blk M
  invFun := blk M
  left_inv := blk_blk hM
  right_inv := blk_blk hM
  measurable_toFun := (blkMP (r := r) hd).measurable
  measurable_invFun := (blkMP (r := r) hd).measurable

theorem blkE_mp {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M * M = 1) (hd : |M.det| = 1) :
    MeasurePreserving (blkE (r := r) hM hd) volume volume := blkMP hd

theorem pairing_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ) :
    timePairing 3 a (M *ᵥ b) = timePairing 3 (Mᵀ *ᵥ a) b := by
  change a ⬝ᵥ (M *ᵥ b) = (Mᵀ *ᵥ a) ⬝ᵥ b
  rw [dotProduct_mulVec, Matrix.mulVec_transpose]

theorem pairing_blk (M : Matrix (Fin 3) (Fin 3) ℝ) (l w : Fin (r + 3) → ℝ) :
    timePairing (r + 3) l (blk M w) = timePairing (r + 3) (blk Mᵀ l) w := by
  rw [blk, pairing_split, pairing_mulVec]
  conv_rhs => rw [pairing_split']
  simp only [blk, hd_append, tl_append]

theorem pairing_comm' {n : ℕ} (a b : Fin n → ℝ) : timePairing n a b = timePairing n b a := by
  simp only [pairing_apply, mul_comm]

theorem timeFourier_blk {h : (Fin (r + 3) → ℝ) → ℂ} (l : Fin (r + 3) → ℝ) :
    timeFourier (fun z => h (blk R3 z)) l = timeFourier h (blk R3ᵀ l) := by
  have hE := blkE_mp (r := r) R3_mul R3_det
  unfold timeFourier VectorFourier.fourierIntegral
  have := hE.integral_comp' (g := fun w : Fin (r + 3) → ℝ =>
    (Real.fourierChar (-(timePairing (r + 3) w (blk R3ᵀ l))) : Circle) • h w)
  refine Eq.trans ?_ this
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  show _ = (Real.fourierChar (-(timePairing (r + 3) (blk R3 z) (blk R3ᵀ l))) : Circle) • h (blk R3 z)
  rw [pairing_comm' (blk R3 z), pairing_blk, blk_blk R3T_mul, pairing_comm']

end WaveTurbulence.Flower.ProtOpsTerm
