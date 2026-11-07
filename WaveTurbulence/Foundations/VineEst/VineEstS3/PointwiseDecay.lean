/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.Pointwise
public import WaveTurbulence.Foundations.Spine.XNormWeightPointwise

/-! # Pointwise decay from weighted restriction norms

`norm_le_decay_of_XNormRestr`: for `F` continuous in time, `‖F t k‖ ≤ β jbr(k)^{-N}` at every `t ∈ closure (interior T)` when
`‖F‖_{𝔛^{θ,A,N}(T)} < β` (via `LGSpine.XNorm00Restr_weight_le_XNormRestr` and the continuity-based pointwise bound).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS3
open WaveTurbulence MeasureTheory
open scoped ENNReal

theorem norm_le_decay_of_XNormRestr {r d : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (A N : ℕ) (T : Set (Fin r → ℝ))
    (F : (Fin r → ℝ) → Mom d → ℂ) (β : ℝ) (hβ : XNormRestr θ A N T Set.univ F < ENNReal.ofReal β)
    (t : Fin r → ℝ) (ht : t ∈ closure (interior T)) (k : Mom d) (hc : Continuous fun s => F s k) :
    ‖F t k‖ ≤ β * ((jbr k) ^ N)⁻¹ := by
  have hc' : Continuous fun s : Fin r → ℝ => ((jbr k ^ N : ℝ) : ℂ) * F s k := continuous_const.mul hc
  have h := enorm_le_XNorm00Restr_of_continuous (V := Mom d) hθ T Set.univ
    (fun s k => ((jbr k ^ N : ℝ) : ℂ) * F s k) t k ht (Set.mem_univ k) hc'
  have h2 := (h.trans (LGSpine.XNorm00Restr_weight_le_XNormRestr θ A N T Set.univ F)).trans_lt hβ
  rw [← ofReal_norm] at h2
  have h3 := (ENNReal.ofReal_lt_ofReal_iff'.1 h2).1
  have hj : 0 < jbr k ^ N := pow_pos (Induct.jbr_pos k) N
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hj.le] at h3
  rw [← div_eq_mul_inv, le_div_iff₀ hj]
  linarith

end WaveTurbulence.VineEstS3
