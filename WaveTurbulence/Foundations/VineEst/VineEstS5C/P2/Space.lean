/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4c.LeibnizPack
public import WaveTurbulence.Foundations.VineEst.VineEstS4c.RowForms
public import WaveTurbulence.Foundations.VineEst.VineEstS3.SNormAux

/-! # P2: the spatial weights of the vine rows, uniform in `r` (4d-A item (iii), R30)

Real spatial factors `M, N : ℝ^d → ℝ` (the `M_i` of `LeafwiseSeparated`, `SNormR` bounds) enter the vine rows through the
`r`-dependent weights

* `spShift c M ε r k = c · M(k + ε r)`, `spDiff c M ε r k = c · (M(k + ε r) - M(k))/|r|`,
* `spProdDiff c M N ε r k = c · (N(k+ε r) - N(k))/|r| · M(k)`   (`ε = ±1`),

each cut off to `‖r‖ ≤ 1` (`cutW`; the engine only uses `r = e - f` with `‖r‖ ≤ L^{-γ+η} ≤ 1`).  `snorm_*`: the bound
`sup_r ‖·‖_{𝔖^{A,W}}` with `A + 1` derivatives on the input (R30: the difference quotient loses one derivative). -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS3.Eng
open scoped ENNReal

variable {d : ℕ}

/-- The complex embedding of a real function. -/
def cm (M : Mom d → ℝ) : Mom d → ℂ := fun k => (M k : ℂ)

/-- Cut-off of an `r`-dependent weight to `‖r‖ ≤ 1`. -/
noncomputable def cutW (g : Mom d → Mom d → ℂ) : Mom d → Mom d → ℂ :=
  fun r k => if ‖r‖ ≤ 1 then g r k else 0

theorem cutW_of_le {g : Mom d → Mom d → ℂ} {r : Mom d} (hr : ‖r‖ ≤ 1) (k : Mom d) : cutW g r k = g r k := by
  simp [cutW, hr]

theorem SNorm_zero' (A B : ℕ) : SNorm A B (fun _ : Mom d => (0 : ℂ)) = 0 := by
  have := VineEstS3.Eng.SNorm_smul_le (d := d) A B 0 (fun _ => 0)
  simpa using this

theorem snorm_cutW_le {A W : ℕ} (g : Mom d → Mom d → ℂ) {B : ℝ≥0∞}
    (h : ∀ r, ‖r‖ ≤ 1 → SNorm A W (g r) ≤ B) : ⨆ r : Mom d, SNorm A W (cutW g r) ≤ B := by
  refine iSup_le fun r => ?_
  by_cases hr : ‖r‖ ≤ 1
  · have : cutW g r = g r := funext fun k => cutW_of_le hr k
    rw [this]; exact h r hr
  · have : cutW g r = fun _ => 0 := funext fun k => by simp [cutW, hr]
    rw [this, SNorm_zero']; exact bot_le

/-- `(M(k + a) - M(k))/|a|` times a constant. -/
noncomputable def spDiff (c : ℝ) (M : Mom d → ℝ) (ε : ℝ) : Mom d → Mom d → ℂ :=
  cutW fun r k => (c : ℂ) * diffQuot (ε • r) (cm M) k

noncomputable def spShift (c : ℝ) (M : Mom d → ℝ) (ε : ℝ) : Mom d → Mom d → ℂ :=
  cutW fun r k => (c : ℂ) * (M (k + ε • r) : ℂ)

noncomputable def spProdDiff (c : ℝ) (M N : Mom d → ℝ) (ε : ℝ) : Mom d → Mom d → ℂ :=
  cutW fun r k => (c : ℂ) * (diffQuot (ε • r) (cm N) k * (M k : ℂ))

/-- The `r`-independent constant multiple. -/
def spPlain (c : ℝ) (M : Mom d → ℝ) : Mom d → Mom d → ℂ := fun _ k => (c : ℂ) * (M k : ℂ)

/-- The `r`-independent product `c M N`. -/
def spProd (c : ℝ) (M N : Mom d → ℝ) : Mom d → Mom d → ℂ := fun _ k => (c : ℂ) * ((N k : ℂ) * (M k : ℂ))

/-- The constant weight. -/
def spOne : Mom d → Mom d → ℂ := fun _ _ => 1

theorem norm_smul_unit {ε : ℝ} (hε : |ε| ≤ 1) {r : Mom d} (hr : ‖r‖ ≤ 1) : ‖ε • r‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs]
  calc |ε| * ‖r‖ ≤ 1 * 1 := mul_le_mul hε hr (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

variable {A W : ℕ} {M N : Mom d → ℝ} {βM βN : ℝ}

theorem snorm_plain_le (hA : A ≠ 0) (c : ℝ) (hβ : 0 ≤ βM)
    (hM : SNorm A W (cm M) ≤ ENNReal.ofReal βM) :
    ⨆ r : Mom d, SNorm A W (spPlain c M r) ≤ ENNReal.ofReal (|c| * βM) := by
  refine iSup_le fun r => ?_
  refine (VineEstS3.Eng.SNorm_smul_le A W (c : ℂ) (cm M)).trans ?_
  rw [ENNReal.ofReal_mul (abs_nonneg c)]
  refine mul_le_mul' (le_of_eq ?_) hM
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]

theorem snorm_one_le' (A : ℕ) : ⨆ r : Mom d, SNorm A 0 (spOne r) ≤ ENNReal.ofReal 1 :=
  iSup_le fun _ => SNorm_one_le A

end WaveTurbulence.VineEstS5C.P2
