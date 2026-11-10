/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCAll2
/-! # VINE-COUNT part 32: **Prop 9.4, Step 1, for every vine-like object removed by `Stage2Op.vine`** (DH23 L1773--L1801).

The VC removed in Step 1 is, by `Prop subsetvc` (L1797: "`𝕍ℂ` is either a single vine, or is formed by two double bonds"),
a single vine (an ordinary VC, or the adjoint of a hyper object: HV and the triple bonds of `subpro` (c)) or two double
bonds `a = x = b` (`DoubleShape`; a VC, or the adjoint of an HVC).  `prop94_vine_all` proves the deviation bound in each
case, with `VINEPARAM` the only vine hypothesis.  NOT covered, and false as a count: a chain of `m ≥ 2` vines that is not
two double bonds (see `FINDING-CHAIN` in `PROGRESS.md`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount WaveTurbulence.CountLemmas

variable {d : ℕ}

/-- The removed VC of `K` is a single vine: of `M` for an ordinary VC, of the adjoint `eraseBond M R.added` for a
hyper object (DH23 L1797, first alternative of `Prop subsetvc`). -/
def SingleVineVC {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    (K : VineCut M) : Prop :=
  match K.C.shape with
  | .vc _ => ∃ X, M.IsVine X K.C.atoms K.C.upper K.C.lower
  | .hyper R => ∃ X, (Molecule.eraseBond M R.added).IsVine X K.C.atoms K.C.upper K.C.lower

theorem dev_const_single {Cf Cs t δ E : ℝ} (d : ℕ) (hCf0 : 0 ≤ Cf) (hCf : Cf ≤ Cs) (ht : 0 < t) (hδ : 0 < δ)
    (hE : 0 ≤ E) :
    Cf * (2 ^ d * (((4 + 8 + 1 : ℕ) : ℝ) / t) ^ (4 + 8 + 1)) * E ≤
      (Cs * (2 ^ d * ((13 : ℝ) / t) ^ 13) * (1 + δ⁻¹)) * E := by
  have hA : 0 ≤ (2 : ℝ) ^ d * ((13 : ℝ) / t) ^ 13 := by positivity
  have h13 : (((4 + 8 + 1 : ℕ) : ℝ)) = 13 := by norm_num
  rw [h13]
  have hs : 0 ≤ Cs := hCf0.trans hCf
  have hδi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  apply mul_le_mul_of_nonneg_right _ hE
  calc Cf * (2 ^ d * (13 / t) ^ (4 + 8 + 1)) ≤ Cs * (2 ^ d * (13 / t) ^ 13) := by
        norm_num; exact mul_le_mul_of_nonneg_right hCf hA
    _ ≤ Cs * (2 ^ d * (13 / t) ^ 13) * (1 + δ⁻¹) := by
        have : 0 ≤ Cs * (2 ^ d * (13 / t) ^ 13) := mul_nonneg hs hA
        nlinarith

theorem dev_const_double {Cd Cs t δ E : ℝ} (d : ℕ) (hCd0 : 0 ≤ Cd) (hCd : Cd ≤ Cs) (ht : 0 < t) (ht2 : t ≤ 2)
    (hδ : 0 < δ) (hE : 0 ≤ E) :
    (Cd * (2 ^ d * (((0 + 8 + 1 : ℕ) : ℝ) / t) ^ (0 + 8 + 1)) * (1 + δ⁻¹)) * E ≤
      (Cs * (2 ^ d * ((13 : ℝ) / t) ^ 13) * (1 + δ⁻¹)) * E := by
  have h9 : (((0 + 8 + 1 : ℕ) : ℝ)) = 9 := by norm_num
  rw [h9]
  have hδi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  have h13 : (1 : ℝ) ≤ 13 / t := (one_le_div ht).2 (by linarith)
  have hp : ((9 : ℝ) / t) ^ (0 + 8 + 1) ≤ ((13 : ℝ) / t) ^ 13 := by
    calc ((9 : ℝ) / t) ^ (0 + 8 + 1) ≤ ((13 : ℝ) / t) ^ (0 + 8 + 1) :=
          pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (by norm_num) ht.le) _
      _ ≤ ((13 : ℝ) / t) ^ 13 := pow_le_pow_right₀ h13 (by norm_num)
  apply mul_le_mul_of_nonneg_right _ hE
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  have hs : 0 ≤ Cs := hCd0.trans hCd
  have h2d : (0 : ℝ) ≤ 2 ^ d := by positivity
  have hq : 0 ≤ ((13 : ℝ) / t) ^ 13 := by positivity
  calc Cd * (2 ^ d * ((9 : ℝ) / t) ^ (0 + 8 + 1)) ≤ Cd * (2 ^ d * ((13 : ℝ) / t) ^ 13) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp h2d) hCd0
    _ ≤ Cs * (2 ^ d * ((13 : ℝ) / t) ^ 13) := mul_le_mul_of_nonneg_right hCd (mul_nonneg h2d hq)


end WaveTurbulence.VineCount
