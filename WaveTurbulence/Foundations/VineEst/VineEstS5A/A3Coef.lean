/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Scalar
public import WaveTurbulence.Foundations.VineEst.VineEstS3.SNormAux
public import WaveTurbulence.Foundations.XChain.SNormOperations

/-! # Coefficient families of arity-3 rows: separated terms and finite sums (V5 Step 4d-A, item 2)

`coefBound θ A B c = ∑_m ⟨m/2⟩^θ sup_r ‖c m r‖_{S^{A,B}}` is the size of a mode family (the `fs_bound` field of
`ClockedModes3`).  A separated family `c m r k = ĥ_m M(r,k)` costs `(∑_m ⟨m/2⟩^θ |ĥ_m|) · sup_r ‖M(r)‖_S`, and a
finite sum of families costs at most the sum of the costs.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5A
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS3.Eng MeasureTheory Finset
open scoped ENNReal

variable {d : ℕ}

/-- The size of a family of mode coefficients (functions of `r` and of the momentum). -/
noncomputable def coefBound (θ : ℝ) (A B : ℕ) (c : (Fin 3 → ℤ) → Mom d → Mom d → ℂ) : ℝ≥0∞ :=
  ∑' m : Fin 3 → ℤ, maxBracketPow θ (half m) * ⨆ r : Mom d, SNorm A B (c m r)

/-- A separated family: time coefficients `ĥ` times a spatial function of `(r, k)`. -/
def sepCoef (h : (Fin 3 → ℤ) → ℂ) (M : Mom d → Mom d → ℂ) : (Fin 3 → ℤ) → Mom d → Mom d → ℂ :=
  fun m r k => h m * M r k

theorem coefBound_sep_le (θ : ℝ) (A B : ℕ) (h : (Fin 3 → ℤ) → ℂ) (M : Mom d → Mom d → ℂ) :
    coefBound θ A B (sepCoef h M) ≤
      (∑' m : Fin 3 → ℤ, maxBracketPow θ (half m) * ‖h m‖ₑ) * ⨆ r : Mom d, SNorm A B (M r) := by
  unfold coefBound
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun m => ?_
  rw [mul_assoc]
  refine mul_le_mul_right ?_ _
  calc ⨆ r : Mom d, SNorm A B (sepCoef h M m r)
      ≤ ⨆ r : Mom d, ‖h m‖ₑ * SNorm A B (M r) :=
        iSup_mono fun r => SNorm_smul_le A B (h m) (M r)
    _ = ‖h m‖ₑ * ⨆ r : Mom d, SNorm A B (M r) := ENNReal.mul_iSup _ _ |>.symm

/-- Triangle inequality for `SNorm` of a finite sum (`A ≠ 0`). -/
theorem SNorm_finsetSum_le {ι : Type*} {A B : ℕ} (hA : A ≠ 0) (s : Finset ι) (f : ι → Mom d → ℂ) :
    SNorm A B (fun x => ∑ i ∈ s, f i x) ≤ ∑ i ∈ s, SNorm A B (f i) := by
  classical
  by_cases htop : ∃ i ∈ s, SNorm A B (f i) = ⊤
  · obtain ⟨i, hi, hit⟩ := htop
    refine le_trans le_top (le_of_eq ?_)
    symm
    rw [ENNReal.sum_eq_top]
    exact ⟨i, hi, hit⟩
  have htop' : ∀ i ∈ s, SNorm A B (f i) ≠ ⊤ := fun i hi h => htop ⟨i, hi, h⟩
  have hcd : ∀ i ∈ s, ContDiff ℝ A (f i) := by
    intro i hi
    by_contra hnc
    apply htop' i hi
    simp [SNorm, hA, hnc]
  have hb := SNorm_finset_sum_bound (A := A) (B := B) s f (fun i => (SNorm A B (f i)).toReal) hcd
    (fun i _ => ENNReal.toReal_nonneg) (fun i hi => (ENNReal.ofReal_toReal (htop' i hi)).symm.le)
  refine hb.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
  exact Finset.sum_congr rfl fun i hi => ENNReal.ofReal_toReal (htop' i hi)

theorem coefBound_finsetSum_le {ι : Type*} (θ : ℝ) {A B : ℕ} (hA : A ≠ 0) (s : Finset ι)
    (c : ι → (Fin 3 → ℤ) → Mom d → Mom d → ℂ) :
    coefBound θ A B (fun m r k => ∑ i ∈ s, c i m r k) ≤ ∑ i ∈ s, coefBound θ A B (c i) := by
  classical
  unfold coefBound
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun m => ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_right ?_ _
  refine iSup_le fun r => ?_
  refine (SNorm_finsetSum_le hA s (fun i => c i m r)).trans ?_
  exact Finset.sum_le_sum fun i _ => le_iSup (fun r' => SNorm A B (c i m r')) r

end WaveTurbulence.VineEstS5A
