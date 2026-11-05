/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.CellSingularBlocks

/-! # Literal natural-order singular folds, without a permutation of operators -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open ApproxNT

/-- The descending recursive construction and the natural outer-to-inner list have
exactly the same operator order. No exchange of singular operations is used. -/
theorem tree_appIter_eq_appAlong {d n : ℕ} (J : Finset (Fin n))
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) (k : ℕ) (hk : k ≤ n) :
    appIter J W k = appAlong J (List.ofFn (fun i : Fin k => (⟨n-k+i,by omega⟩ : Fin n))) W := by
  induction k with
  | zero => simp only [appIter,List.ofFn_zero,appAlong]
  | succ k ih =>
    rw [appIter, dite_eq_left (by omega), List.ofFn_succ,appAlong,ih (by omega)]
    congr 2
    · simp only [Fin.val_zero, Nat.add_zero]
      omega
    · apply congrArg List.ofFn
      funext i
      apply Fin.ext
      simp only [Fin.val_succ]
      omega

/-- The original singular integral is exactly its natural-order fold at zero. -/
theorem tree_appAlong_finRange_eq_singInt {d n : ℕ} (J : Finset (Fin n))
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) :
    appAlong J (List.finRange n) W 0 0 = singInt J W := by
  rw [singInt,tree_appIter_eq_appAlong J W n (le_refl _)]
  congr 2
  rw [← List.ofFn_id]
  congr 1
  funext i
  apply Fin.ext
  simp

end WaveTurbulence.RegAsymp
