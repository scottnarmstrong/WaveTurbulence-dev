/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TypeILeafPair
public import WaveTurbulence.Foundations.Molecule.TypeIIScenarios
public import WaveTurbulence.Foundations.Molecule.ConnectedGeometryBridge

/-! # The free-child switch in a unit twist

TARGET Definition twist L1433--L1435. Keep the outer u23 slot and
interchange the other outer slot with the middle slot. The lower branch
changes sign; the roots of both transported free subtrees retain theirs.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Permute the two free child slots while fixing the retained outer slot. -/
@[expose] def freeSwap (keep : Fin 3) : Equiv.Perm (Fin 3) :=
  Equiv.swap 1 (if keep = 0 then 2 else 0)

/-- The retained outer slot is fixed. -/
theorem freeSwap_keep (keep : Fin 3) (hkeep : keep ≠ 1) : freeSwap keep keep = keep := by
  fin_cases keep <;> simp_all [freeSwap,Equiv.swap_apply_def]

/-- The free-child switch is an involution on slots. -/
theorem freeSwap_involutive (keep : Fin 3) : Function.Involutive (freeSwap keep) :=
  Equiv.swap_apply_self _ _

/-- Switch the two free subtrees of a crown. The leaf clause makes this a total tree operation. -/
@[expose] def switchFree (keep : Fin 3) : TTree → TTree
  | .leaf => .leaf
  | .node l m r => if keep = 0 then .node l r m else .node m l r

/-- Switching twice restores the exact ordered tree. -/
theorem switchFree_involutive (keep : Fin 3) : Function.Involutive (switchFree keep) := by
  intro t
  cases t with
  | leaf => rfl
  | node l m r => by_cases h : keep = 0 <;> simp [switchFree,h]

/-- Transport an address with its free subtree. Only its first slot changes. -/
@[expose] def switchPath (keep : Fin 3) : Path → Path
  | [] => []
  | i :: p => freeSwap keep i :: p

/-- Address transport is involutive. -/
theorem switchPath_involutive (keep : Fin 3) : Function.Involutive (switchPath keep) := by
  intro p
  cases p with
  | nil => rfl
  | cons i p => simp only [switchPath,freeSwap_involutive keep i]

/-- Actual leaf addresses are transported to the switched ordered tree. -/
theorem switchPath_leaf_iff (keep : Fin 3) (t : TTree) (p : Path) :
    switchPath keep p ∈ (switchFree keep t).leaves ↔ p ∈ t.leaves := by
  cases t with
  | leaf => cases p <;> simp [switchPath,switchFree,TTree.leaves]
  | node l m r =>
    cases p with
    | nil => by_cases h : keep = 0 <;> simp [switchPath,switchFree,h,TTree.leaves,TTree.pre]
    | cons i p =>
      fin_cases keep <;> fin_cases i <;>
        simp [switchPath,freeSwap,Equiv.swap_apply_def,switchFree,TTree.leaves,TTree.cons_mem_pre]

/-- Actual branching addresses are transported to the switched ordered tree. -/
theorem switchPath_branch_iff (keep : Fin 3) (t : TTree) (p : Path) :
    switchPath keep p ∈ (switchFree keep t).branching ↔ p ∈ t.branching := by
  cases t with
  | leaf => simp [switchFree,TTree.branching]
  | node l m r =>
    cases p with
    | nil => by_cases h : keep = 0 <;> simp [switchPath,switchFree,h,TTree.branching]
    | cons i p =>
      fin_cases keep <;> fin_cases i <;>
        simp [switchPath,freeSwap,Equiv.swap_apply_def,switchFree,TTree.branching,TTree.cons_mem_pre]

/-- The root sign flips; the signs of transported free descendants are preserved. -/
theorem switchPath_sign (keep i : Fin 3) (hkeep : keep ≠ 1) (ζ : ℤˣ) (p : Path) :
    pathSign (-ζ) (switchPath keep (i::p)) =
      if i = keep then -pathSign ζ (i::p) else pathSign ζ (i::p) := by
  fin_cases keep <;> fin_cases i
  all_goals simp_all [switchPath,freeSwap,Equiv.swap_apply_def,pathSign,List.count_cons,pow_succ,
    mul_comm]

end WaveTurbulence.Twist
