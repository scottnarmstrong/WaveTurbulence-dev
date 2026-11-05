/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawChainInsertion

/-! # Exact identity chain insertion, including arbitrary raw address frames -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem setAt_subtreeAt_self (t : TTree) (p : Path) : t.setAt p (t.subtreeAt p) = t := by
  cases p with
  | nil => simp [TTree.setAt,TTree.subtreeAt]
  | cons i p =>
    cases t with
    | leaf => rfl
    | node l m r =>
      fin_cases i <;> simp [TTree.setAt,TTree.subtreeAt,
        setAt_subtreeAt_self l,setAt_subtreeAt_self m,setAt_subtreeAt_self r]
termination_by structural t

theorem stretch_nil {w : ℕ} (a z : Address w) : stretch a [] z = z := by
  by_cases h : Below a z
  · obtain ⟨p,hp⟩ := below_exists_frame a z h
    rw [hp,stretch_frame]
    rfl
  · exact stretch_outside a [] z h

theorem Raw.insertChain_nil {w : ℕ} (R : Raw w) (a : Address w) : R.insertChain a .nil = R := by
  classical
  apply Raw.ext
  · rfl
  · simp only [Raw.insertChain,RegChain.plug,setAt_subtreeAt_self,Function.update_eq_self]
  · simp only [Raw.insertChain,RegChain.lonePath,stretch_nil,RegChain.pairsAt,List.toFinset_nil,
      Finset.union_empty,Prod.eta]
    exact Finset.image_id

end WaveTurbulence.Reg.Skeleton
