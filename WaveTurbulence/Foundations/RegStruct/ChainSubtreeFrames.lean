/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.Type1CodeRecovery

/-! # Actual extraction of a chain's hole and side-couple trees -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Partial subtree extraction at the chain's terminal path always returns its filling. -/
theorem plug_subtree_lonePath (X : RegChain) (ζ : ℤˣ) (h : TTree) :
    Comb.subtree (X.plug ζ h) X.lonePath = some h := by
  cases X with
  | nil => simp [RegChain.plug,RegChain.lonePath,Comb.subtree]
  | pair k r g i s =>
    obtain ⟨c,b⟩ := k
    fin_cases c <;> fin_cases b <;>
      simp [RegChain.plug,RegChain.lonePath,node3,MiniTreeCode.lone,
        Comb.subtree_append,Comb.subtree,plug_subtree_lonePath i,plug_subtree_lonePath s]
termination_by structural X

/-- The front red slot contains the selected sign-tree of its actual side couple. -/
theorem chain_red_front_subtree (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (h : TTree) :
    Comb.subtree ((RegChain.pair k r g i s).plug ζ h) [k.red.1] =
      some (treeOfSign r.trees (slotSign ζ k.red.1)) := by
  obtain ⟨c,b⟩ := k
  fin_cases c <;> fin_cases b <;>
    simp [RegChain.plug,node3,MiniTreeCode.red,Comb.subtree]

/-- The back red slot contains the opposite sign-tree of the same side couple. -/
theorem chain_red_back_subtree (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (h : TTree) :
    Comb.subtree ((RegChain.pair k r g i s).plug ζ h) ([k.c] ++ i.lonePath ++ [k.red.2]) =
      some (treeOfSign r.trees (-slotSign ζ k.red.1)) := by
  obtain ⟨c,b⟩ := k
  rcases Int.units_eq_one_or ζ with rfl | rfl
  all_goals
    fin_cases c <;> fin_cases b <;>
      simp [RegChain.plug,node3,MiniTreeCode.red,MiniTreeCode.lone,
        Comb.subtree_append,Comb.subtree,plug_subtree_lonePath i,slotSign,treeOfSign]

/-- The front green slot contains the selected sign-tree of its actual side couple. -/
theorem chain_green_front_subtree (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (h : TTree) :
    Comb.subtree ((RegChain.pair k r g i s).plug ζ h) [k.green.1] =
      some (treeOfSign g.trees (slotSign ζ k.green.1)) := by
  obtain ⟨c,b⟩ := k
  fin_cases c <;> fin_cases b <;>
    simp [RegChain.plug,node3,MiniTreeCode.red,MiniTreeCode.green,Comb.subtree]

/-- The back green slot contains the opposite sign-tree of the same side couple. -/
theorem chain_green_back_subtree (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (h : TTree) :
    Comb.subtree ((RegChain.pair k r g i s).plug ζ h) ([k.c] ++ i.lonePath ++ [k.green.2]) =
      some (treeOfSign g.trees (-slotSign ζ k.green.1)) := by
  obtain ⟨c,b⟩ := k
  rcases Int.units_eq_one_or ζ with rfl | rfl
  all_goals
    fin_cases c <;> fin_cases b <;>
      simp [RegChain.plug,node3,MiniTreeCode.red,MiniTreeCode.green,MiniTreeCode.lone,
        Comb.subtree_append,Comb.subtree,plug_subtree_lonePath i,slotSign,treeOfSign]

end WaveTurbulence.Reg
