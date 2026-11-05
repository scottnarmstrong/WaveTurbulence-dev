/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SpliceLeafPieces
public import WaveTurbulence.Foundations.Molecule.PrunedChildExtension
import Mathlib.Tactic

/-! # Incomparability of the three CL boundary subtrees
TARGET `block_clcn` (2): the upper excluded child and the two lower
excluded children are disjoint rooted subtrees of the original tree.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} (G : Garden w)

theorem different_children_incomparable (b : GBranch G.tree) (i j : Fin 3) (hn : i ≠ j) :
    (b.child i).Incomparable (b.child j) := by
  have hno : ∀ i j : Fin 3, i ≠ j → ¬ (b.child i).IsDesc (b.child j) := by
    intro i j hn hd
    have hl : (b.child j).1.2.length ≤ (b.child i).1.2.length := by
      simp only [GBranch.child,List.length_append,List.length_singleton]
      omega
    have hp := hd.2.eq_of_length_le hl
    have he : b.child i = b.child j := Subtype.ext (Prod.ext hd.1 hp)
    have h := child_pair_injective G (a₁ := (b,i)) (a₂ := (b,j)) he
    exact hn (congrArg Prod.snd h)
  exact ⟨hno i j hn,hno j i hn.symm⟩

theorem upper_excluded_lower_child_incomparable {S : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b)
    (i j : Fin 3) (hi : i.succ ∉ internalPositions G S a) :
    (a.child i).Incomparable (b.child j) := by
  have hlen := (cl_parent_strict_descendant G hB hCL).2
  have hnot := cl_excluded_child_no_descendant G hB hCL hB.2.1 hB.2.2.1 i hi
  constructor
  · intro hd
    have hne : (a.child i).1.2 ≠ (b.child j).1.2 := by
      intro he
      have hh := congrArg List.length he
      simp only [GBranch.child,List.length_append,List.length_singleton] at hh
      omega
    have hp := proper_prefix_dropLast hd.2 hne
    apply hnot
    refine ⟨hd.1,?_⟩
    simpa only [GBranch.child,GBranch.toNode,List.dropLast_append_cons,
      List.dropLast_singleton,List.append_nil] using hp
  · intro hd
    have hl := hd.2.length_le
    simp only [GBranch.child,List.length_append,List.length_singleton] at hl
    omega

/-- The other outer child, when the retained child is outer. -/
@[expose] def otherOuterChild (k : Fin 3) : Fin 3 := if k = 0 then 2 else 0

theorem otherOuterChild_ne_middle (k : Fin 3) : otherOuterChild k ≠ 1 := by
  unfold otherOuterChild
  split <;> decide

theorem otherOuterChild_ne (k : Fin 3) (hk : k ≠ 1) : otherOuterChild k ≠ k := by
  fin_cases k <;> simp_all [otherOuterChild]

end WaveTurbulence.Mole
