/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BoundaryGeometry
public import WaveTurbulence.Foundations.Molecule.JointChildSlots
import Mathlib.Tactic

/-! # The three actual retained CL boundary roots
TARGET `block_clcn` (2): these roots are extracted from the proved
joint slots, not supplied by a splicing or isomorphism hypothesis.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {G : Garden w}

@[expose] def clBaseBoundary (a b : GBranch G.tree) (excluded kept : Fin 3) : Fin 3 → GNode G.tree :=
  ![a.child excluded,b.child 1,b.child (otherOuterChild kept)]

@[expose] noncomputable def clBaseBoundaryRoots {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b)
    (excluded kept : Fin 3) (he : excluded.succ ∉ internalPositions G S a) :
    SpliceBoundaryRoots G a where
  node := clBaseBoundary a b excluded kept
  below := by
    intro i
    have hab := (cl_parent_strict_descendant G hB hCL).1
    fin_cases i
    · exact ⟨rfl,List.prefix_append _ _⟩
    · exact ⟨hab.1,hab.2.trans (List.prefix_append _ _)⟩
    · exact ⟨hab.1,hab.2.trans (List.prefix_append _ _)⟩
  incomparable := by
    have h01 := upper_excluded_lower_child_incomparable G hB hCL excluded 1 he
    have h02 := upper_excluded_lower_child_incomparable G hB hCL excluded (otherOuterChild kept) he
    have h12 := different_children_incomparable G b 1 (otherOuterChild kept)
      (otherOuterChild_ne_middle kept).symm
    intro i j hn
    fin_cases i <;> fin_cases j
    · exact (hn rfl).elim
    · exact h01
    · exact h02
    · exact ⟨h01.2,h01.1⟩
    · exact (hn rfl).elim
    · exact h12
    · exact ⟨h02.2,h02.1⟩
    · exact ⟨h12.2,h12.1⟩
    · exact (hn rfl).elim

/-- Slot permutation: keep the upper excluded child in its original
outer slot and put the other two subtrees in the slots fixed by signs. -/
@[expose] def clBoundarySelector (excluded : Fin 3) (sameSign : Bool) (i : Fin 3) : Fin 3 :=
  if i = excluded then 0 else if i = 1 then (if sameSign then 1 else 2) else (if sameSign then 2 else 1)

theorem clBoundarySelector_bijective : ∀ excluded : Fin 3, excluded ≠ 1 → ∀ sameSign : Bool,
    Function.Bijective (clBoundarySelector excluded sameSign) := by decide

@[expose] noncomputable def reindexSpliceBoundary {a : GBranch G.tree}
    (B : SpliceBoundaryRoots G a) (p : Fin 3 ≃ Fin 3) : SpliceBoundaryRoots G a where
  node i := B.node (p i)
  below i := B.below (p i)
  incomparable i j hn := B.incomparable (p i) (p j) (fun he => hn (p.injective he))

@[expose] def clSameSign (a b : GBranch G.tree) : Bool :=
  decide (G.sign a.toNode = G.sign b.toNode)

@[expose] noncomputable def clSignedBoundaryRoots {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b)
    (excluded kept : Fin 3) (he : excluded.succ ∉ internalPositions G S a) (he1 : excluded ≠ 1) :
    SpliceBoundaryRoots G a := by
  classical
  exact reindexSpliceBoundary (clBaseBoundaryRoots hB hCL excluded kept he)
    (Equiv.ofBijective (clBoundarySelector excluded (clSameSign a b))
      (clBoundarySelector_bijective excluded he1 _))

theorem child_sign_formula (v : GBranch G.tree) (i : Fin 3) :
    G.sign (v.child i) = if i = 1 then -G.sign v.toNode else G.sign v.toNode := by
  fin_cases i <;> simp [Garden.sign,nodeSign,TTree.pathSign,GBranch.child,GBranch.toNode,
    List.count_append,pow_succ]

end WaveTurbulence.Mole
