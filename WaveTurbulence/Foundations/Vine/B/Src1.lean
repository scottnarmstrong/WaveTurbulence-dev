/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Hdata
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
import Mathlib.Tactic

/-!
# VINE-B Part II (1): the hinge darts of the unit momenta (G3)

For a plain garden `G` and a set of hinges, a node that is a hinge or a child of a hinge carries the momentum of a
hinge dart (`bondIndex`), or equals a root value (`src_root`).  For the unit `j` of a `SpliceShape`, the four nodes
`hmom j i` are the hinge `u1` and the three crown children of the hinge.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents WaveTurbulence.LGSpine

variable {w : ℕ}

/-- The hinge dart (or root) giving the momentum of a node that is a hinge or the child of a hinge. -/
theorem exists_src (G : Garden w) (hS : G.IsPlain) (hinges : Finset (GBranch G.tree)) (y : GNode G.tree)
    (hy : (∃ c ∈ hinges, c.toNode = y) ∨ ∃ c ∈ hinges, ∃ k, c.child k = y) :
    ∃ s : HingeDarts G hinges ⊕ Fin w,
      (∀ x, s = Sum.inl x → ∀ (d : ℕ) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0),
        bondIndex G z.1 x.1 = z.1 y) ∧
      (∀ r, s = Sum.inr r → ∀ (d : ℕ) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0),
        z.1 y = roots r) := by
  by_cases hr : y.1.2 = []
  · refine ⟨Sum.inr y.1.1, by simp, fun r h d roots z => ?_⟩
    have hr' : r = y.1.1 := (Sum.inr.inj h).symm
    have hy' : y = GNode.root G.tree y.1.1 := Subtype.ext (Prod.ext rfl hr)
    rw [hr', hy']
    exact z.2.2.1 _
  · rcases (TTree.mem_nodes_iff _ _).mp y.2 with h | h
    · -- a leaf
      set ℓ : GLeaf G.tree := ⟨y.1, h⟩ with hℓ
      have hyl : ℓ.toNode = y := rfl
      by_cases hp : (G.pair ℓ).1.2 = []
      · refine ⟨Sum.inr (G.pair ℓ).1.1, by simp, fun r hrr d roots z => ?_⟩
        have hr' : r = (G.pair ℓ).1.1 := (Sum.inr.inj hrr).symm
        have h1 : z.1 y = z.1 (G.pair ℓ).toNode := by
          rw [← hyl]; exact z.2.1.2 ℓ
        have h2 : (G.pair ℓ).toNode = GNode.root G.tree (G.pair ℓ).1.1 :=
          Subtype.ext (Prod.ext rfl hp)
        rw [h1, h2, hr']
        exact z.2.2.1 _
      · refine ⟨Sum.inl ⟨.inr ⟨ℓ, hS ℓ, hr, hp⟩, ?_⟩, fun x hx d roots z => ?_, by simp⟩
        · left
          rcases hy with ⟨c, hc, hce⟩ | ⟨c, hc, k, hce⟩
          · exact (SpliceShape.leaf_ne_branch (hyl.trans hce.symm)).elim
          · have : GNode.parent ℓ.toNode hr = c := by
              have e : ℓ.toNode = c.child k := hyl.trans hce.symm
              have := parent_child c k (child_nonroot c k)
              rw [← this]
              congr 1
            show GNode.parent ℓ.toNode hr ∈ hinges
            rw [this]; exact hc
        · have := Sum.inl.inj hx
          subst this
          rfl
    · -- a branch
      set cb : GBranch G.tree := ⟨y.1, h⟩ with hcb
      have hyb : cb.toNode = y := rfl
      refine ⟨Sum.inl ⟨.inl (⟨cb, hr⟩, true), ?_⟩, fun x hx d roots z => ?_, by simp⟩
      · rcases hy with ⟨c, hc, hce⟩ | ⟨c, hc, k, hce⟩
        · right
          have : cb = c := by
            apply Subtype.ext
            exact congrArg (fun x : GNode G.tree => x.1) (hyb.trans hce.symm)
          show cb ∈ hinges
          rw [this]; exact hc
        · left
          have : GNode.parent cb.toNode hr = c := by
            have e : cb.toNode = c.child k := hyb.trans hce.symm
            have := parent_child c k (child_nonroot c k)
            rw [← this]
            congr 1
          show GNode.parent cb.toNode hr ∈ hinges
          rw [this]; exact hc
      · have := Sum.inl.inj hx
        subst this
        exact congrArg z.1 hyb

end WaveTurbulence.VineB
