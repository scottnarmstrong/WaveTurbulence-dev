/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairAtSides

/-! # Transport of actual oriented attachment slots through a leaf-pair bijection

No sign-preservation premise is needed: `pairOfLeaf` restores the source
positive/negative orientation, including the exceptional pair whose signs flip.
This is a code-reindexing operation. Geometric preservation of an unchanged
oriented couple additionally requires endpoint sign preservation; the
exceptional sign-flipped slot is erased to triv or replaced freely in LF.
-/

public section
namespace WaveTurbulence.LFTwist
open Reg.Skeleton
variable {w v : ℕ} {G : Garden w} {H : Garden v}

theorem pairOfLeaf_first_or_partner (G : Garden w) (hG : G.IsPlain) (l : GLeaf G.tree) :
    (pairOfLeaf G hG l).firstLeaf hG = l ∨
      (pairOfLeaf G hG l).firstLeaf hG = G.pair l := by
  by_cases hs : nodeSign G.sig l.1 = 1
  · exact Or.inl (pairOfLeaf_sides_pos G hG l hs).1
  · exact Or.inr (pairOfLeaf_sides_neg G hG l hs).1

/-- The actual attachment slot of the transported positive leaf. -/
@[expose] noncomputable def mapSourcePair (hG : G.IsPlain) (hH : H.IsPlain)
    (E : GLeaf G.tree ≃ GLeaf H.tree) (p : SourcePair G) : SourcePair H :=
  pairOfLeaf H hH (E (p.firstLeaf hG))

theorem mapSourcePair_leftInverse (hG : G.IsPlain) (hH : H.IsPlain)
    (E : GLeaf G.tree ≃ GLeaf H.tree)
    (hE : ∀ l, E (G.pair l) = H.pair (E l)) :
    Function.LeftInverse (mapSourcePair hH hG E.symm) (mapSourcePair hG hH E) := by
  intro p
  unfold mapSourcePair
  rcases pairOfLeaf_first_or_partner H hH (E (p.firstLeaf hG)) with h | h
  · rw [h, E.symm_apply_apply, pairOfLeaf_firstLeaf]
  · rw [h, ← hE, E.symm_apply_apply, pairOfLeaf_partner, pairOfLeaf_firstLeaf]

/-- Pair-preserving leaf equivalences induce exact bijections of oriented source slots. -/
@[expose] noncomputable def sourcePairEquiv (hG : G.IsPlain) (hH : H.IsPlain)
    (E : GLeaf G.tree ≃ GLeaf H.tree)
    (hE : ∀ l, E (G.pair l) = H.pair (E l)) : SourcePair G ≃ SourcePair H where
  toFun := mapSourcePair hG hH E
  invFun := mapSourcePair hH hG E.symm
  left_inv := mapSourcePair_leftInverse hG hH E hE
  right_inv := mapSourcePair_leftInverse hH hG E.symm (fun l => by
    apply E.injective
    rw [E.apply_symm_apply, hE, E.apply_symm_apply])

/-- The induced slot map follows either endpoint, independently of its orientation. -/
theorem sourcePairEquiv_pairOfLeaf (hG : G.IsPlain) (hH : H.IsPlain)
    (E : GLeaf G.tree ≃ GLeaf H.tree)
    (hE : ∀ l, E (G.pair l) = H.pair (E l)) (l : GLeaf G.tree) :
    sourcePairEquiv hG hH E hE (pairOfLeaf G hG l) = pairOfLeaf H hH (E l) := by
  change pairOfLeaf H hH (E ((pairOfLeaf G hG l).firstLeaf hG)) = _
  rcases pairOfLeaf_first_or_partner G hG l with he | he
  · rw [he]
  · rw [he, hE, pairOfLeaf_partner]

/-- Transport every attachment code along the actual branch and pair bijections. -/
@[expose] noncomputable def transportReconstruction (hG : G.IsPlain) (hH : H.IsPlain)
    (EB : GBranch G.tree ≃ GBranch H.tree) (EL : GLeaf G.tree ≃ GLeaf H.tree)
    (hE : ∀ l, EL (G.pair l) = H.pair (EL l)) (D : ReconstructionData G) :
    ReconstructionData H where
  tree := fun b => D.tree (EB.symm b)
  couple := fun p => D.couple ((sourcePairEquiv hG hH EL hE).symm p)
  tree_wf := fun b => D.tree_wf (EB.symm b)
  couple_wf := fun p => D.couple_wf ((sourcePairEquiv hG hH EL hE).symm p)

theorem transportReconstruction_tree (hG : G.IsPlain) (hH : H.IsPlain)
    (EB : GBranch G.tree ≃ GBranch H.tree) (EL : GLeaf G.tree ≃ GLeaf H.tree)
    (hE : ∀ l, EL (G.pair l) = H.pair (EL l)) (D : ReconstructionData G) (b : GBranch G.tree) :
    (transportReconstruction hG hH EB EL hE D).tree (EB b) = D.tree b := by
  simp only [transportReconstruction, EB.symm_apply_apply]

theorem transportReconstruction_couple (hG : G.IsPlain) (hH : H.IsPlain)
    (EB : GBranch G.tree ≃ GBranch H.tree) (EL : GLeaf G.tree ≃ GLeaf H.tree)
    (hE : ∀ l, EL (G.pair l) = H.pair (EL l)) (D : ReconstructionData G) (p : SourcePair G) :
    (transportReconstruction hG hH EB EL hE D).couple (sourcePairEquiv hG hH EL hE p) = D.couple p := by
  simp only [transportReconstruction, Equiv.symm_apply_apply]

end WaveTurbulence.LFTwist
