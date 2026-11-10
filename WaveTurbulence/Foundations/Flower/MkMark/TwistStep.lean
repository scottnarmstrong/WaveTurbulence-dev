/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.StepProt
public import WaveTurbulence.Foundations.Flower.MkMark.LFTwistCoord
public import WaveTurbulence.Foundations.Molecule.CoreBranchSigns

/-! # B2b MK-MARK: one unit LF twist transports `Π₀` (Lemma 2⁺(a), twist step)

`twistPair`: slot data of the actual unit twist. `noProt_of_near`: if no vertex of `Π₀` lies in the near region of
the lower joint `u₂` (an unmarked vine), then `Π₀` avoids the replaced region `own(u₂) ∪ own(u₂₃) ∪ own(u₀)`.
`twist_step_prot`: the `true` LF choice transports `Π₀` off the replaced regions. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Twist WaveTurbulence.LFTwist

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

theorem leaf_ne_branch {tree : Fin w → TTree} (l : GLeaf tree) (b : GBranch tree) : l.toNode ≠ b.toNode := by
  intro h
  have hv : l.1 = b.1 := congrArg Subtype.val h
  have hl := l.2
  rw [hv] at hl
  exact TTree.not_mem_branching_of_mem_leaves _ hl b.2

section Twist
variable {S : Garden w} (hS : S.IsPlain) (P : CorePlacement S) (D : ReconstructionData S)
  (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true)
  (hsame : (S.pair P.retained).1.1 = P.lower.1.1)

/-- Slot data of the actual unit twist. -/
def twistPair : PairData (twistCoord hS P D X Q hX hQ hsame) where
  νB := chosenBranchEquiv S P true
  hB b := (naiveNodeEquiv_branch S P b).symm
  νL := chosenLeafEquiv S P true
  hL l := (naiveNodeEquiv_leaf S P l).symm
  treeEq b hb := by
    change b.toNode ∉ replacedNodes P at hb
    rw [mem_replacedNodes, not_or, not_or] at hb
    have hbl : b ≠ P.lower := fun e => hb.1 (by rw [e])
    refine ⟨lfReconstructionChoice_tree_other S P hS D true X Q hX hQ b hbl, ?_⟩
    have := coreBranchEquiv_sign S P b
    rw [if_neg hbl] at this
    exact this
  leafEq l hl := by
    change l.toNode ∉ replacedNodes P at hl
    rw [mem_replacedNodes, not_or, not_or] at hl
    obtain ⟨h1, h2, h3⟩ := hl
    have hp : pairOfLeaf (chosenSkeleton S P true) (chosenSkeleton_plain S P hS true) (chosenLeafEquiv S P true l) =
        chosenPairEquiv S P hS true (pairOfLeaf S hS l) :=
      (sourcePairEquiv_pairOfLeaf hS (chosenSkeleton_plain S P hS true) _ _ l).symm
    refine ⟨?_, ?_, (chosenLeafEquiv_pair S P true l).symm⟩
    · rw [hp, lfReconstructionChoice_couple_other]
      intro he
      rcases VineAlign.pairOfLeaf_eq_cases hS l P.retained he with e | e
      · exact h2 (by rw [e])
      · exact h3 (by rw [e])
    · have hs := naiveNodeEquiv_sign_other S P l.toNode h1 h2 h3
      rw [naiveNodeEquiv_leaf] at hs
      exact hs
  rskPair l hl := by
    change l.toNode ∉ replacedNodes P at hl
    change (S.pair l).toNode ∉ replacedNodes P
    rw [mem_replacedNodes, not_or, not_or] at hl ⊢
    obtain ⟨-, h2, h3⟩ := hl
    refine ⟨leaf_ne_branch _ _, fun e => h3 ?_, fun e => h2 ?_⟩
    · have e' : S.pair l = P.retained := leaf_toNode_injective e
      rw [← e', S.pair_pair]
    · have e' : S.pair l = S.pair P.retained := leaf_toNode_injective e
      have := congrArg S.pair e'
      rw [S.pair_pair, S.pair_pair] at this
      rw [this]

theorem retained_tree : P.retained.1.1 = P.lower.1.1 := by
  have := congrArg (fun x : GNode S.tree => x.1.1) P.child
  exact this

theorem retained_nonroot' : P.retained.1.2 ≠ [] := by
  have := congrArg (fun x : GNode S.tree => x.1.2) P.child
  simp only [GBranch.child] at this
  show P.retained.toNode.1.2 ≠ []
  rw [this]
  simp

theorem replaced_nonroot : ∀ o ∈ replacedNodes P, o.1.2 ≠ [] := by
  intro o ho
  rw [mem_replacedNodes] at ho
  rcases ho with rfl | rfl | rfl
  · exact P.nonroot
  · exact retained_nonroot' P
  · exact P.paired_nonroot

include hsame in
theorem replaced_pairTree : ∀ l : GLeaf S.tree, l.toNode ∈ replacedNodes P → (S.pair l).1.1 = l.1.1 := by
  intro l hl
  rw [mem_replacedNodes] at hl
  rcases hl with h | h | h
  · exact absurd h (leaf_ne_branch _ _)
  · have e : l = P.retained := leaf_toNode_injective h
    subst e
    rw [hsame, retained_tree]
  · have e : l = S.pair P.retained := leaf_toNode_injective h
    subst e
    rw [S.pair_pair, hsame, retained_tree]

/-- No vertex of `Π₀` in the near region of the lower joint ⇒ `Π₀` avoids the replaced region. -/
theorem noProt_of_near {LG : LayeredGarden w} (hd : D.Decodes hS LG.garden) {J : Finset (Fin w)}
    {pat : Fin w → FixPat} (t s : ℝ)
    (hn : ∀ a ∈ protI0 LG J pat t s, a.1 ∉ nearRegion S D.tree P.lower) :
    NoProtIn LG J pat (ownedBy S D.tree (replacedNodes P)) := by
  intro z hz hp
  have hz' : owner S D.tree z ∈ replacedNodes P := hz
  have hmem : (⟨z, hp.1⟩ : GNode LG.garden.tree) ∈ protI0 LG J pat t s := (mem_protI0_iff_protAt pat t s _).mpr hp
  apply hn _ hmem
  rw [mem_nearRegion_iff]
  rw [mem_replacedNodes] at hz'
  rcases hz' with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨P.keep, h.trans P.child⟩)
  · refine Or.inr (Or.inr ⟨P.retained, ⟨retained_tree P, P.keep, ?_⟩, h⟩)
    have := congrArg (fun x : GNode S.tree => x.1.2) P.child
    exact this

/-- **One unit LF twist transports `Π₀`.** -/
theorem twist_step_prot {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden)
    (hd' : (lfReconstructionChoice S P hS D true X Q hX hQ).Decodes (chosenSkeleton_plain S P hS true) LG'.garden)
    {J : Finset (Fin w)} {pat : Fin w → FixPat} (t s : ℝ)
    (hn : ∀ a ∈ protI0 LG J pat t s, a.1 ∉ nearRegion S D.tree P.lower) :
    NoProtIn LG' J pat (ownedBy (chosenSkeleton S P true) (lfReconstructionChoice S P hS D true X Q hX hQ).tree
        (twistCoord hS P D X Q hX hQ hsame).Rsk') ∧
      ∀ z, NodeAt LG z → z ∉ ownedBy S D.tree (replacedNodes P) →
        (ProtAt LG' J pat ((twistCoord hS P D X Q hX hQ hsame).map z) ↔ ProtAt LG J pat z) := by
  set C := twistCoord hS P D X Q hX hQ hsame
  set E := twistPair hS P D X Q hX hQ hsame
  refine C.step_prot E hd hd' (replaced_nonroot P) (replaced_pairTree P hsame) ?_ ?_
    (noProt_of_near hS P D hd t s hn)
  · intro o ho
    have h := replaced_nonroot P _ ho
    exact fun h0 => h ((C.root (C.ν.symm o)).mp (by rw [Equiv.apply_symm_apply]; exact h0))
  · intro l' hl'
    set l := E.νL.symm l'
    have hl : l.toNode ∈ replacedNodes P := by
      have : C.ν.symm l'.toNode ∈ replacedNodes P := hl'
      rwa [show C.ν.symm l'.toNode = l.toNode by
        apply C.ν.injective
        rw [Equiv.apply_symm_apply, ← E.hL, Equiv.apply_symm_apply]] at this
    have e : l' = E.νL l := (Equiv.apply_symm_apply _ _).symm
    have hpr : (chosenSkeleton S P true).pair (E.νL l) = E.νL (S.pair l) :=
      (chosenLeafEquiv_pair S P true l).symm
    have htree : ∀ x : GLeaf S.tree, (E.νL x).1.1 = x.1.1 := fun x => by
      have := C.tree x.toNode
      rw [← E.hL] at this
      exact this
    rw [e, hpr, htree, htree]
    exact replaced_pairTree P hsame l hl

end Twist

end WaveTurbulence.Flower.MkMark
