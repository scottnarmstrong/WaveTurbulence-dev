/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.CoordIso
public import WaveTurbulence.Foundations.Molecule.LFTwist.ReconstructionChoice
public import WaveTurbulence.Foundations.Molecule.TwistChildLabels
public import WaveTurbulence.Foundations.Molecule.TwistDecorationRoots
public import WaveTurbulence.Foundations.Molecule.LFTwist.CutNodeEquiv
public import WaveTurbulence.Foundations.Molecule.LFTwist.CutSignedValues
public import WaveTurbulence.Foundations.Molecule.TwistExcludedSubtree
public import WaveTurbulence.Foundations.Molecule.CLBranchRealization
public import WaveTurbulence.Foundations.Vine.Align.SurvivingSlots

/-! # B2b MK-MARK: skeleton coordinates across a unit LF twist

For a core placement `P` of the skeleton `S` (lower joint `u₂ = P.lower`, retained leaf `u₂₃ = P.retained`, its
partner `u₀`), the replaced skeleton nodes are `Rsk = {u₂, u₂₃, u₀}` (`replacedNodes`). The actual unit twist
(`chosenSkeleton S P true = unitTwistGarden S P`) with reconstruction data `lfReconstructionChoice … true X Q` and
the naive node bijection `naiveNodeEquiv` form a `CoordData` (`twistCoord`): off `Rsk` the local trees, holes,
ordered children and parents are transported (main's `naiveNodeEquiv_*`, `lfReconstructionChoice_*_other`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Twist WaveTurbulence.LFTwist

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

section Twist
variable {S : Garden w} (P : CorePlacement S)

/-- The replaced skeleton nodes of an LF operation at `P`: `u₂`, `u₂₃`, `u₀`. -/
def replacedNodes : Set (GNode S.tree) := {P.lower.toNode, P.retained.toNode, (S.pair P.retained).toNode}

/-- `u₀` lies in the tree of `u₂` (the realization of a core (CL) vine lies in one tree). -/
theorem pair_retained_tree {Xv : VineType} {A : Finset (GBranch S.tree)} {a : GBranch S.tree}
    (hcore : IsCoreCLVine S Xv A a P.lower) (hP : IsPlacementAt S A P.lower P) :
    (S.pair P.retained).1.1 = P.lower.1.1 := by
  have hB := hcore.1.1
  have hCL := hcore.2.1
  have hr := placement_pair_in_realization S P hB hP
  have h1 := (Mole.cl_leaf_realization_iff S hB hCL _).mp ((Mole.leaf_incidence_realization_iff S A _).mp hr)
  have h2 := (Mole.cl_branch_realization_iff S hB hCL P.lower).mp hB.2.2.1
  exact h1.1.1.symm.trans h2.1.1

theorem exchangeAddress_fst (hsame : (S.pair P.retained).1.1 = P.lower.1.1) (a : Address w) :
    (exchangeAddress P.lower.1 (S.pair P.retained).1 P.keep a).1 = a.1 := by
  unfold exchangeAddress
  split_ifs with h1 h2
  · exact hsame.trans h1.1.symm
  · rw [h2]
    exact hsame.symm
  · rfl

theorem exchangeAddress_fixed (a : Address w) (h1 : ¬ (a.1 = P.lower.1.1 ∧ P.lower.1.2 <+: a.2))
    (h2 : a ≠ (S.pair P.retained).1) : exchangeAddress P.lower.1 (S.pair P.retained).1 P.keep a = a := by
  unfold exchangeAddress
  rw [if_neg h1, if_neg h2]

theorem exchangeAddress_lower : exchangeAddress P.lower.1 (S.pair P.retained).1 P.keep P.lower.1 =
    (S.pair P.retained).1 := by
  unfold exchangeAddress
  rw [if_pos ⟨rfl, List.prefix_refl _⟩]
  simp [switchPath]

theorem exchangeAddress_paired : exchangeAddress P.lower.1 (S.pair P.retained).1 P.keep (S.pair P.retained).1 =
    P.lower.1 := by
  unfold exchangeAddress
  rw [if_neg (fun h => P.paired_outside ⟨h.1.symm, h.2⟩), if_pos rfl]

theorem naive_lower_val : (naiveNodeEquiv S P P.lower.toNode).1 = (S.pair P.retained).1 := by
  rw [naiveNodeEquiv_address]
  exact exchangeAddress_lower P

theorem naive_paired_val : (naiveNodeEquiv S P (S.pair P.retained).toNode).1 = P.lower.1 := by
  rw [naiveNodeEquiv_address]
  exact exchangeAddress_paired P

theorem coreBranch_fixed (b : GBranch S.tree) (hn : ¬ (b.1.1 = P.lower.1.1 ∧ P.lower.1.2 <+: b.1.2)) :
    (coreBranchEquiv S P b).1 = b.1 := by
  rw [coreBranchEquiv_address]
  apply exchangeAddress_fixed P _ hn
  intro e
  have hl := (S.pair P.retained).2
  rw [← e] at hl
  exact TTree.not_mem_branching_of_mem_leaves _ hl b.2

end Twist

theorem holeOf_leaf {S : Garden w} (D : ReconstructionData S) (l : GLeaf S.tree) : holeOf D l.toNode = none := by
  unfold holeOf
  exact dif_neg (TTree.not_mem_branching_of_mem_leaves _ l.2)

theorem mem_replacedNodes {S : Garden w} (P : CorePlacement S) (o : GNode S.tree) :
    o ∈ replacedNodes P ↔ o = P.lower.toNode ∨ o = P.retained.toNode ∨ o = (S.pair P.retained).toNode := by
  simp [replacedNodes]

section TwistCoord
variable {S : Garden w} (hS : S.IsPlain) (P : CorePlacement S) (D : ReconstructionData S)
  (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true)

/-- **The coordinate data of the actual unit twist** (the `true` choice of an LF operation). -/
def twistCoord (hsame : (S.pair P.retained).1.1 = P.lower.1.1) :
    CoordData D hS (lfReconstructionChoice S P hS D true X Q hX hQ) (chosenSkeleton_plain S P hS true) where
  ν := naiveNodeEquiv S P
  Rsk := replacedNodes P
  Rsk' := {x | (naiveNodeEquiv S P).symm x ∈ replacedNodes P}
  tree o := by
    show (naiveNodeEquiv S P o).1.1 = o.1.1
    rw [naiveNodeEquiv_address]
    exact exchangeAddress_fst P hsame o.1
  root o := by
    have := naiveNodeEquiv_nonroot S P o
    show (naiveNodeEquiv S P o).1.2 = [] ↔ o.1.2 = []
    constructor
    · intro h
      by_contra hn
      exact (this.mpr hn) h
    · intro h
      by_contra hn
      exact (this.mp hn) h
  rsk o := by
    show (naiveNodeEquiv S P).symm (naiveNodeEquiv S P o) ∈ replacedNodes P ↔ o ∈ replacedNodes P
    rw [Equiv.symm_apply_apply]
  loc o ho := by
    rw [mem_replacedNodes, not_or, not_or] at ho
    obtain ⟨h1, h2, h3⟩ := ho
    rcases (TTree.mem_nodes_iff _ _).mp o.2 with hl | hb
    · let l : GLeaf S.tree := ⟨o.1, hl⟩
      have hlo : l.toNode = o := rfl
      have hs := naiveNodeEquiv_sign_other S P o h1 h2 h3
      rw [← hlo, naiveNodeEquiv_leaf] at hs
      show localTree _ _ (naiveNodeEquiv S P o) = _
      rw [← hlo, naiveNodeEquiv_leaf, localTree_leaf]
      refine (localTree_leaf (lfReconstructionChoice S P hS D true X Q hX hQ) (chosenSkeleton_plain S P hS true)
        (chosenLeafEquiv S P true l)).trans ?_
      unfold ReconstructionData.leafTree
      have hp : pairOfLeaf (chosenSkeleton S P true) (chosenSkeleton_plain S P hS true) (chosenLeafEquiv S P true l) =
          chosenPairEquiv S P hS true (pairOfLeaf S hS l) :=
        (sourcePairEquiv_pairOfLeaf hS (chosenSkeleton_plain S P hS true) _ _ l).symm
      rw [hp, lfReconstructionChoice_couple_other]
      · congr 1
      · intro he
        rcases VineAlign.pairOfLeaf_eq_cases hS l P.retained he with e | e
        · exact h2 (by rw [← hlo, e])
        · exact h3 (by rw [← hlo, e])
    · let b : GBranch S.tree := ⟨o.1, hb⟩
      have hbo : b.toNode = o := rfl
      have hs := naiveNodeEquiv_sign_other S P o h1 h2 h3
      rw [← hbo, naiveNodeEquiv_branch] at hs
      show localTree _ _ (naiveNodeEquiv S P o) = _
      rw [← hbo, naiveNodeEquiv_branch, localTree_branch]
      refine (localTree_branch (lfReconstructionChoice S P hS D true X Q hX hQ) (chosenSkeleton_plain S P hS true)
        (chosenBranchEquiv S P true b)).trans ?_
      have ht := lfReconstructionChoice_tree_other S P hS D true X Q hX hQ b (fun e => h1 (by rw [← hbo, e]))
      rw [ht]
      congr 1
  hole o ho := by
    have ho' := ho
    rw [mem_replacedNodes, not_or, not_or] at ho
    obtain ⟨h1, -, -⟩ := ho
    rcases (TTree.mem_nodes_iff _ _).mp o.2 with hl | hb
    · let l : GLeaf S.tree := ⟨o.1, hl⟩
      have hlo : l.toNode = o := rfl
      show holeOf _ (naiveNodeEquiv S P o) = _
      rw [← hlo, naiveNodeEquiv_leaf, holeOf_leaf]
      exact holeOf_leaf (lfReconstructionChoice S P hS D true X Q hX hQ) (chosenLeafEquiv S P true l)
    · let b : GBranch S.tree := ⟨o.1, hb⟩
      have hbo : b.toNode = o := rfl
      show holeOf _ (naiveNodeEquiv S P o) = _
      rw [← hbo, naiveNodeEquiv_branch, holeOf_branch]
      refine (holeOf_branch (lfReconstructionChoice S P hS D true X Q hX hQ) (chosenBranchEquiv S P true b)).trans ?_
      have ht := lfReconstructionChoice_tree_other S P hS D true X Q hX hQ b (fun e => h1 (by rw [← hbo, e]))
      rw [ht]
  child b b' hb hbb i := by
    have hbb' : b' = coreBranchEquiv S P b := by
      apply Subtype.ext
      have h1 : b'.1 = (naiveNodeEquiv S P b.toNode).1 := congrArg Subtype.val hbb
      have h2 : (naiveNodeEquiv S P b.toNode).1 = (coreBranchEquiv S P b).1 :=
        congrArg Subtype.val (naiveNodeEquiv_branch S P b)
      exact h1.trans h2
    subst hbb'
    rw [mem_replacedNodes, not_or, not_or] at hb
    obtain ⟨hb1, -, hb3⟩ := hb
    have hbval : b.1 ≠ P.lower.1 := fun e => hb1 (congrArg GBranch.toNode (Subtype.ext e))
    by_cases hc : b.child i ∈ replacedNodes P
    · refine ⟨⟨fun _ => ?_, fun _ => hc⟩, fun h => absurd hc h⟩
      show (naiveNodeEquiv S P).symm ((coreBranchEquiv S P b).child i) ∈ replacedNodes P
      rw [mem_replacedNodes] at hc
      rcases hc with hc | hc | hc
      · have hn : ¬ (b.1.1 = P.lower.1.1 ∧ P.lower.1.2 <+: b.1.2) := by
          rintro ⟨-, e2⟩
          have hl := congrArg (fun x : GNode S.tree => x.1.2.length) hc
          have := e2.length_le
          simp [GBranch.child, GBranch.toNode] at hl
          omega
        have e : (coreBranchEquiv S P b).child i = naiveNodeEquiv S P (S.pair P.retained).toNode := by
          apply Subtype.ext
          show ((coreBranchEquiv S P b).1.1, (coreBranchEquiv S P b).1.2 ++ [i]) = _
          rw [coreBranch_fixed P b hn, naive_paired_val]
          exact congrArg Subtype.val hc
        rw [e, Equiv.symm_apply_apply, mem_replacedNodes]
        exact Or.inr (Or.inr rfl)
      · exfalso
        have e := hc.trans P.child
        have hv := congrArg Subtype.val e
        simp only [GBranch.child, Prod.mk.injEq] at hv
        exact hbval (Prod.ext hv.1 (List.append_inj' hv.2 rfl).1)
      · have hn : ¬ (b.1.1 = P.lower.1.1 ∧ P.lower.1.2 <+: b.1.2) := by
          rintro ⟨e1, e2⟩
          apply P.paired_outside
          have hv : ((b.1.1, b.1.2 ++ [i]) : Address w) = (S.pair P.retained).1 := congrArg Subtype.val hc
          refine ⟨?_, ?_⟩
          · show P.lower.1.1 = (S.pair P.retained).1.1
            rw [← hv]
            exact e1.symm
          · show P.lower.1.2 <+: (S.pair P.retained).1.2
            rw [← hv]
            exact e2.trans (List.prefix_append _ _)
        have e : (coreBranchEquiv S P b).child i = naiveNodeEquiv S P P.lower.toNode := by
          apply Subtype.ext
          show ((coreBranchEquiv S P b).1.1, (coreBranchEquiv S P b).1.2 ++ [i]) = _
          rw [coreBranch_fixed P b hn, naive_lower_val]
          exact congrArg Subtype.val hc
        rw [e, Equiv.symm_apply_apply, mem_replacedNodes]
        exact Or.inl rfl
    · have hc' := hc
      rw [mem_replacedNodes, not_or, not_or] at hc'
      have hn := naiveNodeEquiv_child S P (p := b) (n := b.child i) (i := i) rfl hc'.1 hc'.2.2
      have hslot : exchangeChildSlot P.lower.1 P.keep b.1 i = i := by
        unfold exchangeChildSlot
        rw [if_neg hbval]
      rw [hslot] at hn
      refine ⟨?_, fun _ => hn⟩
      show b.child i ∈ replacedNodes P ↔ (naiveNodeEquiv S P).symm ((coreBranchEquiv S P b).child i) ∈ replacedNodes P
      rw [← hn, Equiv.symm_apply_apply]
  parent o h h' ho := by
    rw [mem_replacedNodes, not_or, not_or] at ho
    obtain ⟨h1, -, h3⟩ := ho
    have hp := naiveNodeEquiv_parent S P o h h1 h3
    have e : ((naiveNodeEquiv S P o).parent h').toNode = naiveNodeEquiv S P (o.parent h).toNode := by
      rw [naiveNodeEquiv_branch, ← hp]
      rfl
    show _ ↔ (naiveNodeEquiv S P).symm ((naiveNodeEquiv S P o).parent h').toNode ∈ replacedNodes P
    rw [e, Equiv.symm_apply_apply]

end TwistCoord

end WaveTurbulence.Flower.MkMark
