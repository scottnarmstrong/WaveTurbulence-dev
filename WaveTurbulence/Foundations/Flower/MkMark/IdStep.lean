/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.TwistStep

/-! # B2b MK-MARK: the `false` LF choice transports `Π₀`

With the `false` choice the skeleton is unchanged and only the regular tree at `u₂` and the regular couple at
`(u₂₃, u₀)` are replaced (`lfReconstructionChoice … false X Q`). The identity of skeleton nodes is a `CoordData`
(`idCoord`) with slot data (`idPair`), and `id_step_prot` transports `Π₀` off the replaced regions. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Twist WaveTurbulence.LFTwist

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

section Id
variable {S : Garden w} (hS : S.IsPlain) (P : CorePlacement S) (D : ReconstructionData S)
  (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true)

theorem id_tree_other (b : GBranch S.tree) (hb : b ≠ P.lower) :
    (lfReconstructionChoice S P hS D false X Q hX hQ).tree b = D.tree b :=
  lfReconstructionChoice_tree_other S P hS D false X Q hX hQ b hb

theorem id_couple_leaf (l : GLeaf S.tree) (h2 : l ≠ P.retained) (h3 : l ≠ S.pair P.retained) :
    (lfReconstructionChoice S P hS D false X Q hX hQ).couple
        (pairOfLeaf (chosenSkeleton S P false) (chosenSkeleton_plain S P hS false) l) =
      D.couple (pairOfLeaf S hS l) := by
  have hp : pairOfLeaf (chosenSkeleton S P false) (chosenSkeleton_plain S P hS false) (chosenLeafEquiv S P false l) =
      chosenPairEquiv S P hS false (pairOfLeaf S hS l) :=
    (sourcePairEquiv_pairOfLeaf hS (chosenSkeleton_plain S P hS false) _ _ l).symm
  refine (congrArg _ hp).trans ?_
  rw [lfReconstructionChoice_couple_other]
  intro he
  rcases VineAlign.pairOfLeaf_eq_cases hS l P.retained he with e | e
  · exact h2 e
  · exact h3 e

omit hS in
theorem replaced_pair_closed (l : GLeaf S.tree) (hl : l.toNode ∉ replacedNodes P) :
    (S.pair l).toNode ∉ replacedNodes P := by
  rw [mem_replacedNodes, not_or, not_or] at hl ⊢
  obtain ⟨-, h2, h3⟩ := hl
  refine ⟨leaf_ne_branch _ _, fun e => h3 ?_, fun e => h2 ?_⟩
  · have e' : S.pair l = P.retained := leaf_toNode_injective e
    rw [← e', S.pair_pair]
  · have e' : S.pair l = S.pair P.retained := leaf_toNode_injective e
    have := congrArg S.pair e'
    rw [S.pair_pair, S.pair_pair] at this
    rw [this]

/-- The identity coordinate data of the `false` LF choice. -/
def idCoord : CoordData D hS (lfReconstructionChoice S P hS D false X Q hX hQ) (chosenSkeleton_plain S P hS false) where
  ν := Equiv.refl (GNode S.tree)
  Rsk := replacedNodes P
  Rsk' := replacedNodes P
  tree _ := rfl
  root _ := Iff.rfl
  rsk _ := Iff.rfl
  loc o ho := by
    rw [mem_replacedNodes, not_or, not_or] at ho
    obtain ⟨h1, h2, h3⟩ := ho
    rcases (TTree.mem_nodes_iff _ _).mp o.2 with hl | hb
    · let l : GLeaf S.tree := ⟨o.1, hl⟩
      have hlo : l.toNode = o := rfl
      show localTree _ _ o = _
      rw [← hlo, localTree_leaf]
      refine (localTree_leaf (lfReconstructionChoice S P hS D false X Q hX hQ) (chosenSkeleton_plain S P hS false)
        l).trans ?_
      unfold ReconstructionData.leafTree
      rw [id_couple_leaf hS P D X Q hX hQ l (fun e => h2 (by rw [← hlo, e])) (fun e => h3 (by rw [← hlo, e]))]
      rfl
    · let b : GBranch S.tree := ⟨o.1, hb⟩
      have hbo : b.toNode = o := rfl
      show localTree _ _ o = _
      rw [← hbo, localTree_branch]
      refine (localTree_branch (lfReconstructionChoice S P hS D false X Q hX hQ) (chosenSkeleton_plain S P hS false)
        b).trans ?_
      rw [id_tree_other hS P D X Q hX hQ b (fun e => h1 (by rw [← hbo, e]))]
      rfl
  hole o ho := by
    rw [mem_replacedNodes, not_or, not_or] at ho
    obtain ⟨h1, -, -⟩ := ho
    rcases (TTree.mem_nodes_iff _ _).mp o.2 with hl | hb
    · let l : GLeaf S.tree := ⟨o.1, hl⟩
      have hlo : l.toNode = o := rfl
      show holeOf _ o = _
      rw [← hlo, holeOf_leaf]
      exact holeOf_leaf (lfReconstructionChoice S P hS D false X Q hX hQ) l
    · let b : GBranch S.tree := ⟨o.1, hb⟩
      have hbo : b.toNode = o := rfl
      show holeOf _ o = _
      rw [← hbo, holeOf_branch]
      refine (holeOf_branch (lfReconstructionChoice S P hS D false X Q hX hQ) b).trans ?_
      rw [id_tree_other hS P D X Q hX hQ b (fun e => h1 (by rw [← hbo, e]))]
  child b b' _ hbb i := by
    have e : b' = b := Subtype.ext (by exact congrArg (fun x : GNode S.tree => x.1) hbb)
    subst e
    exact ⟨Iff.rfl, fun _ => rfl⟩
  parent _ _ _ _ := Iff.rfl

/-- Slot data of the `false` LF choice. -/
def idPair : PairData (idCoord hS P D X Q hX hQ) where
  νB := Equiv.refl _
  hB _ := rfl
  νL := Equiv.refl _
  hL _ := rfl
  treeEq b hb := by
    change b.toNode ∉ replacedNodes P at hb
    rw [mem_replacedNodes, not_or, not_or] at hb
    exact ⟨id_tree_other hS P D X Q hX hQ b (fun e => hb.1 (by rw [e])), rfl⟩
  leafEq l hl := by
    change l.toNode ∉ replacedNodes P at hl
    rw [mem_replacedNodes, not_or, not_or] at hl
    obtain ⟨-, h2, h3⟩ := hl
    exact ⟨id_couple_leaf hS P D X Q hX hQ l (fun e => h2 (by rw [e])) (fun e => h3 (by rw [e])), rfl, rfl⟩
  rskPair l hl := replaced_pair_closed P l hl

end Id

end WaveTurbulence.Flower.MkMark
