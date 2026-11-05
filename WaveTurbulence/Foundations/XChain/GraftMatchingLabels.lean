/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftNodeLabels
/-! Exact node-label bijection with shared attachment-root labels, for arbitrary top trees. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

def GraftMatching {V : Type*} {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (x : (GNode top → V) × ((B : P.parts) → GNode (low B).tree → V)) : Prop :=
  ∀ B k, x.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode =
    x.2 B (GNode.root (low B).tree k)

noncomputable def graftAssembleLabels {V : Type*} {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (x : (GNode top → V) × ((B : P.parts) → GNode (low B).tree → V)) :
    GNode (graftForest top (blockGraftTrees top P low)) → V :=
  (graftNodeLabelsEquiv top P low).symm (fun b => x.1 b.toNode, x.2)

theorem graftAssembleLabels_lower {V : Type*} {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (x : (GNode top → V) × ((B : P.parts) → GNode (low B).tree → V))
    (B : P.parts) (a : GNode (low B).tree) :
    graftAssembleLabels top P low x (lowerNodeEmbedding top P low B a) = x.2 B a := by
  have he := congrArg (fun z => z.2 B a)
    ((graftNodeLabelsEquiv top P low).apply_symm_apply (fun b => x.1 b.toNode, x.2))
  exact he

theorem graftAssembleLabels_top_branch {V : Type*} {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (x : (GNode top → V) × ((B : P.parts) → GNode (low B).tree → V)) (a : GBranch top) :
    graftAssembleLabels top P low x (gardenNodeEquiv top P low (.inl a)) = x.1 a.toNode := by
  have he := congrArg (fun z => z.1 a)
    ((graftNodeLabelsEquiv top P low).apply_symm_apply (fun b => x.1 b.toNode, x.2))
  exact he

theorem graftAssembleLabels_top {V : Type*} {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (x : (GNode top → V) × ((B : P.parts) → GNode (low B).tree → V)) (hx : GraftMatching top P low x)
    (a : GNode top) :
    graftAssembleLabels top P low x (topNodeEmbedding top P low a) = x.1 a := by
  rcases (TTree.mem_nodes_iff _ _).mp a.2 with ha | ha
  · let l : GLeaf top := ⟨a.1, ha⟩
    have he := topNodeEmbedding_leaf top P low l
    have he' := congrArg (graftAssembleLabels top P low x) he
    have hm := hx (blockRootEquiv top P l).1 (blockRootEquiv top P l).2
    have hi := congrArg (fun l : GLeaf top => x.1 l.toNode)
      ((blockRootEquiv top P).symm_apply_apply l)
    exact he'.trans ((graftAssembleLabels_lower top P low x _ _).trans (hm.symm.trans hi))
  · let b : GBranch top := ⟨a.1, ha⟩
    exact (congrArg (graftAssembleLabels top P low x) (topNodeEmbedding_branch top P low b)).trans
      (graftAssembleLabels_top_branch top P low x b)

/-- Global labels are exactly a top label array and component label arrays that agree at every
attachment root. No tree family, truncation, pairing, layer or sign hypothesis is needed. -/
noncomputable def graftMatchingLabelsEquiv {V : Type*} {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    (GNode (graftForest top (blockGraftTrees top P low)) → V) ≃
      {x : (GNode top → V) × ((B : P.parts) → GNode (low B).tree → V) // GraftMatching top P low x} where
  toFun κ := ⟨(fun a => κ (topNodeEmbedding top P low a),
      fun B a => κ (lowerNodeEmbedding top P low B a)), fun B k =>
        congrArg κ (topNodeEmbedding_lower_root top P low B k)⟩
  invFun x := graftAssembleLabels top P low x.1
  left_inv κ := by
    funext a
    obtain ⟨z, rfl⟩ := (gardenNodeEquiv top P low).surjective a
    rcases z with b | ⟨B, a⟩
    · exact (graftAssembleLabels_top_branch top P low _ b).trans
        (congrArg κ (topNodeEmbedding_branch top P low b))
    · exact graftAssembleLabels_lower top P low _ B a
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext a
      exact graftAssembleLabels_top top P low x.1 x.2 a
    · funext B a
      exact graftAssembleLabels_lower top P low x.1 B a

end WaveTurbulence.Induct
