/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.NodeSums
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionLeafOrder
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflateNodeEquations
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionDataCount

/-! # Exact total order of a literal reconstruction -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.inflateNode_branch_order {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree) :
    (D.inflateNode hS b.toNode).order =
      (D.tree b).size + 1 + ∑ i : Fin 3, (D.inflateNode hS (b.child i)).order := by
  rw [D.inflateNode_branch,code_plug_order]
  simp only [node3,TTree.order,Fin.sum_univ_three]
  omega

theorem ReconstructionData.forest_order {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) :
    (∑ j, (D.forest hS j).order) = S.order + D.size := by
  classical
  let f : GNode S.tree → ℕ := fun a => (D.inflateNode hS a).order
  have hn := sum_nodes_leaf_branch S.tree f
  have hr := sum_nodes_root_child S.tree f
  have hb : (∑ b : GBranch S.tree, f b.toNode) =
      (∑ b : GBranch S.tree, (D.tree b).size) + S.order +
        ∑ b : GBranch S.tree, ∑ i : Fin 3, f (b.child i) := by
    have he := Finset.sum_congr (s₁ := Finset.univ) rfl
      (fun b _ => D.inflateNode_branch_order hS b)
    change (∑ b : GBranch S.tree, f b.toNode) = _ at he
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      smul_eq_mul,mul_one,Comb.card_gbranch] at he
    exact he
  have hl : (∑ ℓ : GLeaf S.tree, f ℓ.toNode) = ∑ p : SourcePair S, (D.couple p).size := by
    have he := D.sum_leafTree_order hS
    simpa only [f,D.inflateNode_leaf] using he
  change (∑ j, f (GNode.root S.tree j)) = _
  change (∑ j, f (GNode.root S.tree j)) = S.order +
    ((∑ b : GBranch S.tree, (D.tree b).size) + ∑ p : SourcePair S, (D.couple p).size)
  omega

theorem ReconstructionData.decoded_order {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G) :
    G.order = S.order + D.size := by
  have ht := congrArg Raw.tree hd.2
  change D.forest hS = G.tree at ht
  change (∑ j, (G.tree j).order) = _
  rw [← ht]
  exact D.forest_order hS

end WaveTurbulence.Reg.Skeleton
