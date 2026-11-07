/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepUG11
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG7
import Mathlib.Tactic

/-!
# S2 REPRESENTS, G1 (4): layer indices of the clocks of a unit on `G_sb`

For the layer `lay = (stSt S σ).layer (coreLayer …)` of `G_sb` (`lay c = layer (core (ob c))`):
* `lay_hinge`: the layer of the hinge of unit `j` is `layer (core (blk j).upper)` (= `qOut 0`);
* `lay_branch_child`: for a branch lower child `c` of the hinge (`nodeClk (hmom j k) = inr c`, `k ∈ {2, 3}`) the layer
  `lay c` is `layer (core ⟨(bnodes (blk j) k).1, _⟩)`, the layer of the core of the skeleton branch carrying that node.
  This is the exact value of `qOut` (for a branch child) in the R74 box (`outNode` = the core).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf

variable {w : ℕ} {S : Garden w}

/-- B1b (Mk-general form of `lay_hinge`). -/
theorem lay_hingeMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (j : Fin (unitBlocks (Mk := Mk) S σ).length)
    (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) :
    (stSt (Mk := Mk) S σ).layer (RegRed.coreLayer (layeredReconstruction D hS layer hLayer) D hS (D.garden_decodes hS))
        ((stShape (Mk := Mk) hM σ).hinge (unitBlkMk_disj (Mk := Mk) hM σ) j) =
      layer (D.coreBranch hS (unitBlkMk (Mk := Mk) hM σ j).upper).toNode := by
  have h := (stShape (Mk := Mk) hM σ).br_hinge (unitBlkMk_disj (Mk := Mk) hM σ) j
  have h' : (stSt (Mk := Mk) S σ).M.ob ((stShape (Mk := Mk) hM σ).hinge (unitBlkMk_disj (Mk := Mk) hM σ) j) = (unitBlkMk (Mk := Mk) hM σ j).upper := h
  show layer (D.coreBranch hS ((stSt (Mk := Mk) S σ).M.ob ((stShape (Mk := Mk) hM σ).hinge (unitBlkMk_disj (Mk := Mk) hM σ) j))).toNode = _
  rw [h']

theorem lay_hinge (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks S σ).length)
    (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) :
    (stSt S σ).layer (RegRed.coreLayer (layeredReconstruction D hS layer hLayer) D hS (D.garden_decodes hS))
        ((stShape hM σ).hinge (unitBlk_disj hM σ) j) =
      layer (D.coreBranch hS (unitBlk hM σ j).upper).toNode := lay_hingeMk (Mk := ∅) hM σ j D hS layer hLayer

/-- B1b (Mk-general form of `lay_branch_child`). -/
theorem lay_branch_childMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (j : Fin (unitBlocks (Mk := Mk) S σ).length)
    (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (k : Fin 4) (c : GBranch (stSt (Mk := Mk) S σ).G.tree)
    (hc : nodeClk (stSt (Mk := Mk) S σ).G ((stShape (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j k) = Sum.inr c) :
    ∃ hb : (bnodes (unitBlkMk (Mk := Mk) hM σ j) k).1.2 ∈ (S.tree (bnodes (unitBlkMk (Mk := Mk) hM σ j) k).1.1).branching,
      (stSt (Mk := Mk) S σ).layer (RegRed.coreLayer (layeredReconstruction D hS layer hLayer) D hS (D.garden_decodes hS)) c =
        layer (D.coreBranch hS ⟨(bnodes (unitBlkMk (Mk := Mk) hM σ j) k).1, hb⟩).toNode := by
  have hcn : c.toNode = (stShape (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j k := by
    unfold nodeClk at hc
    by_cases h : ((stShape (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j k).1.2 ∈
        ((stSt (Mk := Mk) S σ).G.tree ((stShape (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j k).1.1).branching
    · rw [dif_pos h] at hc
      have := Sum.inr.inj hc
      subst this
      rfl
    · rw [dif_neg h] at hc
      exact absurd hc (by simp)
  have hnode : ((stShape (Mk := Mk) hM σ).br c).toNode = bnodes (unitBlkMk (Mk := Mk) hM σ j) k := by
    rw [(stShape (Mk := Mk) hM σ).br_node, hcn]
    exact (stShape (Mk := Mk) hM σ).node_hmom (unitBlkMk_disj (Mk := Mk) hM σ) j k
  have hb : (bnodes (unitBlkMk (Mk := Mk) hM σ j) k).1.2 ∈ (S.tree (bnodes (unitBlkMk (Mk := Mk) hM σ j) k).1.1).branching := by
    rw [← hnode]; exact ((stShape (Mk := Mk) hM σ).br c).2
  refine ⟨hb, ?_⟩
  have hbr : (stShape (Mk := Mk) hM σ).br c = ⟨(bnodes (unitBlkMk (Mk := Mk) hM σ j) k).1, hb⟩ := by
    apply WaveTurbulence.Mole.branch_toNode_injective
    rw [hnode]
    rfl
  have hob : (stSt (Mk := Mk) S σ).M.ob c = ⟨(bnodes (unitBlkMk (Mk := Mk) hM σ j) k).1, hb⟩ := hbr
  show layer (D.coreBranch hS ((stSt (Mk := Mk) S σ).M.ob c)).toNode = _
  rw [hob]

theorem lay_branch_child (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks S σ).length)
    (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (k : Fin 4) (c : GBranch (stSt S σ).G.tree)
    (hc : nodeClk (stSt S σ).G ((stShape hM σ).hmom (unitBlk_disj hM σ) j k) = Sum.inr c) :
    ∃ hb : (bnodes (unitBlk hM σ j) k).1.2 ∈ (S.tree (bnodes (unitBlk hM σ j) k).1.1).branching,
      (stSt S σ).layer (RegRed.coreLayer (layeredReconstruction D hS layer hLayer) D hS (D.garden_decodes hS)) c =
        layer (D.coreBranch hS ⟨(bnodes (unitBlk hM σ j) k).1, hb⟩).toNode := lay_branch_childMk (Mk := ∅) hM σ j D hS layer hLayer k c hc

/-- The core layer is monotone along the unit: every atom of the unit has core layer at most that of its upper joint. -/
theorem layer_core_le_upper (u : CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) :
    ∀ v ∈ u.atoms, layer (D.coreBranch hS v).toNode ≤ layer (D.coreBranch hS u.upper).toNode := by
  have hpre := LFTwist.inducedPrelayer_isBranchPrelayering (layeredReconstruction D hS layer hLayer) D hS
    (D.garden_decodes hS)
  suffices key : ∀ n : ℕ, ∀ v : GBranch S.tree, v.1.2.length = n → v ∈ u.atoms →
      layer (D.coreBranch hS v).toNode ≤ layer (D.coreBranch hS u.upper).toNode from
    fun v hv => key _ v rfl hv
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn hv
    by_cases hup : v = u.upper
    · rw [hup]
    · obtain ⟨hnr, hp⟩ := real_parent u ((branch_real_iff u v).mpr hv) (fun h => hup (WaveTurbulence.Mole.branch_toNode_injective h))
      obtain ⟨i, hi⟩ := VineB.child_parent v.toNode hnr
      have hlen : (v.toNode.parent hnr).1.2.length < n := by
        rw [← hn]
        simp only [GNode.parent, GBranch.toNode, List.length_dropLast]
        have : v.1.2.length ≠ 0 := fun h0 => hnr (List.length_eq_zero_iff.mp h0)
        omega
      have h1 := ih _ hlen (v.toNode.parent hnr) rfl hp
      have h2 := hpre (v.toNode.parent hnr) v i hi.symm
      exact le_trans h2 h1

/-- A boundary node of a unit whose `G_sb` clock is a root time is not a branch of the skeleton. -/
theorem not_branch_of_nodeClk_inl (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks S σ).length)
    (k : Fin 4) (r : Fin w)
    (hc : nodeClk (stSt S σ).G ((stShape hM σ).hmom (unitBlk_disj hM σ) j k) = Sum.inl r) :
    (bnodes (unitBlk hM σ j) k).1.2 ∉ (S.tree (bnodes (unitBlk hM σ j) k).1.1).branching := by
  intro h
  set b' : GBranch S.tree := ⟨(bnodes (unitBlk hM σ j) k).1, h⟩ with hb'
  have hbn : b'.toNode = bnodes (unitBlk hM σ j) k := rfl
  have hr : Ret (unitBlk hM σ) b'.toNode := by
    rw [hbn]; exact (stShape hM σ).ret_bdryNode (unitBlk_disj hM σ) j k
  obtain ⟨c, hcb⟩ := (stShape hM σ).exists_br hr
  have h1 : (stShape hM σ).node c.toNode = (stShape hM σ).node ((stShape hM σ).hmom (unitBlk_disj hM σ) j k) := by
    rw [← (stShape hM σ).br_node, hcb, hbn, (stShape hM σ).node_hmom]
  have h2 := (stShape hM σ).inj h1
  rw [← h2] at hc
  have hcc : nodeClk (stSt S σ).G c.toNode = Sum.inr c := by
    unfold nodeClk
    rw [dif_pos (show c.toNode.1.2 ∈ ((stSt S σ).G.tree c.toNode.1.1).branching from c.2)]
    rfl
  rw [hcc] at hc
  exact absurd hc (by simp)

end WaveTurbulence.Represents
