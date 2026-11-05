/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.NodeCoordinateRows
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ForgetTree
public import WaveTurbulence.Foundations.RegStruct.CodeOrders

/-! # The actual regular couple supplies the localization forest -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links
open TTree

/-- Select the actual positive member of the source leaf pair. -/
def positiveRepresentative {G : Garden 2} (hG : IsCouple G) (ℓ : GLeaf G.tree) : PlusLeaf G :=
  if h : ℓ ∈ plusLeaves G then ⟨ℓ,(mem_plusLeaves ℓ).mp h⟩ else
    ⟨G.pair ℓ,(mem_plusLeaves (G.pair ℓ)).mp ((pair_mem_plus_iff hG.1 ℓ).2 h)⟩

theorem sourceNodeRow_positiveRepresentative {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) (ℓ : GLeaf G.tree) :
    sourceNodeRow hQ ℓ.toNode = sourceNodeRow hQ (positiveRepresentative hG ℓ).val.toNode := by
  unfold positiveRepresentative
  split
  · rfl
  · exact sourceNodeRow_pair hQ ℓ

/-- Extend the actual node rows to all addresses, as the source itself does. -/
def forestNodeRow {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    (i : Fin 2) (p : Path) : LinkCoord Q → ℤ := fun c => extend (coordinateDecoration hQ c).val (i,p)

theorem forestNodeRow_node {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (a : GNode G.tree) :
    forestNodeRow hQ a.val.1 a.val.2 = sourceNodeRow hQ a := by
  funext c
  exact extend_node (coordinateDecoration hQ c).val a

/-- Every structural localization datum is constructed from the actual C2
carrier; no analytic estimate is supplied as a field. -/
def coupleMomentumData {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) :
    Incoh.MomentumTreeData Q.links.length (2*Q.links.length+1) 2 where
  tree i := localizationTree (G.tree i)
  order_eq := by
    simp only [localizationTree_order]
    change G.order = _
    rw [Reg.size_eq_order hQ]
    have hh := couple_linksAt_length Q ((0 : Fin 2),[]) (1,[])
    simpa only [RegCpl.links,Nat.mul_comm] using hh.symm
  nodeRow := forestNodeRow hQ
  inputRow a := sourceNodeRow hQ (plusLeafEquiv hQ hG a).val.toNode
  input_root_column a := sourceNodeRow_root_column hQ _
  leafInput i p := if h : p ∈ (G.tree i).leaves then
    some ((plusLeafEquiv hQ hG).symm (positiveRepresentative hG ⟨(i,p),h⟩)) else none
  root_row i := by
    rw [show forestNodeRow hQ i [] = sourceNodeRow hQ (GNode.root G.tree i) from forestNodeRow_node hQ (GNode.root G.tree i)]
    exact sourceNodeRow_root hQ i
  parent_row i p hp := by
    rw [localizationTree_branching] at hp
    let b : GBranch G.tree := ⟨(i,p),hp⟩
    funext c
    exact nodeRel_extend (coordinateDecoration hQ c).property.1 b
  leaf_row i p hp := by
    rw [localizationTree_leaves] at hp
    simp only [dite_eq_left hp,Equiv.apply_symm_apply]
    let ℓ : GLeaf G.tree := ⟨(i,p),hp⟩
    exact (forestNodeRow_node hQ ℓ.toNode).trans
      (sourceNodeRow_positiveRepresentative hQ hG ℓ)
  chosenTree j := (chosenNode Q j).1
  chosenPath j := (chosenNode Q j).2
  chosen_mem_nodes j := by
    rw [localizationTree_nodes]
    exact (chosenBranch hQ j).toNode.property
  child0_mem_nodes j := by
    rw [localizationTree_nodes]
    exact ((chosenBranch hQ j).child 0).property
  child2_mem_nodes j := by
    rw [localizationTree_nodes]
    exact ((chosenBranch hQ j).child 2).property
  link_x_row j := by
    funext c
    have hh := congrFun (linkCoords_coordinateDecoration hQ hG c) (some (j,0))
    change xv (extend (coordinateDecoration hQ c).val) (chosenNode Q j) = _ at hh
    simpa only [Pi.sub_apply,forestNodeRow,xv,addrExt,Incoh.momentumUnitRow,eq_comm] using hh
  link_y_row j := by
    funext c
    have hh := congrFun (linkCoords_coordinateDecoration hQ hG c) (some (j,1))
    change yv (extend (coordinateDecoration hQ c).val) (chosenNode Q j) = _ at hh
    simpa only [Pi.sub_apply,forestNodeRow,yv,addrExt,Incoh.momentumUnitRow,eq_comm] using hh

end WaveTurbulence.RegAsymp
