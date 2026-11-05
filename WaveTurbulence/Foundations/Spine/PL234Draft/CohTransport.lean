/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.CoupleInduction

/-!
# The coherence facts of an embedded coherent couple, on its decoded carrier

`cohFacts_of_coherent`: for a coherent embedded type-2 couple with parent layers `q ≥ q'` (TARGET L901,
`IsCoherentCoupleAt`), LAYERREG's `layerreg1_type2` in the ambient canonical garden gives the facts `CohFacts` on
the decoded carrier, transported along the root embedding `z ↦ (a or b) · z.2` (`Embeds.treeA/treeB`: the decoded
trees are the ambient subtrees, so the node sets correspond).
-/

@[expose] public section

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-- The root embedding of a decoded couple carrier into the ambient garden. -/
def rootEmb {w : ℕ} (a b : Fin w × Path) (z : Fin 2 × Path) : Fin w × Path :=
  if z.1 = 0 then addrExt a z.2 else addrExt b z.2

theorem rootEmb_hom {w : ℕ} (a b : Fin w × Path) (z : Fin 2 × Path) (p : Path) :
    rootEmb a b (addrExt z p) = addrExt (rootEmb a b z) p := by
  have e : (addrExt z p).1 = z.1 := rfl
  unfold rootEmb
  rw [e]
  split_ifs <;> simp [addrExt, List.append_assoc]

theorem rootEmb_zero {w : ℕ} (a b : Fin w × Path) : rootEmb a b ((0 : Fin 2), []) = a := by
  simp [rootEmb, addrExt]

theorem rootEmb_one {w : ℕ} (a b : Fin w × Path) : rootEmb a b ((1 : Fin 2), []) = b := by
  simp [rootEmb, addrExt]

/-- **The layers of the decoded carrier** are the ambient layers along the root embedding, at every address. -/
theorem layerAt_rootEmb {w : ℕ} {Q : RegCpl} {LG : LayeredGarden 2} {HH : LayeredGarden w}
    {a b : Fin w × Path} (hQ : Q.Decodes LG.garden) (hE : Embeds HH.garden Q a b)
    (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt HH (addrExt (if z.1.1 = 0 then a else b) z.1.2))
    (z : Fin 2 × Path) : layerAt LG z = layerAt HH (rootEmb a b z) := by
  have hnodes : (rootEmb a b z).2 ∈ (HH.garden.tree (rootEmb a b z).1).nodes ↔
      z.2 ∈ (LG.garden.tree z.1).nodes := by
    obtain ⟨j, q⟩ := z
    by_cases hj : j = 0
    · subst hj
      have e : rootEmb a b ((0 : Fin 2), q) = addrExt a q := by simp [rootEmb]
      rw [e, (node_iff_of_subtree hE.nodeA hE.treeA q).1]
      show q ∈ Q.trees.1.nodes ↔ q ∈ (LG.garden.tree 0).nodes
      rw [hQ.2.1]
    · have hj1 : j = 1 := by
        fin_cases j
        · exact absurd rfl hj
        · rfl
      subst hj1
      have e : rootEmb a b ((1 : Fin 2), q) = addrExt b q := by simp [rootEmb]
      rw [e, (node_iff_of_subtree hE.nodeB hE.treeB q).1]
      show q ∈ Q.trees.2.nodes ↔ q ∈ (LG.garden.tree 1).nodes
      rw [hQ.2.2.1]
  by_cases hz : z.2 ∈ (LG.garden.tree z.1).nodes
  · calc layerAt LG z = LG.layer ⟨z, hz⟩ := layerAt_node LG ⟨z, hz⟩
      _ = layerAt HH (addrExt (if z.1 = 0 then a else b) z.2) := hlay ⟨z, hz⟩
      _ = layerAt HH (rootEmb a b z) := by
          unfold rootEmb
          split_ifs <;> rfl
  · unfold layerAt
    rw [dite_eq_right_of_eq_false (eq_false hz),
      dite_eq_right_of_eq_false (eq_false (fun h => hz (hnodes.mp h)))]

/-- **The coherence facts** of a coherent embedded type-2 couple with parent layers `q ≥ q'`. -/
theorem cohFacts_of_coherent {p q q' : ℕ} {Xp Xm : RegChain} {Qlp : RegCpl} {LG : LayeredGarden 2}
    (hqq : q' ≤ q) (hqp : q ≤ p) (h : IsCoherentCoupleAt p q q' (.type2 Xp Xm Qlp) LG) :
    CohFacts LG Xp Xm Qlp q' p := by
  obtain ⟨hwf, hQ, w, HH, a, b, hcan, hE, -, -, hcoh, hpa, hpb, hlay⟩ := h
  obtain ⟨hL, hPLp, -, hXp, hXm⟩ := layerreg1_type2 hcan.2.2 hcan.1 hwf hE hcoh
  have hmin : min (parAt HH p a) (parAt HH p b) = q' := by rw [hpa, hpb]; exact min_eq_right hqq
  rw [hmin] at hL hXp hXm
  rw [hpa] at hXp
  rw [hpb] at hXm
  have hf := rootEmb_hom a b
  have hlf := layerAt_rootEmb hQ hE hlay
  obtain ⟨Cp, -, -⟩ := hE.type2
  have hmapX : chainNodesSet Xp 1 a = (chainNodesSet Xp 1 ((0 : Fin 2), [])).image (rootEmb a b) := by
    have := chainNodesSet_map Xp (rootEmb a b) hf 1 ((0 : Fin 2), [])
    rwa [rootEmb_zero] at this
  have hmapM : chainNodesSet Xm (-1) b = (chainNodesSet Xm (-1) ((1 : Fin 2), [])).image (rootEmb a b) := by
    have := chainNodesSet_map Xm (rootEmb a b) hf (-1) ((1 : Fin 2), [])
    rwa [rootEmb_one] at this
  refine ⟨hwf, (Embeds.of_decodes hQ).type2.1, ?_, ?_, ?_, ?_, ?_, ?_, le_trans hqq hqp⟩
  · refine chainPairLayers_map HH LG (rootEmb a b) hf hlf Xp 1 _ ?_
    rw [rootEmb_zero]
    exact hPLp
  · refine spineMono_map HH LG (rootEmb a b) hf hlf Xp _ ?_
    rw [rootEmb_zero]
    exact spineMono_of_chainEmb Cp
  · intro z hz
    rw [hlf]
    have hz' : rootEmb a b z ∈ chainNodesSet Xp 1 a := by
      rw [hmapX]
      exact Finset.mem_image_of_mem _ hz
    exact (hXp _ hz').1
  · intro z hz
    rw [hlf]
    have hz' : rootEmb a b z ∈ chainNodesSet Xp 1 a := by
      rw [hmapX]
      exact Finset.mem_image_of_mem _ hz
    exact (hXp _ hz').2.trans hqp
  · intro z hz
    rw [hlf]
    have hz' : rootEmb a b z ∈ chainNodesSet Xm (-1) b := by
      rw [hmapM]
      exact Finset.mem_image_of_mem _ hz
    exact le_antisymm (hXm _ hz').2 (hXm _ hz').1
  · intro z hz
    rw [hlf]
    apply hL
    have e1 : rootEmb a b ((0 : Fin 2), Xp.lonePath) = addrExt a Xp.lonePath := by simp [rootEmb]
    have e2 : rootEmb a b ((1 : Fin 2), Xm.lonePath) = addrExt b Xm.lonePath := by simp [rootEmb]
    have hmapL := cplNodes_map Qlp (rootEmb a b) hf ((0 : Fin 2), Xp.lonePath) ((1 : Fin 2), Xm.lonePath)
    rw [e1, e2] at hmapL
    rw [hmapL]
    exact Finset.mem_image_of_mem _ hz

end WaveTurbulence.PL234
