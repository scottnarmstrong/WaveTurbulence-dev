/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Geo5
public import WaveTurbulence.Foundations.VineEst.ZpSurj.Sound3

/-! # ZP-SURJ: coherent objects carry the layerreg1 patterns; change of the parent layers -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
open TTree WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.LGSpine WaveTurbulence.ConjCoh WaveTurbulence.Stage1

variable {w : ℕ}

/-- **Lemma P (couples)**: a coherent couple carries the pattern at its parent layers. -/
theorem pattern_of_coherentCouple {p q q' : ℕ} {Q : RegCpl} {LQ : LayeredGarden 2}
    (h : IsCoherentCoupleAt p q q' Q LQ) :
    LayerPatternN LQ q q' Q ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)) := by
  obtain ⟨hwf, hQ, w', H, a, b, hcan, hemb, hsa, hsb, hcoh, hpa, hpb, hlay⟩ := h
  obtain ⟨hplain, -, hcrit⟩ := hcan
  have hpat := layerPattern_of_canon hcrit hplain hwf hemb hcoh
  rw [layerPattern_eq_N, hpa, hpb] at hpat
  have EQ := Embeds.of_decodes hQ
  have key : ∀ (i : Fin 2) (c : Fin w' × Path)
      (hiff : ∀ r, (addrExt c r).2 ∈ (H.garden.tree (addrExt c r).1).nodes ↔ r ∈ (LQ.garden.tree i).nodes)
      (hc : ∀ z : GNode LQ.garden.tree, z.1.1 = i → LQ.layer z = layerAt H (addrExt c z.1.2)) (r : Path),
      layerAt LQ (i, r) = layerAt H (addrExt c r) := by
    intro i c hiff hc r
    by_cases hr : r ∈ (LQ.garden.tree i).nodes
    · have := hc ⟨(i, r), hr⟩ rfl
      rw [← this]; exact layerAt_of_mem _ hr
    · have e1 : layerAt LQ (i, r) = 0 := by unfold layerAt; exact dif_neg hr
      have e2 : layerAt H (addrExt c r) = 0 := by
        unfold layerAt; exact dif_neg (fun hh => hr ((hiff r).1 hh))
      rw [e1, e2]
  refine (layerPatternN_reloc (H1 := H) (H2 := LQ) q q' Q a b hemb.indep ((0 : Fin 2), ([] : Path))
    ((1 : Fin 2), ([] : Path)) (fun r => ?_) (fun r => ?_)).2 hpat
  · refine key 0 a (fun r => ?_) (fun z hz => ?_) r
    · exact (node_iff_of_subtree hemb.nodeA hemb.treeA r).1.trans
        (node_iff_of_subtree EQ.nodeA EQ.treeA r).1.symm
    · have := hlay z; rwa [if_pos hz] at this
  · refine key 1 b (fun r => ?_) (fun z hz => ?_) r
    · exact (node_iff_of_subtree hemb.nodeB hemb.treeB r).1.trans
        (node_iff_of_subtree EQ.nodeB EQ.treeB r).1.symm
    · have := hlay z
      have hz' : ¬ z.1.1 = 0 := by rw [hz]; decide
      rwa [if_neg hz'] at this

/-- **Lemma P (trees)**. -/
theorem pattern_of_coherentTree {p q q' : ℕ} {X : RegChain} {LX : LayeredGarden 1}
    (h : IsCoherentTreeAt p q q' X LX) :
    TreePatternN LX q X (LX.garden.sig 0) ((0 : Fin 1), ([] : Path)) := by
  obtain ⟨hwf, hX, w', H, a, t, hcan, hemb, hsa, hcoh, hpa, hlone, hlay⟩ := h
  obtain ⟨hplain, -, hcrit⟩ := hcan
  have hpat := treePattern_of_canon hcrit hplain hwf hemb hcoh
  rw [treePattern_eq_N, hpa] at hpat
  have hT0 : LX.garden.tree 0 = X.plug (LX.garden.sig 0) .leaf := hX.1
  refine (treePatternN_native (H := H) (a := a) (X := X) (ζ := LX.garden.sig 0) (LX := LX) q (fun r hr => ?_)).1 hpat
  have hr' : r ∈ (LX.garden.tree 0).nodes := by rw [hT0]; exact hr
  have := hlay ⟨((0 : Fin 1), r), hr'⟩
  rw [← this]; exact (layerAt_of_mem _ hr').symm

theorem layerAt_le_root {w' : ℕ} (L : LayeredGarden w') (j : Fin w') (r : Path) :
    layerAt L (j, r) ≤ layerAt L (j, []) := by
  by_cases hr : r ∈ (L.garden.tree j).nodes
  · have h0 : ([] : Path) ∈ (L.garden.tree j).nodes := TTree.nil_mem_nodes _
    rw [layerAt_of_mem L hr, layerAt_of_mem L h0]
    exact L.layer_le_of_isDesc (a := ⟨(j, []), h0⟩) (c := ⟨(j, r), hr⟩) ⟨rfl, List.nil_prefix⟩
  · unfold layerAt; rw [dif_neg hr]; exact Nat.zero_le _

/-- **Lemma M (couples)**: the pattern at the parent layers `(pa, pb)` is the pattern at `(pa', pb')` when the minimum is
unchanged and the roots lie below the new parent layers. -/
theorem layerPatternN_change {LQ : LayeredGarden 2} {pa pb pa' pb' : ℕ} {Q : RegCpl}
    (h : LayerPatternN LQ pa pb Q ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)))
    (hmin : min pa' pb' = min pa pb) (ha : layerAt LQ ((0 : Fin 2), ([] : Path)) ≤ pa')
    (hb : layerAt LQ ((1 : Fin 2), ([] : Path)) ≤ pb') :
    LayerPatternN LQ pa' pb' Q ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)) := by
  obtain ⟨hc, h2⟩ := h
  refine ⟨hc, ?_⟩
  cases Q with
  | triv => intro z hz; rw [hmin]; exact h2 z hz
  | type1 c Q₁ Q₂ Q₃ => intro z hz; rw [hmin]; exact h2 z hz
  | type2 Xp Xm Qlp =>
    obtain ⟨c1, c2, c3, c4, c5⟩ := h2
    refine ⟨fun z hz => by rw [hmin]; exact c1 z hz, c2, c3, fun z hz => ?_, fun z hz => ?_⟩
    · refine ⟨hmin ▸ (c4 z hz).1, ?_⟩
      obtain ⟨r, -, rfl⟩ := chainNodesSet_node Xp 1 _ z hz
      exact (layerAt_le_root LQ 0 r).trans ha
    · refine ⟨hmin ▸ (c5 z hz).1, ?_⟩
      obtain ⟨r, -, rfl⟩ := chainNodesSet_node Xm (-1) _ z hz
      exact (layerAt_le_root LQ 1 r).trans hb

/-- **Lemma M (trees)**. -/
theorem treePatternN_change {LX : LayeredGarden 1} {pa pa' : ℕ} {X : RegChain} {ζ : ℤˣ}
    (h : TreePatternN LX pa X ζ ((0 : Fin 1), ([] : Path))) (ha : layerAt LX ((0 : Fin 1), ([] : Path)) ≤ pa') :
    TreePatternN LX pa' X ζ ((0 : Fin 1), ([] : Path)) := by
  obtain ⟨hc, hp, h3⟩ := h
  refine ⟨hc, hp, fun z hz => ⟨(h3 z hz).1, ?_⟩⟩
  obtain ⟨r, -, rfl⟩ := chainNodesSet_node X ζ _ z hz
  exact (layerAt_le_root LX 0 r).trans ha

end WaveTurbulence.ZpSurj
