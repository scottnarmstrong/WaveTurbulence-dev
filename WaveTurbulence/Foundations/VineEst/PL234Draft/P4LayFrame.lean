/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4LayGarden

/-!
# Labelled codes are coherent

The frame (`P4Frame`) of the labelled decoded couple `lcLG` carries the `layerreg1` pattern. Its proof is the
decoded-coordinate pattern transported forward along `frameIota`. So the frame is canonical (`frame_canon`), and:

* **`coherent_lc`**: `IsCoherentCoupleAt p q q' (type2 Xp Xm Qlp) (lcLG Xp Xm Qlp ls q q')`;
* **`coherent_low`**: a code not of type 2 is coherent at `(p, q, q')` with the constant layering `q'`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

section Couple

variable {Xp : RegChain} (Xm : RegChain) (Qlp : RegCpl) {ls : List ℕ} {p q q' : ℕ}
  (h : LabOK q' Xp ls q ∧ q' ≤ q) (hqp : q ≤ p)

theorem lc_decodes : (RegCpl.type2 Xp Xm Qlp).Decodes (lcLG Xp Xm Qlp ls q q').garden := by
  rw [lcLG_garden]
  exact decodedCouple_decodes _

include h

theorem lc_chain (z : Fin 2 × Path) (hz : z ∈ chainNodesSet Xp 1 ((0 : Fin 2), [])) :
    layerAt (lcLG Xp Xm Qlp ls q q') z = chainLay Xp ls q' ((0 : Fin 2), []) z := by
  rw [layerAt_lcLG h (lc_node (mem_cplNodes_type2.2 (Or.inl hz))), lcLayer_chain (chainNodes_region Xp 1 _ z hz).1]

theorem lc_minus (z : Fin 2 × Path) (hz : z ∈ chainNodesSet Xm (-1) ((1 : Fin 2), [])) :
    layerAt (lcLG Xp Xm Qlp ls q q') z = q' := by
  rw [layerAt_lcLG h (lc_node (mem_cplNodes_type2.2 (Or.inr (Or.inl hz)))),
    lcLayer_low (Or.inr (chainNodes_region Xm (-1) _ z hz).1)]

theorem lc_lp (z : Fin 2 × Path)
    (hz : z ∈ cplNodes Qlp (addrExt ((0 : Fin 2), []) Xp.lonePath) (addrExt ((1 : Fin 2), []) Xm.lonePath)) :
    layerAt (lcLG Xp Xm Qlp ls q q') z = q' := by
  rw [layerAt_lcLG h (lc_node (mem_cplNodes_type2.2 (Or.inr (Or.inr hz)))),
    lcLayer_low ((cplNodes_region hz).imp id fun h => under_trans (under_ext _ _) h)]

theorem lc_coh (x : (Fin 2 × Path) × (Fin 2 × Path))
    (hx : x ∈ (RegCpl.type2 Xp Xm Qlp).linksAt ((0 : Fin 2), []) ((1 : Fin 2), [])) :
    layerAt (lcLG Xp Xm Qlp ls q q') x.1 = layerAt (lcLG Xp Xm Qlp ls q q') x.2 := by
  rw [layerAt_lcLG h (lc_node (Finset.mem_union_left _ (mem_pairEndpoints_fst hx))),
    layerAt_lcLG h (lc_node (Finset.mem_union_left _ (mem_pairEndpoints_snd hx)))]
  exact lc_links Xp Xm Qlp ls x hx

theorem lc_rootA : layerAt (lcLG Xp Xm Qlp ls q q') ((0 : Fin 2), []) ≤ q := by
  rw [layerAt_lcLG h (TTree.nil_mem_nodes _), lcLayer_chain (under_refl _)]
  exact chainLay_le Xp ls q _ _ h.1 h.2

theorem lc_rootB : layerAt (lcLG Xp Xm Qlp ls q q') ((1 : Fin 2), []) ≤ q' := by
  rw [layerAt_lcLG h (TTree.nil_mem_nodes _), lcLayer_low (Or.inr (under_refl _))]

include hqp

/-- **The frame of a labelled couple.** -/
noncomputable abbrev lcFrame : LayeredGarden 2 :=
  frameLayered (LQ := lcLG Xp Xm Qlp ls q q') (lc_decodes Xm Qlp) h.2 hqp (lc_rootA Xm Qlp h) (lc_rootB Xm Qlp h)

theorem lcFrame_iota (z : Fin 2 × Path) :
    layerAt (lcFrame Xm Qlp h hqp) (frameIota z) = layerAt (lcLG Xp Xm Qlp ls q q') z :=
  layerAt_frame_iota _ _ _ _ _ z

theorem lcFrame_parA : parAt (lcFrame Xm Qlp h hqp) p fA = q := frame_parAt_fA _ _ _ _ _

theorem lcFrame_parB : parAt (lcFrame Xm Qlp h hqp) p fB = q' := frame_parAt_fB _ _ _ _ _

theorem lcFrame_min : min (parAt (lcFrame Xm Qlp h hqp) p fA) (parAt (lcFrame Xm Qlp h hqp) p fB) = q' := by
  rw [lcFrame_parA, lcFrame_parB]
  exact min_eq_right h.2

theorem lcFrame_pattern : LayerPattern (lcFrame Xm Qlp h hqp) p (.type2 Xp Xm Qlp) fA fB := by
  have hlay : ∀ z, layerAt (lcLG Xp Xm Qlp ls q q') z = layerAt (lcFrame Xm Qlp h hqp) (frameIota z) :=
    fun z => (lcFrame_iota Xm Qlp h hqp z).symm
  have hA : ∀ s : Path, addrExt fA s = frameIota (addrExt ((0 : Fin 2), []) s) := fun s => rfl
  have hB : ∀ s : Path, addrExt fB s = frameIota (addrExt ((1 : Fin 2), []) s) := fun s => rfl
  have hmX : chainNodesSet Xp 1 fA = (chainNodesSet Xp 1 ((0 : Fin 2), [])).image frameIota := by
    rw [← frameIota_zero]
    exact chainNodesSet_map Xp frameIota frameIota_hom 1 ((0 : Fin 2), [])
  have hmM : chainNodesSet Xm (-1) fB = (chainNodesSet Xm (-1) ((1 : Fin 2), [])).image frameIota := by
    rw [← frameIota_one]
    exact chainNodesSet_map Xm frameIota frameIota_hom (-1) ((1 : Fin 2), [])
  have hmin := lcFrame_min Xm Qlp h hqp
  refine ⟨fun l hl => ?_, ?_⟩
  · rw [← frameIota_zero, ← frameIota_one, couple_linksAt_map _ frameIota frameIota_hom] at hl
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    rw [← hlay, ← hlay]
    exact lc_coh Xm Qlp h x hx
  · rw [hmin, lcFrame_parA, lcFrame_parB]
    refine ⟨fun z hz => ?_, ?_, ?_, fun z hz => ?_, fun z hz => ?_⟩
    · rw [hA, hB, cplNodes_map Qlp frameIota frameIota_hom] at hz
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hz
      rw [← hlay]
      exact lc_lp Xm Qlp h z' hz'
    · exact chainPairLayers_push _ _ frameIota frameIota_hom hlay Xp 1 ((0 : Fin 2), [])
        (chainPairLayers_of_lay Xp 1 ls _ (lc_chain Xm Qlp h))
    · exact chainPairLayers_push _ _ frameIota frameIota_hom hlay Xm (-1) ((1 : Fin 2), [])
        (chainPairLayers_of_const (c := q') _ _ _ (lc_minus Xm Qlp h))
    · rw [hmX] at hz
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hz
      rw [← hlay, lc_chain Xm Qlp h z' hz']
      exact ⟨le_chainLay Xp ls q _ _ h.1, chainLay_le Xp ls q _ _ h.1 h.2⟩
    · rw [hmM] at hz
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hz
      rw [← hlay, lc_minus Xm Qlp h z' hz']
      exact ⟨le_rfl, le_rfl⟩

/-- **A labelled type-2 couple is coherent at `(p, q, q')`.** -/
theorem coherent_lc (hwf : (RegCpl.type2 Xp Xm Qlp).wf = true) :
    IsCoherentCoupleAt p q q' (.type2 Xp Xm Qlp) (lcLG Xp Xm Qlp ls q q') := by
  refine ⟨hwf, lc_decodes Xm Qlp, 2, lcFrame Xm Qlp h hqp, fA, fB,
    frame_canon _ _ _ _ _ (lcFrame_pattern Xm Qlp h hqp), frame_embeds _, nodeSign_fA, nodeSign_fB,
    (lcFrame_pattern Xm Qlp h hqp).1, lcFrame_parA Xm Qlp h hqp, lcFrame_parB Xm Qlp h hqp, ?_⟩
  rintro ⟨⟨j, path⟩, hz⟩
  have e : addrExt (if j = 0 then fA else fB) path = frameIota (j, path) := by
    fin_cases j <;> rfl
  show _ = layerAt (lcFrame Xm Qlp h hqp) (addrExt (if j = 0 then fA else fB) path)
  rw [e, lcFrame_iota]
  exact (layerAt_node _ _).symm

end Couple

section Low

variable (Q : RegCpl) {p q q' : ℕ} (hqq : q' ≤ q) (hqp : q ≤ p)

/-- The frame of a constant layering `q'` with parent layers `(q, q')`. -/
noncomputable abbrev lowFrame : LayeredGarden 2 :=
  frameLayered (LQ := constLayered (decodedCouple Q) q') (decodedCouple_decodes Q) hqq hqp
    ((const_root_le Q 0).trans hqq) (const_root_le Q 1)

theorem lowFrame_layer (z : Fin 2 × Path) (hz : z ∈ cplNodes Q fA fB) : layerAt (lowFrame Q hqq hqp) z = q' := by
  rw [← frameIota_zero, ← frameIota_one, cplNodes_map Q frameIota frameIota_hom] at hz
  obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hz
  rw [show layerAt (lowFrame Q hqq hqp) (frameIota z') = layerAt (constLayered (decodedCouple Q) q') z' from
    layerAt_frame_iota _ _ _ _ _ z']
  exact layerAt_constLayered _ q' ((Embeds.of_decodes (decodedCouple_decodes Q)).mem_nodes hz')

include hqq hqp in
/-- **A code not of type 2, constantly in layer `q'`, is coherent at `(p, q, q')`.** -/
theorem coherent_low (hwf : Q.wf = true) (h2 : Q.isType2 = false) :
    IsCoherentCoupleAt p q q' Q (constLayered (decodedCouple Q) q') := by
  have hpA : parAt (lowFrame Q hqq hqp) p fA = q := frame_parAt_fA _ _ _ _ _
  have hpB : parAt (lowFrame Q hqq hqp) p fB = q' := frame_parAt_fB _ _ _ _ _
  have hmin : min (parAt (lowFrame Q hqq hqp) p fA) (parAt (lowFrame Q hqq hqp) p fB) = q' := by
    rw [hpA, hpB]
    exact min_eq_right hqq
  have hcoh : CohOn (lowFrame Q hqq hqp) (Q.linksAt fA fB) :=
    cohOn_of_const fun z hz => lowFrame_layer Q hqq hqp z (Finset.mem_union_left _ hz)
  have hP : LayerPattern (lowFrame Q hqq hqp) p Q fA fB := by
    cases Q with
    | triv => exact ⟨hcoh, fun z hz => (lowFrame_layer _ hqq hqp z hz).trans hmin.symm⟩
    | type1 c Q₁ Q₂ Q₃ => exact ⟨hcoh, fun z hz => (lowFrame_layer _ hqq hqp z hz).trans hmin.symm⟩
    | type2 Xp Xm Qlp => exact absurd h2 (by simp [RegCpl.isType2])
  refine ⟨hwf, decodedCouple_decodes Q, 2, lowFrame Q hqq hqp, fA, fB, frame_canon _ _ _ _ _ hP,
    frame_embeds Q, nodeSign_fA, nodeSign_fB, hcoh, hpA, hpB, ?_⟩
  rintro ⟨⟨j, path⟩, hz⟩
  have e : addrExt (if j = 0 then fA else fB) path = frameIota (j, path) := by
    fin_cases j <;> rfl
  show q' = layerAt (lowFrame Q hqq hqp) (addrExt (if j = 0 then fA else fB) path)
  rw [e, show layerAt (lowFrame Q hqq hqp) (frameIota (j, path)) =
    layerAt (constLayered (decodedCouple Q) q') (j, path) from layerAt_frame_iota _ _ _ _ _ _]
  exact (layerAt_constLayered _ q' hz).symm

end Low

end WaveTurbulence.PL234
