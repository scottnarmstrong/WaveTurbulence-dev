/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Pin2
import Mathlib.Tactic

/-!
# K2: native pins between a canonical layered garden and its two-exception normalization
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ} {S : Garden w}

/-- Pins from `LG` to its normalization (core, other trees, other couples). -/
theorem k2_normalized {p : ℕ} {kind : Bool} (LG : LayeredGarden w) (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS LG.garden) (b0 : GBranch S.tree) (q0 : SourcePair S)
    (hc : CanonicalObject p kind LG)
    (ht : CohOn LG ((D.tree b0).linksAt (nodeSign S.sig b0.1) (inflatedPosition S D.tree b0.toNode))) :
    (∀ c, layerAt LG (D.corePosition c) =
      layerAt (normalizedLayered LG D hS hd b0 q0 p) ((normalizedData D b0 q0).corePosition c)) ∧
    (∀ c, c ≠ b0 → ∀ r ∈ ((D.tree c).plug (nodeSign S.sig c.1) .leaf).nodes,
      layerAt LG (addrExt (inflatedPosition S D.tree c.toNode) r) =
        layerAt (normalizedLayered LG D hS hd b0 q0 p)
          (addrExt (inflatedPosition S (normalizedData D b0 q0).tree c.toNode) r)) ∧
    (∀ q', q' ≠ q0 → ∀ (i : Fin 2) (r : Path),
      layerAt LG (addrExt (coupleRoot D hS q' i) r) =
        layerAt (normalizedLayered LG D hS hd b0 q0 p)
          (addrExt (coupleRoot (normalizedData D b0 q0) hS q' i) r)) := by
  classical
  by_cases hq : D.couple q0 = .triv
  · have hN : normalizedLayered LG D hS hd b0 q0 p =
        collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b0) := by
      simp only [normalizedLayered, hq, ite_true]
    rw [hN]
    have hf : (D.eraseTree b0).couple q0 = .triv := hq
    have he : normalizedData D b0 q0 = D.eraseTree b0 := (D.eraseTree b0).eraseCouple_eq_self q0 hf
    rw [he]
    exact ⟨te1_core LG D hS hd b0, fun c hc' r hr => te1_tree LG D hS hd b0 c hc' r hr,
      fun q' _ i r => te1_couple LG D hS hd b0 q' i r⟩
  · have hN : normalizedLayered LG D hS hd b0 q0 p =
        collapseCoupleLayered (collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b0))
          ((D.eraseTree b0).decoded_couple_isSubCouple hS (eraseTree_collapse_decodes D hS hd b0) q0) p := by
      simp only [normalizedLayered, hq, ite_false]
    rw [hN]
    have hcan := hc.eraseTree_coherent LG D hS hd b0 ht
    have hA := collapseCouple_outAgree
      (collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b0))
      ((D.eraseTree b0).decoded_couple_isSubCouple hS (eraseTree_collapse_decodes D hS hd b0) q0) p
      hcan.criterion hcan.plain
    refine ⟨fun c => (te1_core LG D hS hd b0 c).trans (ce1_core (D.eraseTree b0) hS q0 hA c),
      fun c hc' r hr => (te1_tree LG D hS hd b0 c hc' r hr).trans ?_,
      fun q' hq' i r => (te1_couple LG D hS hd b0 q' i r).trans (ce1_couple (D.eraseTree b0) hS q0 hA q' hq' i r)⟩
    exact ce1_tree (D.eraseTree b0) hS q0 hA c r (by rw [D.eraseTree_other b0 c hc']; exact hr)

end WaveTurbulence.Stage1
