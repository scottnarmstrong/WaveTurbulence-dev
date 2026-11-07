/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Construct4

/-! # ZP-SURJ: existence of the LF construction (assembly) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.Stage1

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
variable {Q : RegCpl} {X : RegChain} {LQ : LayeredGarden 2} {LX : LayeredGarden 1}

theorem oat_nil {LM LH : LayeredGarden w} {a n' : Address w}
    (h : OutAgreeT LM LH a a n') : OutAgreeT LM LH a (addrExt a RegChain.nil.lonePath) n' := by
  rw [show addrExt a RegChain.nil.lonePath = a from addrExt_nil a]; exact h

/-- The construction of an exceptional datum: reinsert the couple, then the tree. -/
@[expose] noncomputable def construction (hD : ExcDatum s ε Q X LQ LX)
    (hcnt : ∀ (t : TTree) (hEO : ChainEmb (midG hD).garden .nil (srcSign s ε) (tA s ε) t)
      (hEN : ChainEmb ((s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε)) X (srcSign s ε) (tA s ε) t)
      (hOutT : GOutT (midG hD).garden ((s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε)) (tA s ε)
        (addrExt (tA s ε) X.lonePath)),
      rawTreeLayerCount LG s.data s.plain p s.placement.lower +
        rawCoupleLayerCount LG s.data s.plain p s.exceptional =
      rawTreeLayerCount (outG hD t hEO hEN hOutT) (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε) p
        (s.branches ε s.placement.lower) +
      rawCoupleLayerCount (outG hD t hEO hEN hOutT) (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε) p
        (s.pairs ε s.exceptional)) :
    LFConstruction s ε := by
  let t := Classical.choose (exc_tree_side (s := s) (ε := ε) Q hD.hQ X hD.hX)
  have hEO := (Classical.choose_spec (exc_tree_side (s := s) (ε := ε) Q hD.hQ X hD.hX)).1
  have hEN := (Classical.choose_spec (exc_tree_side (s := s) (ε := ε) Q hD.hQ X hD.hX)).2.1
  have hOutT := (Classical.choose_spec (exc_tree_side (s := s) (ε := ε) Q hD.hQ X hD.hX)).2.2
  let mid := midG hD
  let out := outG hD t hEO hEN hOutT
  have hA := graftC_outAgree (exc_embM (s := s) (ε := ε) Q hD.hQ).indep exc_embB (exc_embM Q hD.hQ)
    (exc_gout Q hD.hQ) hD.dQ hD.rootA hD.rootB
  have hT := graftT_outAgree (LM := mid) (M' := (s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε)) hEO hEN
    hD.hEX hOutT hD.lone' hD.root'
  have hT' := oat_nil hT
  have hpins := pins_of_records s ε (k2_pins s ε) (hplug_of s ε) X Q hD.hX hD.hQ mid out
    ((s.midData ε Q hD.hQ).garden_decodes _) ((s.finalData ε X Q hD.hX hD.hQ).garden_decodes _) hA hEO hT'
  refine {
    newTree := X
    newCouple := Q
    tree_wf := hD.hX
    couple_wf := hD.hQ
    midLayer := mid.layer
    mid_isLayering := mid.isLayering
    outLayer := out.layer
    out_isLayering := out.isLayering
    tail := t
    coupleInsertion := ?_
    treeInsertion := ?_
    coreLayers := hpins.1
    ordinaryTreeLayers := hpins.2.1
    ordinaryCoupleLayers := hpins.2.2
    combinedOrder := hD.size
    combinedTopCount := hcnt t hEO hEN hOutT }
  · rw [coupleRoot_zero, coupleRoot_one]
    refine ⟨hD.hQ, ?_, ?_, ?_, exc_embB, exc_embM Q hD.hQ, hA, ?_⟩
    · rw [base_garden_eq s ε]; rfl
    · change nodeSign (s.base ε).garden.sig (cA s ε) = 1
      exact ((s.baseData ε).decodedNode_sign (s.chosen_plain ε) (s.base_decodes ε)
        ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).toNode).trans
        (sourcePair_first_sign _ (s.chosen_plain ε) _)
    · change nodeSign (s.base ε).garden.sig (cB s ε) = -1
      exact ((s.baseData ε).decodedNode_sign (s.chosen_plain ε) (s.base_decodes ε)
        ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).toNode).trans
        (sourcePair_second_sign _ (s.chosen_plain ε) _)
    · refine (graftC_pattern_iff (exc_embM (s := s) (ε := ε) Q hD.hQ).indep exc_embB (exc_embM Q hD.hQ)
        (exc_gout Q hD.hQ) hD.dQ hD.rootA hD.rootB).2 ?_
      rw [graftC_parAt_a, graftC_parAt_b]
      exact hD.patQ
  · refine ⟨hD.hX, rfl, ?_, hEO, hEN, hT', ?_⟩
    · exact ((s.midData ε Q hD.hQ).decodedNode_sign (s.chosen_plain ε) ((s.midData ε Q hD.hQ).garden_decodes _)
        (s.branches ε s.placement.lower).toNode)
    · refine (graftT_pattern_iff (LM := mid) (M' := (s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε)) hEO hEN
        hD.hEX hOutT hD.lone' hD.root').2 ?_
      have h1 := graftT_parAt (LM := mid) (M' := (s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε)) (p := p)
        hEO hEN hD.hEX hOutT hD.lone' hD.root'
      rw [h1, midG_parAt_tA]
      exact hD.patX

end WaveTurbulence.ZpSurj
