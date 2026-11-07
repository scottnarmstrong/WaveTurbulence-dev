/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Construct5
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Cls7Inj

/-! # ZP-SURJ: the native exceptional data of the constructed output -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.Stage1

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
variable {Q : RegCpl} {X : RegChain} {LQ : LayeredGarden 2} {LX : LayeredGarden 1}

section Native
variable (hD : ExcDatum s ε Q X LQ LX) (t : TTree)
  (hEO : ChainEmb (midG hD).garden .nil (srcSign s ε) (tA s ε) t)
  (hEN : ChainEmb ((s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε)) X (srcSign s ε) (tA s ε) t)
  (hOutT : GOutT (midG hD).garden ((s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε)) (tA s ε)
    (addrExt (tA s ε) X.lonePath))

include hD hEO hEN hOutT

theorem outG_layer_chain {r : Path} (hr : r ∈ (X.plug (srcSign s ε) .leaf).nodes) :
    layerAt (outG hD t hEO hEN hOutT) (addrExt (tA s ε) r) = layerAt LX ((0 : Fin 1), r) := by
  by_cases hl : X.lonePath <+: r
  · have hrl : X.lonePath = r := leaf_prefix_node_eq (chain_lone_mem_leaves X (srcSign s ε)) hr hl
    subst hrl
    have h1 := graftT_layerAt_tail (LM := midG hD) (M' := (s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε))
      (p := p) hEO hEN hD.hEX hOutT hD.lone' hD.root' []
    simp only [addrExt_nil] at h1
    exact h1.trans hD.lone'.symm
  · exact graftT_layerAt_chain (LM := midG hD) (M' := (s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε))
      (p := p) hEO hEN hD.hEX hOutT hD.lone' hD.root' hl

theorem native_chain_eq :
    nativeChainLayered (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε) (outG hD t hEO hEN hOutT).layer
      (outG hD t hEO hEN hOutT).isLayering (s.branches ε s.placement.lower) = LX := by
  have hFD : (s.finalData ε X Q hD.hX hD.hQ).tree (s.branches ε s.placement.lower) = X := Function.update_self _ _ _
  have hg : (nativeChainLayered (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε) (outG hD t hEO hEN hOutT).layer
      (outG hD t hEO hEN hOutT).isLayering (s.branches ε s.placement.lower)).garden = LX.garden := by
    change decodedTree ((s.finalData ε X Q hD.hX hD.hQ).tree (s.branches ε s.placement.lower))
      (nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1) = LX.garden
    rw [hFD]
    exact (decodedTree_unique X _ LX.garden hD.dX hD.sig).symm
  refine layered_ext hg ?_
  intro x
  by_cases hx : x.2 ∈ ((nativeChainLayered (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε)
      (outG hD t hEO hEN hOutT).layer (outG hD t hEO hEN hOutT).isLayering
      (s.branches ε s.placement.lower)).garden.tree x.1).nodes
  · have hx' : x.2 ∈ (LX.garden.tree x.1).nodes := by rw [← hg]; exact hx
    have hL : layerAt (nativeChainLayered (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε)
        (outG hD t hEO hEN hOutT).layer (outG hD t hEO hEN hOutT).isLayering (s.branches ε s.placement.lower)) x =
        layerAt (outG hD t hEO hEN hOutT) (addrExt (inflatedPosition (s.chosen ε)
          (s.finalData ε X Q hD.hX hD.hQ).tree (s.branches ε s.placement.lower).toNode) x.2) := by
      rw [layerAt_of_mem _ hx]
      exact (layerAt_node (outG hD t hEO hEN hOutT) _).symm
    rw [hL]
    have hxr : x = ((0 : Fin 1), x.2) := Prod.ext (Subsingleton.elim _ _) rfl
    have hmem : x.2 ∈ (X.plug (srcSign s ε) .leaf).nodes := by
      have := hx
      change x.2 ∈ ((decodedTree ((s.finalData ε X Q hD.hX hD.hQ).tree (s.branches ε s.placement.lower))
        (nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1)).tree x.1).nodes at this
      rw [hFD] at this
      exact this
    have h1 := outG_layer_chain hD t hEO hEN hOutT hmem
    rw [pos_final Q hD.hQ X hD.hX, h1, ← hxr]
  · have hx' : x.2 ∉ (LX.garden.tree x.1).nodes := by rw [← hg]; exact hx
    have e1 : layerAt (nativeChainLayered (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε)
        (outG hD t hEO hEN hOutT).layer (outG hD t hEO hEN hOutT).isLayering
        (s.branches ε s.placement.lower)) x = 0 := by
      unfold layerAt; exact dif_neg hx
    have e2 : layerAt LX x = 0 := by unfold layerAt; exact dif_neg hx'
    rw [e1, e2]

theorem collapse_out_eq_mid :
    collapsePairedTreeLayered (outG hD t hEO hEN hOutT)
      ((s.finalData ε X Q hD.hX hD.hQ).decoded_chain_isSubPairedTree (s.chosen_plain ε)
        ((s.finalData ε X Q hD.hX hD.hQ).garden_decodes _) (s.branches ε s.placement.lower)) = midG hD := by
  have hT := graftT_outAgree (LM := midG hD) (M' := (s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε))
    hEO hEN hD.hEX hOutT hD.lone' hD.root'
  exact collapse_insert_tree' (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε) (outG hD t hEO hEN hOutT) (midG hD)
    ((s.finalData ε X Q hD.hX hD.hQ).garden_decodes _) (s.branches ε s.placement.lower) (s.midData ε Q hD.hQ)
    (eraseTree_final X Q hD.hX hD.hQ) X (Function.update_self _ _ _) ((s.midData ε Q hD.hQ).garden_decodes _)
    hEO (oat_nil hT)

theorem outG_layer_couple (i : Fin 2) (r : Path) :
    layerAt (outG hD t hEO hEN hOutT) (addrExt (coupleRoot (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε)
      (s.pairs ε s.exceptional) i) r) = layerAt LQ (i, r) := by
  have h1 := te1_couple (outG hD t hEO hEN hOutT) (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε)
    ((s.finalData ε X Q hD.hX hD.hQ).garden_decodes _) (s.branches ε s.placement.lower) (s.pairs ε s.exceptional) i r
  have h2 := congrArg (fun L => layerAt L (addrExt (coupleRoot ((s.finalData ε X Q hD.hX hD.hQ).eraseTree
    (s.branches ε s.placement.lower)) (s.chosen_plain ε) (s.pairs ε s.exceptional) i) r))
    (collapse_out_eq_mid hD t hEO hEN hOutT)
  have h3 := eraseTree_final (s := s) (ε := ε) X Q hD.hX hD.hQ
  refine h1.trans (h2.trans ?_)
  simp only [h3]
  fin_cases i <;> simp only []
  · have h := graftC_layerAt_a (exc_embM (s := s) (ε := ε) Q hD.hQ).indep exc_embB (exc_embM Q hD.hQ)
      (exc_gout Q hD.hQ) hD.dQ hD.rootA hD.rootB r
    have e : coupleRoot (s.midData ε Q hD.hQ) (s.chosen_plain ε) (s.pairs ε s.exceptional) 0 = cA s ε :=
      coupleRoot_zero s ε
    exact (congrArg (fun z => layerAt (midG hD) (addrExt z r)) e).trans h
  · have h := graftC_layerAt_b (exc_embM (s := s) (ε := ε) Q hD.hQ).indep exc_embB (exc_embM Q hD.hQ)
      (exc_gout Q hD.hQ) hD.dQ hD.rootA hD.rootB r
    have e : coupleRoot (s.midData ε Q hD.hQ) (s.chosen_plain ε) (s.pairs ε s.exceptional) 1 = cB s ε :=
      coupleRoot_one s ε
    exact (congrArg (fun z => layerAt (midG hD) (addrExt z r)) e).trans h

end Native

end WaveTurbulence.ZpSurj
