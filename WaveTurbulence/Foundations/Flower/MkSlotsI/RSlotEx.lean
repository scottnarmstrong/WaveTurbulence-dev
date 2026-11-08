/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.RSlotChM

/-! # B3s-HELPER7 WP6 (R-slot, part 6): the existence of a selected vertex is common to the run class

With one capped flower per tree (`CapGeo`) and a stem-clean representative, for every tree `j` the member's tree `j`
has a selected vertex iff the representative's has (**`member_selEx`**). The selected vertex is a capped-stem node;
by γ's classification (`kindMember_spec`, `kindOf_spec`) it is the core of a `G_sb` atom (δ's `selCap_member_core_iff`)
or a non-core native node of a retained slot, which is the image of a `G_sb` slot (`slotRet_iota`); there the selection
is read on the common native object (`selCap_cpl_transfer`, `selCap_ch_transfer`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntCore WaveTurbulence.Flower.MkSlots.IntCapT

namespace WaveTurbulence.Flower.MkSlotsI

/-- A retained slot is the image of a `G_sb` slot. -/
theorem slotRet_iota {w : ℕ} {S Gsb : Garden w} {Ju : Type} [Fintype Ju] [DecidableEq Ju] {blk : Ju → CLBlock S}
    (Φ : SpliceShape blk Gsb) (hS : S.IsPlain) (hG : Gsb.IsPlain) (s : ReplacementSlot S)
    (h : MkSlotsT.SlotRet hS (blk := blk) s) : ∃ s', Φ.iota hS hG s' = s := by
  cases s with
  | inl q =>
    obtain ⟨m, hm⟩ := Φ.exists_leaf h.1
    refine ⟨.inl (pairOfLeaf Gsb hG m), ?_⟩
    show Sum.inl (pairOfLeaf S hS (Φ.leaf ((pairOfLeaf Gsb hG m).firstLeaf hG))) = Sum.inl q
    rw [← IntCore.pairOfLeaf_shape_leaf Φ hS hG m, hm, pairOfLeaf_firstLeaf]
  | inr β =>
    obtain ⟨c, hc⟩ := Φ.exists_br h
    exact ⟨.inr c, congrArg Sum.inr hc⟩

section Class

variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (J : Finset (Fin (2 * R)))
  (hGeoA : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J p)
  (hGeoY : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p)
  (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))
  (hc : Stage1MKGate.CleanPt J a) (kSel : Fin (2 * R) → Option ℕ)

include hy hG hGeoA hGeoY hrepU hc in
/-- **Selection at a native couple branch transfers along the run class.** -/
theorem selCap_cpl_transfer (q : SourcePair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G)
    (x : Fin 2 × Path)
    (h₁ : x.2 ∈ ((nativeCoupleLayered y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
      (pairOfLeaf y.1.skeleton y.1.plain ((memShape a mk y hy).leaf (q.firstLeaf hG)))).garden.tree x.1).branching)
    (h₂ : x.2 ∈ ((nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (pairOfLeaf a.prime.skeleton a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).leaf
          (q.firstLeaf hG)))).garden.tree x.1).branching)
    (j : Fin (2 * R)) :
    selCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J kSel j =
        some (capT_bemb (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
          (nativeCoupleForest y.1.data y.1.plain
            (pairOfLeaf y.1.skeleton y.1.plain ((memShape a mk y hy).leaf (q.firstLeaf hG))))
          (nativeCoupleForest_closed y.1.data y.1.plain
            (pairOfLeaf y.1.skeleton y.1.plain ((memShape a mk y hy).leaf (q.firstLeaf hG)))) ⟨x, h₁⟩) ↔
      selCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J kSel j =
        some (capT_bemb (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
          (nativeCoupleForest a.prime.data a.prime.prime.1 (pairOfLeaf a.prime.skeleton a.prime.prime.1
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).leaf (q.firstLeaf hG))))
          (nativeCoupleForest_closed a.prime.data a.prime.prime.1 (pairOfLeaf a.prime.skeleton a.prime.prime.1
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).leaf (q.firstLeaf hG))))
          ⟨x, h₂⟩) := by
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA.cap_leaf
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoY.cap_leaf
  set Φy := memShape a mk y hy with hΦy
  set Φa := stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) with hΦa
  set qy := pairOfLeaf y.1.skeleton y.1.plain (Φy.leaf (q.firstLeaf hG)) with hqy
  set qa := pairOfLeaf a.prime.skeleton a.prime.prime.1 (Φa.leaf (q.firstLeaf hG)) with hqa
  set LGy := layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) with hLGy
  set LGa := layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    with hLGa
  have hN : nativeCoupleLayered y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) qy =
      nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) qa :=
    memShape_nativeCouple a mk y hy hG q
  have hroot : ∀ c, ((nativeCoupleForest y.1.data y.1.plain qy).root c =
      attachedNode y.1.data y.1.plain (Φy.node (if c = 0 then q.firstLeaf hG else q.secondLeaf hG).toNode)) ∧
      ((nativeCoupleForest a.prime.data a.prime.prime.1 qa).root c =
        attachedNode a.prime.data a.prime.prime.1
          (Φa.node (if c = 0 then q.firstLeaf hG else q.secondLeaf hG).toNode)) :=
    fun c => ⟨cpl_root_attached Φy y.1.data y.1.plain hG q c, cpl_root_attached Φa a.prime.data a.prime.prime.1 hG q c⟩
  have hri : cplRI y.1.data y.1.plain qy = cplRI a.prime.data a.prime.prime.1 qa := by
    funext c
    unfold cplRI
    rw [(hroot c).1, (hroot c).2, attached_tree, attached_tree]
  -- the stem test is common
  have hst : stemN (nativeCoupleLayered y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) qy)
      (cplRI y.1.data y.1.plain qy) J ⟨x, h₁⟩ ↔
      stemN (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) qa)
        (cplRI a.prime.data a.prime.prime.1 qa) J ⟨x, h₂⟩ :=
    (branch_fun_congr2 (fun N r b => stemN N r J b) hN hri x h₁ h₂).to_iff
  -- the depth is common on the stem
  have hrd : stemN (nativeCoupleLayered y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) qy)
      (cplRI y.1.data y.1.plain qy) J ⟨x, h₁⟩ →
        cplRD y.1.data y.1.plain qy x.1 = cplRD a.prime.data a.prime.prime.1 qa x.1 := by
    rintro ⟨⟨l, hl, hl1, -⟩, -⟩
    have hfy : ∃ l : GLeaf (nativeCoupleLayered y.1.data y.1.plain (stateLayer y.1)
        (stateLayer_isLayering y.1) qy).garden.tree,
        capT_IsFl (nativeCoupleLayered y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) qy)
          (cplRI y.1.data y.1.plain qy) J l ∧ l.1.1 = x.1 := ⟨l, hl, hl1⟩
    have hfa := flower_transport hN hri J x.1 hfy
    have stY := root_onCapStem LGy (nativeCoupleForest y.1.data y.1.plain qy)
      (nativeCoupleForest_closed y.1.data y.1.plain qy) J x.1 hfy
    have stA := root_onCapStem LGa (nativeCoupleForest a.prime.data a.prime.prime.1 qa)
      (nativeCoupleForest_closed a.prime.data a.prime.prime.1 qa) J x.1 hfa
    rw [(hroot x.1).1] at stY
    rw [(hroot x.1).2] at stA
    unfold cplRD
    rw [(hroot x.1).1, (hroot x.1).2]
    exact member_attached_depth a mk y hy hG J hcapA hcapY hc _
      ((MkMark.onCapStem_iff _ J _).mp stA) ((MkMark.onCapStem_iff _ J _).mp stY)
  rw [MkSlotsS.selCap_eq_some_iff hGeoY.one_flower, MkSlotsS.selCap_eq_some_iff hGeoA.one_flower,
    MkSlotsS.mem_stemSetCap_iff', MkSlotsS.mem_stemSetCap_iff',
    stem_bemb_iff LGy _ _ J ⟨x, h₁⟩, stem_bemb_iff LGa _ _ J ⟨x, h₂⟩]
  have hl : ∀ (n : ℕ) (r : Path), (n + r.length = (cplRD y.1.data y.1.plain qy x.1) + x.2.length) →
      True := fun _ _ _ => trivial
  have hly : (capT_bemb LGy (nativeCoupleForest y.1.data y.1.plain qy) (nativeCoupleForest_closed y.1.data y.1.plain qy)
      ⟨x, h₁⟩).1.2.length = cplRD y.1.data y.1.plain qy x.1 + x.2.length := by
    show (((nativeCoupleForest y.1.data y.1.plain qy).root x.1).1.2 ++ x.2).length = _
    rw [List.length_append]
    rfl
  have hla : (capT_bemb LGa (nativeCoupleForest a.prime.data a.prime.prime.1 qa)
      (nativeCoupleForest_closed a.prime.data a.prime.prime.1 qa) ⟨x, h₂⟩).1.2.length =
      cplRD a.prime.data a.prime.prime.1 qa x.1 + x.2.length := by
    show (((nativeCoupleForest a.prime.data a.prime.prime.1 qa).root x.1).1.2 ++ x.2).length = _
    rw [List.length_append]
    rfl
  rw [hly, hla]
  have htr : (capT_bemb LGy (nativeCoupleForest y.1.data y.1.plain qy) (nativeCoupleForest_closed y.1.data y.1.plain qy)
      ⟨x, h₁⟩).1.1 = (capT_bemb LGa (nativeCoupleForest a.prime.data a.prime.prime.1 qa)
      (nativeCoupleForest_closed a.prime.data a.prime.prime.1 qa) ⟨x, h₂⟩).1.1 := congrFun hri x.1
  rw [htr]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, hst.mp h2⟩, by rw [← hrd h2]; exact h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, hst.mpr h2⟩, by rw [hrd (hst.mpr h2)]; exact h3⟩

include hy hG hGeoA hGeoY hrepU hc in
/-- **Selection at a native chain branch transfers along the run class.** -/
theorem selCap_ch_transfer (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree)
    (x : Fin 1 × Path)
    (h₁ : x.2 ∈ ((nativeChainLayered y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
      ((memShape a mk y hy).br c)).garden.tree x.1).branching)
    (h₂ : x.2 ∈ ((nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)).garden.tree x.1).branching)
    (j : Fin (2 * R)) :
    selCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J kSel j =
        some (MkSlotsB.nativeBr y.1.data y.1.plain (.inr ((memShape a mk y hy).br c)) ⟨x, h₁⟩) ↔
      selCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J kSel j =
        some (MkSlotsB.nativeBr a.prime.data a.prime.prime.1
          (.inr ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)) ⟨x, h₂⟩) := by
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA.cap_leaf
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoY.cap_leaf
  set Φy := memShape a mk y hy with hΦy
  set Φa := stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) with hΦa
  set LGy := layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) with hLGy
  set LGa := layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    with hLGa
  have hatt : attachedNode y.1.data y.1.plain (Φy.br c).toNode = attachedNode y.1.data y.1.plain (Φy.node c.toNode) ∧
      attachedNode a.prime.data a.prime.prime.1 (Φa.br c).toNode =
        attachedNode a.prime.data a.prime.prime.1 (Φa.node c.toNode) := by
    rw [Φy.br_node, Φa.br_node]
    exact ⟨rfl, rfl⟩
  have hri : chRI y.1.data (Φy.br c) = chRI a.prime.data (Φa.br c) := by
    have e1 := attached_tree Φy y.1.data y.1.plain c.toNode
    have e2 := attached_tree Φa a.prime.data a.prime.prime.1 c.toNode
    rw [← hatt.1] at e1
    rw [← hatt.2] at e2
    exact e1.trans e2.symm
  have hlp : (y.1.data.tree (Φy.br c)).lonePath = (a.prime.data.tree (Φa.br c)).lonePath := by
    rw [MkSlotsS.memShape_chain_eq a mk y hy hG c]
  have hsb := member_coreStem a mk y hy J hcapA hcapY c
  have hny : x.2 ≠ (y.1.data.tree (Φy.br c)).lonePath :=
    lone_not_branch y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) (Φy.br c) ⟨x, h₁⟩
  have hna : x.2 ≠ (a.prime.data.tree (Φa.br c)).lonePath :=
    lone_not_branch a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (Φa.br c) ⟨x, h₂⟩
  have hstY : OnCapStem LGy J (MkSlotsB.nativeBr y.1.data y.1.plain (.inr (Φy.br c)) ⟨x, h₁⟩).toNode ↔
      x.2 <+: (y.1.data.tree (Φy.br c)).lonePath ∧
        OnCapStem LGy J (y.1.data.coreBranch y.1.plain (Φy.br c)).toNode :=
    onCapStem_ch y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J (Φy.br c) hcapY
      ⟨x, TTree.branching_subset_nodes _ h₁⟩ hny
  have hstA : OnCapStem LGa J (MkSlotsB.nativeBr a.prime.data a.prime.prime.1 (.inr (Φa.br c)) ⟨x, h₂⟩).toNode ↔
      x.2 <+: (a.prime.data.tree (Φa.br c)).lonePath ∧
        OnCapStem LGa J (a.prime.data.coreBranch a.prime.prime.1 (Φa.br c)).toNode :=
    onCapStem_ch a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J (Φa.br c) hcapA
      ⟨x, TTree.branching_subset_nodes _ h₂⟩ hna
  have hcfY := cfp_nativeBr_ch y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J (Φy.br c) hcapY
    ⟨x, h₁⟩
  have hcfA := cfp_nativeBr_ch a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J (Φa.br c)
    hcapA ⟨x, h₂⟩
  have htr : (MkSlotsB.nativeBr y.1.data y.1.plain (.inr (Φy.br c)) ⟨x, h₁⟩).1.1 =
      (MkSlotsB.nativeBr a.prime.data a.prime.prime.1 (.inr (Φa.br c)) ⟨x, h₂⟩).1.1 := hri
  have hly : (MkSlotsB.nativeBr y.1.data y.1.plain (.inr (Φy.br c)) ⟨x, h₁⟩).1.2.length =
      chRD y.1.data (Φy.br c) + x.2.length := by
    show ((inflatedPosition y.1.skeleton y.1.data.tree (Φy.br c).toNode).2 ++ x.2).length = _
    rw [List.length_append]
    rfl
  have hla : (MkSlotsB.nativeBr a.prime.data a.prime.prime.1 (.inr (Φa.br c)) ⟨x, h₂⟩).1.2.length =
      chRD a.prime.data (Φa.br c) + x.2.length := by
    show ((inflatedPosition a.prime.skeleton a.prime.data.tree (Φa.br c).toNode).2 ++ x.2).length = _
    rw [List.length_append]
    rfl
  refine (MkSlotsS.selCap_eq_some_iff (LG := LGy) hGeoY.one_flower kSel j
    (MkSlotsB.nativeBr y.1.data y.1.plain (.inr (Φy.br c)) ⟨x, h₁⟩)).trans (Iff.trans ?_
    (MkSlotsS.selCap_eq_some_iff (LG := LGa) hGeoA.one_flower kSel j
      (MkSlotsB.nativeBr a.prime.data a.prime.prime.1 (.inr (Φa.br c)) ⟨x, h₂⟩)).symm)
  constructor
  · rintro ⟨hm, hk⟩
    obtain ⟨h1, hs, -⟩ := MkSlotsS.mem_stemSetCap_iff'.1 hm
    obtain ⟨hp, hcs⟩ := hstY.mp hs
    have hd : chRD y.1.data (Φy.br c) = chRD a.prime.data (Φa.br c) :=
      member_chainTop_depth a mk y hy hG J hcapA hcapY hc c (hsb.mp hcs)
    refine ⟨MkSlotsS.mem_stemSetCap_iff'.2 ⟨htr.symm.trans h1, hstA.mpr ⟨hlp ▸ hp, hsb.mp hcs⟩, hcfA⟩, ?_⟩
    exact hk.trans (congrArg some (hly.trans ((congrArg (· + x.2.length) hd).trans hla.symm)))
  · rintro ⟨hm, hk⟩
    obtain ⟨h1, hs, -⟩ := MkSlotsS.mem_stemSetCap_iff'.1 hm
    obtain ⟨hp, hcs⟩ := hstA.mp hs
    have hd : chRD y.1.data (Φy.br c) = chRD a.prime.data (Φa.br c) :=
      member_chainTop_depth a mk y hy hG J hcapA hcapY hc c hcs
    refine ⟨MkSlotsS.mem_stemSetCap_iff'.2 ⟨htr.trans h1, hstY.mpr ⟨hlp ▸ hp, hsb.mpr hcs⟩, hcfY⟩, ?_⟩
    exact hk.trans (congrArg some (hla.trans ((congrArg (· + x.2.length) hd.symm).trans hly.symm)))

include hy hG hGeoA hGeoY hrepU hc in
/-- **The existence of a selected vertex of every tree is common to the run class.** -/
theorem member_selEx (j : Fin (2 * R)) :
    (selCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J kSel j).isSome =
      (selCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J kSel
        j).isSome := by
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA.cap_leaf
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoY.cap_leaf
  set Φy := memShape a mk y hy with hΦy
  set Φa := stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) with hΦa
  set LGy := layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) with hLGy
  set LGa := layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    with hLGa
  have hdy := source_disjMk a mk y hy
  have hda := unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
  have hRa := MkSlotsT.stemRet_congr (VineAlign.sourceLayer_reconstructs a).symm
    (MkSlotsT.stemRet_repMk hc (mk a.prime))
  have hcore := fun c => MkSlotsS.selCap_member_core_iff a mk y hy J hcapA hcapY hG hrepU hc hGeoA.one_flower
    hGeoY.one_flower kSel j c
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hs
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    have hst : v ∈ stemSetCap LGy J j := (MkSlotsS.selCap_spec hv).2
    have hon : MkSlotsT.OnStemAddr LGy J v.toNode.1 := MkSlotsT.onStemAddr_of_mem_stemSetCap hst
    obtain ⟨hA, hT, hSl, hRet⟩ := MkSlotsT.kindMember_spec a mk y hy J hcapA hcapY hc (z := v.toNode) hon
    cases hk : MkSlotsT.kindOf y.1.data y.1.plain Φy v.toNode with
    | atom c =>
      obtain ⟨hv', -⟩ := (hA c).mp hk
      have hve : v = MkSlotsT.coreLG y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) (Φy.br c) := by
        have hvv := congrArg Subtype.val hv'
        exact Subtype.ext hvv
      rw [hve] at hv
      rw [(hcore c).mp hv]
      rfl
    | top j' =>
      have hv' := (hT j').mp hk
      have hu : (unitClBlock (y.2 j')).upper = Φy.br (Φy.hinge hdy j') := (Φy.br_hinge hdy j').symm
      rw [hu] at hv'
      have hve : v = MkSlotsT.coreLG y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
          (Φy.br (Φy.hinge hdy j')) := by
        have hvv := congrArg Subtype.val hv'
        exact Subtype.ext hvv
      rw [hve] at hv
      rw [(hcore _).mp hv]
      rfl
    | slot sl =>
      obtain ⟨hsl, hnc⟩ := (hSl sl).mp hk
      obtain ⟨s', hs'⟩ := slotRet_iota Φy y.1.plain hG _ hRet
      cases s' with
      | inl q =>
        obtain ⟨x, hx⟩ := IntGeo.exists_nativeNodeAt_of_slotOf y.1.data y.1.plain hs'.symm
        have hval : ((nativeCoupleForest y.1.data y.1.plain
            (pairOfLeaf y.1.skeleton y.1.plain (Φy.leaf (q.firstLeaf hG)))).nodeEmbedding x).1 = v.1 :=
          congrArg Subtype.val hx
        have hb : x.1.2 ∈ ((nativeCoupleLayered y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
            (pairOfLeaf y.1.skeleton y.1.plain (Φy.leaf (q.firstLeaf hG)))).garden.tree x.1.1).branching := by
          refine (Comb.subtree_branching_iff ((nativeCoupleForest y.1.data y.1.plain
            (pairOfLeaf y.1.skeleton y.1.plain (Φy.leaf (q.firstLeaf hG)))).subtree_eq x.1.1) x.1.2).mpr ?_
          have h := v.2
          rw [← hval] at h
          exact h
        have hve : v = capT_bemb LGy (nativeCoupleForest y.1.data y.1.plain
            (pairOfLeaf y.1.skeleton y.1.plain (Φy.leaf (q.firstLeaf hG))))
            (nativeCoupleForest_closed y.1.data y.1.plain
              (pairOfLeaf y.1.skeleton y.1.plain (Φy.leaf (q.firstLeaf hG)))) ⟨x.1, hb⟩ := Subtype.ext hval.symm
        rw [hve] at hv
        have h2 := branching_of_eq (memShape_nativeCouple a mk y hy hG q) hb
        rw [(selCap_cpl_transfer a mk y hy hG J hGeoA hGeoY hrepU hc kSel q x.1 hb h2 j).mp hv]
        rfl
      | inr c =>
        obtain ⟨x, hx⟩ := IntGeo.exists_nativeNodeAt_of_slotOf y.1.data y.1.plain hs'.symm
        have hx' : chainContextNode y.1.data y.1.plain (Φy.br c) x = v.toNode := hx
        have hb : x.1.2 ∈ ((nativeChainLayered y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
            (Φy.br c)).garden.tree x.1.1).branching := by
          refine chain_branch_of_branch' y.1.data y.1.plain (Φy.br c) x ?_ ?_
          · rw [hx']
            exact v.2
          · rw [hx']
            exact hnc (Φy.br c)
        have hve : v = MkSlotsB.nativeBr y.1.data y.1.plain (.inr (Φy.br c)) ⟨x.1, hb⟩ :=
          Subtype.ext (congrArg Subtype.val hx').symm
        rw [hve] at hv
        have h2 := branching_of_eq (MkSlotsB.memShape_nativeChain a mk y hy hG c) hb
        rw [(selCap_ch_transfer a mk y hy hG J hGeoA hGeoY hrepU hc kSel c x.1 hb h2 j).mp hv]
        rfl
  · intro hs
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    have hst : v ∈ stemSetCap LGa J j := (MkSlotsS.selCap_spec hv).2
    have hon : MkSlotsT.OnStemAddr LGa J v.toNode.1 := MkSlotsT.onStemAddr_of_mem_stemSetCap hst
    obtain ⟨hA, hT, hSl, hRet⟩ := MkSlotsT.kindOf_spec a.prime.data a.prime.prime.1 Φa hda hRa (z := v.toNode) hon
    cases hk : MkSlotsT.kindOf a.prime.data a.prime.prime.1 Φa v.toNode with
    | atom c =>
      obtain ⟨hv', -⟩ := (hA c).mp hk
      have hve : v = MkSlotsT.coreLG a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (Φa.br c) := by
        have hvv := congrArg Subtype.val hv'
        exact Subtype.ext hvv
      rw [hve] at hv
      rw [(hcore c).mpr hv]
      rfl
    | top j' =>
      have hv' := (hT j').mp hk
      have hu : (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j').upper =
          Φa.br (Φa.hinge hda j') := (Φa.br_hinge hda j').symm
      rw [hu] at hv'
      have hve : v = MkSlotsT.coreLG a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (Φa.br (Φa.hinge hda j')) := by
        have hvv := congrArg Subtype.val hv'
        exact Subtype.ext hvv
      rw [hve] at hv
      rw [(hcore _).mpr hv]
      rfl
    | slot sl =>
      obtain ⟨hsl, hnc⟩ := (hSl sl).mp hk
      obtain ⟨s', hs'⟩ := slotRet_iota Φa a.prime.prime.1 hG _ hRet
      cases s' with
      | inl q =>
        obtain ⟨x, hx⟩ := IntGeo.exists_nativeNodeAt_of_slotOf a.prime.data a.prime.prime.1 hs'.symm
        have hval : ((nativeCoupleForest a.prime.data a.prime.prime.1
            (pairOfLeaf a.prime.skeleton a.prime.prime.1 (Φa.leaf (q.firstLeaf hG)))).nodeEmbedding x).1 = v.1 :=
          congrArg Subtype.val hx
        have hb : x.1.2 ∈ ((nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            (pairOfLeaf a.prime.skeleton a.prime.prime.1 (Φa.leaf (q.firstLeaf hG)))).garden.tree x.1.1).branching := by
          refine (Comb.subtree_branching_iff ((nativeCoupleForest a.prime.data a.prime.prime.1
            (pairOfLeaf a.prime.skeleton a.prime.prime.1 (Φa.leaf (q.firstLeaf hG)))).subtree_eq x.1.1) x.1.2).mpr ?_
          have h := v.2
          rw [← hval] at h
          exact h
        have hve : v = capT_bemb LGa (nativeCoupleForest a.prime.data a.prime.prime.1
            (pairOfLeaf a.prime.skeleton a.prime.prime.1 (Φa.leaf (q.firstLeaf hG))))
            (nativeCoupleForest_closed a.prime.data a.prime.prime.1
              (pairOfLeaf a.prime.skeleton a.prime.prime.1 (Φa.leaf (q.firstLeaf hG)))) ⟨x.1, hb⟩ :=
          Subtype.ext hval.symm
        rw [hve] at hv
        have h1 := branching_of_eq (memShape_nativeCouple a mk y hy hG q).symm hb
        rw [(selCap_cpl_transfer a mk y hy hG J hGeoA hGeoY hrepU hc kSel q x.1 h1 hb j).mpr hv]
        rfl
      | inr c =>
        obtain ⟨x, hx⟩ := IntGeo.exists_nativeNodeAt_of_slotOf a.prime.data a.prime.prime.1 hs'.symm
        have hx' : chainContextNode a.prime.data a.prime.prime.1 (Φa.br c) x = v.toNode := hx
        have hb : x.1.2 ∈ ((nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            (Φa.br c)).garden.tree x.1.1).branching := by
          refine chain_branch_of_branch' a.prime.data a.prime.prime.1 (Φa.br c) x ?_ ?_
          · rw [hx']
            exact v.2
          · rw [hx']
            exact hnc (Φa.br c)
        have hve : v = MkSlotsB.nativeBr a.prime.data a.prime.prime.1 (.inr (Φa.br c)) ⟨x.1, hb⟩ :=
          Subtype.ext (congrArg Subtype.val hx').symm
        rw [hve] at hv
        have h1 := branching_of_eq (MkSlotsB.memShape_nativeChain a mk y hy hG c).symm hb
        rw [(selCap_ch_transfer a mk y hy hG J hGeoA hGeoY hrepU hc kSel c x.1 h1 hb j).mpr hv]
        rfl

end Class

end WaveTurbulence.Flower.MkSlotsI
