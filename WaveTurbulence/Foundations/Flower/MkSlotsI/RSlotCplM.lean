/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.RSlotCtx

/-! # B3s-HELPER7 WP6 (R-slot, part 4): the general kernel of an outer couple slot is common to the run class

For a `G_sb` pair `q` and a member `y` of the run class of `a`, the general slot kernel of `y` at `Φ_y.iota (.inl q)`
is the representative's `genSlotKer` at `Φ_a.iota (.inl q)` (**`member_genSlot_inl`**): both are `kerC` of the common
native couple (`memShape_nativeCouple`) with node data read through `RSlotCpl` from the root data of `RSlotCtx`
(`kerC_transport`).

* generic transports: `node_fun_congr2`, `branch_fun_congr2` (a function of the garden, a datum and a node), the
  side transport of a capped flower `flower_transport`, `root_onCapStem`, the congruences `genC_congr`, `genNode_none`;
* the hypotheses: the capped geometry of both reconstructions, the representative's `hrepUP` (no unit atom core pinned,
  β's `PatGeoU.hU_rep_pat_recon`), and, when the weight is stem dependent, `CleanPt J a` and the commonness of the
  existence of selected vertices `hex` (`member_selEx`, RSlotEx). -/

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

/-! ## Generic transports -/

theorem node_fun_congr2 {n : ℕ} {α β : Type*} (F : (N : LayeredGarden n) → α → GNode N.garden.tree → β)
    {N₁ N₂ : LayeredGarden n} (hN : N₁ = N₂) {r₁ r₂ : α} (hr : r₁ = r₂) (x : Fin n × Path)
    (h₁ : x.2 ∈ (N₁.garden.tree x.1).nodes) (h₂ : x.2 ∈ (N₂.garden.tree x.1).nodes) :
    F N₁ r₁ ⟨x, h₁⟩ = F N₂ r₂ ⟨x, h₂⟩ := by
  subst hN hr
  rfl

theorem branch_fun_congr2 {n : ℕ} {α β : Type*} (F : (N : LayeredGarden n) → α → GBranch N.garden.tree → β)
    {N₁ N₂ : LayeredGarden n} (hN : N₁ = N₂) {r₁ r₂ : α} (hr : r₁ = r₂) (x : Fin n × Path)
    (h₁ : x.2 ∈ (N₁.garden.tree x.1).branching) (h₂ : x.2 ∈ (N₂.garden.tree x.1).branching) :
    F N₁ r₁ ⟨x, h₁⟩ = F N₂ r₂ ⟨x, h₂⟩ := by
  subst hN hr
  rfl

theorem flower_transport {w : ℕ} {N₁ N₂ : LayeredGarden 2} (hN : N₁ = N₂) {ri₁ ri₂ : Fin 2 → Fin w}
    (hri : ri₁ = ri₂) (J : Finset (Fin w)) (c : Fin 2) :
    (∃ l : GLeaf N₁.garden.tree, capT_IsFl N₁ ri₁ J l ∧ l.1.1 = c) →
      ∃ l : GLeaf N₂.garden.tree, capT_IsFl N₂ ri₂ J l ∧ l.1.1 = c := by
  subst hN hri
  exact id

/-- A root of a couple whose side carries a capped flower of the couple is on the capped stem. -/
theorem root_onCapStem {w : ℕ} (LG : LayeredGarden w) (E : Comb.RootedSubforest LG.garden.tree 2)
    (hc : LG.garden.CompletelyPaired (Comb.RootedSubforest.leafSet E)) (J : Finset (Fin w)) (c : Fin 2)
    (h : ∃ l : GLeaf (rootedLayeredGarden LG E hc).garden.tree,
      capT_IsFl (rootedLayeredGarden LG E hc) (fun c => (E.root c).1.1) J l ∧ l.1.1 = c) :
    OnCapStem LG J (E.root c) := by
  obtain ⟨l, hl, hl1⟩ := h
  have h2 := (onCapStem_emb_iff LG E hc J (GNode.root (rootedLayeredGarden LG E hc).garden.tree c)).mpr
    ⟨l, hl, hl1, List.nil_prefix⟩
  have he : capT_emb LG E hc (GNode.root (rootedLayeredGarden LG E hc).garden.tree c) = E.root c :=
    subforest_node_root E c
  rw [he] at h2
  exact h2

theorem genC_congr {w : ℕ} (N : LayeredGarden 2) (ri : Fin 2 → Fin w) (rd rd' : Fin 2 → ℕ) (ex : Fin w → Prop)
    (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (hrd : ∀ c : Fin 2, (∃ b : GBranch N.garden.tree, b.1.1 = c ∧ stemN N ri J b) → rd c = rd' c)
    (a : GNode N.garden.tree) (v : ℝ) :
    genC N ri rd ex J L σ kSel Rs a v = genC N ri rd' ex J L σ kSel Rs a v := by
  unfold genC
  by_cases hb : a.1.2 ∈ (N.garden.tree a.1.1).branching
  · rw [dite_eq_left hb, dite_eq_left hb]
    unfold genD
    by_cases hs : stemN N ri J ⟨a.1, hb⟩
    · rw [hrd a.1.1 ⟨⟨a.1, hb⟩, rfl, hs⟩]
    · rw [ite_eq_right hs, ite_eq_right hs]
  · rw [dite_eq_right hb, dite_eq_right hb]

theorem genNode_none {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (J : Finset (Fin w)) (L : ℝ)
    (Rs : Fin w → ℝ) (z : GNode (D.forest hS)) (v : ℝ) :
    genNode D hS layer hLayer J L (fun _ => none) (fun _ => none) Rs z v = 1 := by
  unfold genNode
  split_ifs
  · rfl
  · exact genNW_noFilt (layeredReconstruction D hS layer hLayer) J L Rs z v

theorem stemDep_none {w : ℕ} {σ kSel : Fin w → Option ℕ} (h : ¬ Stage1MKGate.StemDep σ kSel) :
    σ = (fun _ => none) ∧ kSel = (fun _ => none) := by
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · by_contra hi
    exact h (Or.inl ⟨i, hi⟩)
  · by_contra hi
    exact h (Or.inr ⟨i, hi⟩)

/-! ## The run class -/

section Class

variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (J : Finset (Fin (2 * R)))
  (hGeoA : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J p)
  (hGeoY : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p)
  (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (hrepUP : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
      (a.prime.data.coreBranch a.prime.prime.1 b) = none)

include hy hG hGeoA hGeoY hrepUP in
/-- **The general kernel of an outer couple slot is common to the run class.** -/
theorem member_genSlot_inl {d : ℕ} (L γ δ : ℝ) (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (roots : Fin (2 * R) → (Fin d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom d))
    (hstem : Stage1MKGate.StemDep σ kSel → Stage1MKGate.CleanPt J a)
    (hex : Stage1MKGate.StemDep σ kSel → ∀ j,
      (selCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J kSel j).isSome =
        (selCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J kSel
          j).isSome)
    (q : SourcePair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) (ts : Fin 2 → ℝ) (k : Mom d) :
    MkSlotsB.slotFnGWFRL y.1.data y.1.plain L γ δ
        (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) h L
          roots)
        (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L γ δ p s J Rf dag)
        (genΘs y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J L σ kSel Rs)
        (stateLayer y.1) (stateLayer_isLayering y.1)
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)
        ((memShape a mk y hy).iota y.1.plain hG (.inl q)) ts k =
      genSlotKer L γ δ p a J pat t s σ kSel Rs h roots Rf dag
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
          (.inl q)) ts k := by
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA.cap_leaf
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoY.cap_leaf
  have hrepU := MkSlotsB.hrepU_of_pat a mk J pat t s hrepUP
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
  have hrr : ∀ c, cplRR y.1.data y.1.plain qy c ↔ cplRR a.prime.data a.prime.prime.1 qa c := by
    intro c
    unfold cplRR
    rw [(hroot c).1, (hroot c).2, attached_root_iff, attached_root_iff]
  have hrc : cplRC y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J qy =
      cplRC a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J qa := by
    funext c
    unfold cplRC
    rw [(hroot c).1, (hroot c).2]
    exact member_rcOf a mk y hy hG J hcapA hcapY hrepU _
  have hqw : cplQW y.1.data y.1.plain (stateLayer y.1) qy p = cplQW a.prime.data a.prime.prime.1 (sourceLayer a) qa p :=
    funext fun c => memShape_wLay a mk y hy hG (.inl q) c p
  refine (slotFnGWFRL_inl_eq y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J L σ kSel Rs γ δ _ _ _
    qy ts k).trans ((kerC_transport L γ δ hN ?_ ?_ ?_ ?_ ts k).trans (slotFnGWFRL_inl_eq a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) J L σ kSel Rs γ δ _ _ _ qa ts k).symm)
  · -- profiles
    intro x h₁ h₂
    exact (anch_cpl y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J qy h L roots ⟨x, h₁⟩).trans
      ((node_fun_congr2 (fun N r b => capT_prof J N r h L roots b) hN hri x h₁ h₂).trans
        (anch_cpl a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J qa h L roots ⟨x, h₂⟩).symm)
  · -- node weights
    intro x h₁ h₂
    funext v
    by_cases hq : IsCapPair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G hG J q
    · have hqy' := (IntMember.isCapPair_iota Φy y.1.plain hG J q).mpr hq
      have hqa' := (IntMember.isCapPair_iota Φa a.prime.prime.1 hG J q).mpr hq
      exact (chainW_cpl_cap y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J qy hGeoY L γ δ s Rf dag
        hqy' ⟨x, h₁⟩ v).trans
        ((congrFun (node_fun_congr2 (fun N (r : (Fin 2 → Fin (2 * R)) × (Fin 2 → Option (Fin 3))) b =>
          capT_nodeW L γ δ p s J Rf dag N r.1 r.2 b) hN
          (r₁ := (cplRI y.1.data y.1.plain qy,
            cplRC y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J qy))
          (r₂ := (cplRI a.prime.data a.prime.prime.1 qa,
            cplRC a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J qa))
          (by rw [hri, hrc]) x h₁ h₂) v).trans
        (chainW_cpl_cap a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J qa hGeoA L γ δ s Rf
          dag hqa' ⟨x, h₂⟩ v).symm)
    · have hqy' : ¬ IsCapPair y.1.skeleton y.1.plain J qy := fun h' =>
        hq ((IntMember.isCapPair_iota Φy y.1.plain hG J q).mp h')
      have hqa' : ¬ IsCapPair a.prime.skeleton a.prime.prime.1 J qa := fun h' =>
        hq ((IntMember.isCapPair_iota Φa a.prime.prime.1 hG J q).mp h')
      exact (chainW_cpl_noncap y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J qy hcapY L γ δ p s Rf
        dag hqy' ⟨x, h₁⟩ v).trans
        ((congrFun (node_fun_congr2 (fun N (r : (Fin 2 → Fin (2 * R)) × (Fin 2 → ℕ)) b =>
          fwI p (fun j => frontierG (Rf j)) N r.1 r.2 b) hN
          (r₁ := (cplRI y.1.data y.1.plain qy, cplQW y.1.data y.1.plain (stateLayer y.1) qy p))
          (r₂ := (cplRI a.prime.data a.prime.prime.1 qa, cplQW a.prime.data a.prime.prime.1 (sourceLayer a) qa p))
          (by rw [hri, hqw]) x h₁ h₂) v).trans
        (chainW_cpl_noncap a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J qa hcapA L γ δ p
          s Rf dag hqa' ⟨x, h₂⟩ v).symm)
  · -- per-node factors
    intro x h₁ h₂
    funext v
    by_cases hsd : Stage1MKGate.StemDep σ kSel
    · have hc := hstem hsd
      have hexf : (fun j => (selCap LGy J kSel j).isSome = true) = (fun j => (selCap LGa J kSel j).isSome = true) :=
        funext fun j => by rw [hex hsd j]
      refine (genNode_cpl y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J qy L σ kSel Rs
        hGeoY.one_flower ⟨x, h₁⟩ v).trans ?_
      refine Eq.trans ?_ (genNode_cpl a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J qa L
        σ kSel Rs hGeoA.one_flower ⟨x, h₂⟩ v).symm
      rw [hri, hexf]
      refine (genC_congr _ _ _ (cplRD a.prime.data a.prime.prime.1 qa) _ J L σ kSel Rs ?_ ⟨x, h₁⟩ v).trans ?_
      rotate_left
      · exact node_fun_congr2 (fun N (r : Unit) b => genC N (cplRI a.prime.data a.prime.prime.1 qa)
          (cplRD a.prime.data a.prime.prime.1 qa) (fun j => (selCap LGa J kSel j).isSome = true) J L σ kSel Rs b v)
          hN (rfl : () = ()) x h₁ h₂
      · rintro c ⟨b, hbc, ⟨l, hl, hl1, -⟩, -⟩
        have hfy : ∃ l : GLeaf (nativeCoupleLayered y.1.data y.1.plain (stateLayer y.1)
            (stateLayer_isLayering y.1) qy).garden.tree,
            capT_IsFl (nativeCoupleLayered y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) qy)
              (cplRI a.prime.data a.prime.prime.1 qa) J l ∧ l.1.1 = c := ⟨l, hl, hl1.trans hbc⟩
        have hfa := flower_transport hN rfl J c hfy
        have hfy' := flower_transport rfl hri.symm J c hfy
        have stY := root_onCapStem LGy (nativeCoupleForest y.1.data y.1.plain qy)
          (nativeCoupleForest_closed y.1.data y.1.plain qy) J c hfy'
        have stA := root_onCapStem LGa (nativeCoupleForest a.prime.data a.prime.prime.1 qa)
          (nativeCoupleForest_closed a.prime.data a.prime.prime.1 qa) J c hfa
        rw [(hroot c).1] at stY
        rw [(hroot c).2] at stA
        unfold cplRD
        rw [(hroot c).1, (hroot c).2]
        exact member_attached_depth a mk y hy hG J hcapA hcapY hc _
          ((MkMark.onCapStem_iff _ J _).mp stA) ((MkMark.onCapStem_iff _ J _).mp stY)
    · obtain ⟨hσ, hk⟩ := stemDep_none hsd
      subst hσ hk
      exact (genNode_none _ _ _ _ J L Rs _ v).trans (genNode_none _ _ _ _ J L Rs _ v).symm
  · -- pins
    intro x h₁ h₂
    show fixCap LGy J pat t s (capT_bemb LGy (nativeCoupleForest y.1.data y.1.plain qy)
        (nativeCoupleForest_closed y.1.data y.1.plain qy) ⟨x, h₁⟩) =
      fixCap LGa J pat t s (capT_bemb LGa (nativeCoupleForest a.prime.data a.prime.prime.1 qa)
        (nativeCoupleForest_closed a.prime.data a.prime.prime.1 qa) ⟨x, h₂⟩)
    refine MkSlotsB.fixCap_congr J pat t s _ _ ?_ ?_ ?_ ?_ ?_
    · show cplRI y.1.data y.1.plain qy x.1 = cplRI a.prime.data a.prime.prime.1 qa x.1
      rw [hri]
    · exact (capT_cfp_iff LGy _ _ J _ (fun _ => rfl) ⟨x, h₁⟩).trans
        ((branch_fun_congr2 (fun N r b => capT_IsFP N r J b) hN hri x h₁ h₂).to_iff.trans
          (capT_cfp_iff LGa _ _ J _ (fun _ => rfl) ⟨x, h₂⟩).symm)
    · exact (root_bemb_iff LGy _ _ ⟨x, h₁⟩).trans
        ((and_congr Iff.rfl (hrr x.1)).trans (root_bemb_iff LGa _ _ ⟨x, h₂⟩).symm)
    · exact (par_bemb_iff LGy _ _ J ⟨x, h₁⟩).trans
        ((branch_fun_congr2 (fun N r b => ∃ c : GBranch N.garden.tree, capT_IsFP N r J c ∧ c.IsChildOf b) hN hri
          x h₁ h₂).to_iff.trans (par_bemb_iff LGa _ _ J ⟨x, h₂⟩).symm)
    · intro i
      refine (ch_bemb_iff LGy _ _ J ⟨x, h₁⟩ i).trans (Iff.trans ?_ (ch_bemb_iff LGa _ _ J ⟨x, h₂⟩ i).symm)
      refine or_congr (branch_fun_congr2 (fun N r b => ∃ c : GBranch N.garden.tree,
          capT_IsFP N r J c ∧ b.1.1 = c.1.1 ∧ b.1.2 = c.1.2 ++ [i]) hN hri x h₁ h₂).to_iff (and_congr Iff.rfl ?_)
      have e := congrFun hrc x.1
      unfold cplRC at e
      rw [e]

end Class

end WaveTurbulence.Flower.MkSlotsI
