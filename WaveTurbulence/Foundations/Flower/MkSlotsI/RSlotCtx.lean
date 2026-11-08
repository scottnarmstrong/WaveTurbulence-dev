/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.RSlotCh
public import WaveTurbulence.Foundations.Flower.MkSlots.IntChain
public import WaveTurbulence.Foundations.Flower.MkSlots.IntCapM
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoMem
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoChain
public import WaveTurbulence.Foundations.Flower.MkSlotsT.MemberRun
public import WaveTurbulence.Foundations.Flower.MkUnits.WAlign

/-! # B3s-HELPER7 WP6 (R-slot, part 3): the root data of the outer slots are common to the run class

The native objects of the outer slots hang below the attached nodes of `G_sb` nodes `z` (couple roots at the leaves of
a `G_sb` pair, chain tops at `G_sb` branches). Their root data are common to the run class:

* tree index and root test: `attached_tree`, `attached_root_iff` (through any splice shape);
* the capped-flower-parent letter `rcOf` above the attached node: `rcOf_attached` (it is the core of the skeleton
  parent), `node_parent_cases` (that parent is the old name of the `G_sb` parent, or an atom of the unit at a hinge),
  **`member_rcOf`** (α's `member_cfp_iff`, `member_unit_not_cfp`, the representative's `hrepU`);
* the depth of an attached node on the capped stem: `attached_stem_depth` (retention `StemRet`: at a hinge only the
  excluded child can carry the stem), **`member_attached_depth`** (δ's `stemCore_length_member`);
* at a chain slot: the core stem test **`member_coreStem`** (γ's `onStem_core_iff`), the chain-top depth
  **`member_chainTop_depth`**, the clock pin **`member_clock`** (β's `member_fixCap_pat`);
* `cpl_root_attached`: the roots of the native couple of the image of a `G_sb` pair are attached nodes. -/

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
open WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntCore

namespace WaveTurbulence.Flower.MkSlotsI

/-! ## Through a splice shape -/

section Shape

variable {w : ℕ} {S Gsb : Garden w} {Ju : Type} [Fintype Ju] [DecidableEq Ju] {blk : Ju → CLBlock S}
  (Φ : SpliceShape blk Gsb) (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (J : Finset (Fin w))

theorem attached_tree (z : GNode Gsb.tree) : (attachedNode D hS (Φ.node z)).1.1 = z.1.1 :=
  (inflatedPosition_index S D.tree _).trans (Φ.tree_eq z)

theorem attached_root_iff (z : GNode Gsb.tree) : (attachedNode D hS (Φ.node z)).1.2 = [] ↔ z.1.2 = [] := by
  rw [← Φ.root_iff z]
  constructor
  · intro h
    by_contra hn
    exact inflatedPosition_nonroot S D.tree _ hn h
  · intro h
    have he : Φ.node z = GNode.root S.tree (Φ.node z).1.1 := Subtype.ext (Prod.ext rfl h)
    show (inflatedPosition S D.tree (Φ.node z)).2 = []
    rw [he, inflatedPosition_root]

/-- The skeleton parent of the old name of a non-root `G_sb` node: the old name of its `G_sb` parent (same last
step) when that is not a hinge, an atom of the unit when it is (β's `br_parent_cases` for nodes). -/
theorem node_parent_cases (z : GNode Gsb.tree) (hz : z.1.2 ≠ []) :
    ∃ hν : (Φ.node z).1.2 ≠ [],
      ((∀ j, Φ.br (z.parent hz) ≠ (blk j).upper) →
        (Φ.node z).parent hν = Φ.br (z.parent hz) ∧ (Φ.node z).1.2.getLast hν = z.1.2.getLast hz) ∧
      (∀ j, Φ.br (z.parent hz) = (blk j).upper → (Φ.node z).parent hν ∈ (blk j).atoms) := by
  have hν : (Φ.node z).1.2 ≠ [] := fun h => hz ((Φ.root_iff z).mp h)
  refine ⟨hν, fun hnh => ?_, fun j hj => ?_⟩
  · have hn := Φ.child (z.parent hz) (z.1.2.getLast hz) hnh
    rw [Reg.Skeleton.child_parent z hz] at hn
    have hv := congrArg Subtype.val hn
    have h1 : (Φ.node z).1.1 = (Φ.br (z.parent hz)).1.1 := by have h := congrArg Prod.fst hv; exact h
    have h2 : (Φ.node z).1.2 = (Φ.br (z.parent hz)).1.2 ++ [z.1.2.getLast hz] := by
      have h := congrArg Prod.snd hv; exact h
    refine ⟨Subtype.ext ?_, getLast_of_eq' h2 hν⟩
    show ((Φ.node z).1.1, (Φ.node z).1.2.dropLast) = _
    rw [h1, h2, List.dropLast_concat]
  · have hcr := Φ.crown (z.parent hz) j hj (z.1.2.getLast hz)
    rw [Reg.Skeleton.child_parent z hz] at hcr
    obtain ⟨v, hv, i, hvi⟩ := crown_parent (blk j) hcr
    have hpv : (Φ.node z).parent hν = v := by
      have hv' := congrArg Subtype.val hvi
      have h1 : v.1.1 = (Φ.node z).1.1 := by have h := congrArg Prod.fst hv'; exact h
      have h2 : v.1.2 ++ [i] = (Φ.node z).1.2 := by have h := congrArg Prod.snd hv'; exact h
      apply Subtype.ext
      show ((Φ.node z).1.1, (Φ.node z).1.2.dropLast) = v.1
      rw [← h1, ← h2, List.dropLast_concat]
    rw [hpv]
    exact hv

/-- **The capped-flower-parent letter above an attached node** is read at the core of the skeleton parent. -/
theorem rcOf_attached (ν : GNode S.tree) :
    rcOf (layeredReconstruction D hS layer hLayer) J (attachedNode D hS ν) =
      if h : ν.1.2 ≠ [] then
        (if IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS (ν.parent h)) then
          some (ν.1.2.getLast h) else none)
      else none := by
  unfold rcOf
  by_cases h : ν.1.2 ≠ []
  · have h1 : (attachedNode D hS ν).1.2 ≠ [] := inflatedPosition_nonroot S D.tree ν h
    rw [dite_eq_left h1, dite_eq_left h]
    have e := IntGeo.attachedNode_nonroot D hS ν h
    have hv := congrArg Subtype.val e
    have hv2 : (attachedNode D hS ν).1.2 = (D.coreBranch hS (ν.parent h)).1.2 ++ [ν.1.2.getLast h] := by
      have h' := congrArg Prod.snd hv; exact h'
    have hp : GNode.parent (tree := (layeredReconstruction D hS layer hLayer).garden.tree)
        (attachedNode D hS ν) h1 = D.coreBranch hS (ν.parent h) := by
      apply Subtype.ext
      show ((attachedNode D hS ν).1.1, (attachedNode D hS ν).1.2.dropLast) = _
      rw [hv2, List.dropLast_concat]
      have h' := congrArg Prod.fst hv
      exact Prod.ext h' rfl
    rw [hp, getLast_of_eq' hv2 h1]
  · have h1 : ¬ ((attachedNode D hS ν).1.2 ≠ []) := by
      rw [not_not] at h ⊢
      have he : ν = GNode.root S.tree ν.1.1 := Subtype.ext (Prod.ext rfl h)
      show (inflatedPosition S D.tree ν).2 = []
      rw [he, inflatedPosition_root]
    rw [dite_eq_right h1, dite_eq_right h]

/-- **On the capped stem, the attached node of a non-root `G_sb` node hangs below the core of the old name of its
`G_sb` parent** (retention: at a hinge only the excluded child can carry the stem). -/
theorem attached_stem_depth (hR : MkSlotsT.StemRet S D.tree blk (layeredReconstruction D hS layer hLayer) J)
    (z : GNode Gsb.tree) (hz : z.1.2 ≠ [])
    (hst : MkSlotsT.OnStemAddr (layeredReconstruction D hS layer hLayer) J (attachedNode D hS (Φ.node z)).1) :
    (attachedNode D hS (Φ.node z)).1.2.length = (D.corePosition (Φ.br (z.parent hz))).2.length + 1 ∧
      MkSlotsT.OnStemAddr (layeredReconstruction D hS layer hLayer) J (D.corePosition (Φ.br (z.parent hz))) := by
  obtain ⟨hν, h1, h2⟩ := node_parent_cases Φ z hz
  set P := (Φ.node z).parent hν with hP
  have e := IntGeo.attachedNode_nonroot D hS (Φ.node z) hν
  have hv := congrArg Subtype.val e
  have hv1 : (attachedNode D hS (Φ.node z)).1.1 = (D.coreBranch hS P).1.1 := by
    have h' := congrArg Prod.fst hv; exact h'
  have hv2 : (attachedNode D hS (Φ.node z)).1.2 = (D.coreBranch hS P).1.2 ++ [(Φ.node z).1.2.getLast hν] := by
    have h' := congrArg Prod.snd hv; exact h'
  have hstP : MkSlotsT.OnStemAddr (layeredReconstruction D hS layer hLayer) J (D.corePosition P) :=
    MkSlotsT.onStemAddr_of_addrBelow hst ⟨hv1.symm, by rw [hv2]; exact List.prefix_append _ _⟩
  have hPe : P = Φ.br (z.parent hz) := by
    by_cases hh : ∀ j, Φ.br (z.parent hz) ≠ (blk j).upper
    · exact (h1 hh).1
    · push_neg at hh
      obtain ⟨j, hj⟩ := hh
      rw [hj]
      exact hR.upper j _ hstP P (MkSlotsT.owner_corePosition D P) (h2 j hj)
  rw [← hPe]
  refine ⟨?_, hstP⟩
  rw [hv2, List.length_append]
  rfl

end Shape

/-- The roots of the native couple of the image of a `G_sb` pair are the attached nodes of its two leaves. -/
theorem cpl_root_attached {w : ℕ} {S Gsb : Garden w} {Ju : Type} [Fintype Ju] [DecidableEq Ju]
    {blk : Ju → CLBlock S} (Φ : SpliceShape blk Gsb) (D : ReconstructionData S) (hS : S.IsPlain)
    (hG : Gsb.IsPlain) (q : SourcePair Gsb) (c : Fin 2) :
    (nativeCoupleForest D hS (pairOfLeaf S hS (Φ.leaf (q.firstLeaf hG)))).root c =
      attachedNode D hS (Φ.node (if c = 0 then q.firstLeaf hG else q.secondLeaf hG).toNode) := by
  apply Subtype.ext
  rw [IntCapT.capT_root_val, IntCapM.coupleRoot_iota_val Φ D hS hG q c, Φ.leaf_node]
  rfl

/-! ## The run class -/

section Class

variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (J : Finset (Fin (2 * R)))
  (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
  (hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf)
  (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))

include hG hcapA hcapY hrepU in
/-- **The capped-flower-parent letter above the attached node of a `G_sb` node is common to the run class.** -/
theorem member_rcOf (z : GNode (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    rcOf (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
        (attachedNode y.1.data y.1.plain ((memShape a mk y hy).node z)) =
      rcOf (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J
        (attachedNode a.prime.data a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).node z)) := by
  set Φy := memShape a mk y hy
  set Φa := stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
  rw [rcOf_attached y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J,
    rcOf_attached a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J]
  by_cases hz : z.1.2 = []
  · have hy' : ¬ ((Φy.node z).1.2 ≠ []) := fun h => h ((Φy.root_iff z).mpr hz)
    have ha' : ¬ ((Φa.node z).1.2 ≠ []) := fun h => h ((Φa.root_iff z).mpr hz)
    rw [dite_eq_right hy', dite_eq_right ha']
  · obtain ⟨hνy, hy1, hy2⟩ := node_parent_cases Φy z hz
    obtain ⟨hνa, ha1, ha2⟩ := node_parent_cases Φa z hz
    rw [dite_eq_left hνy, dite_eq_left hνa]
    by_cases hh : ∃ j, Φa.br (z.parent hz) =
        (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper
    · obtain ⟨j, hj⟩ := hh
      obtain ⟨j', hj'⟩ := (member_hinge_iff a mk y hy (z.parent hz)).mpr ⟨j, hj⟩
      rw [ite_eq_right (member_unit_not_cfp a mk y hy hG J hcapA hcapY hrepU j' _ (hy2 j' hj')),
        ite_eq_right (hrepU j _ (ha2 j hj))]
    · have h0a : ∀ j, Φa.br (z.parent hz) ≠
          (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper :=
        fun j e => hh ⟨j, e⟩
      have h0y : ∀ j, Φy.br (z.parent hz) ≠ (unitClBlock (y.2 j)).upper := fun j e =>
        hh ((member_hinge_iff a mk y hy _).mp ⟨j, e⟩)
      obtain ⟨py, ly⟩ := hy1 h0y
      obtain ⟨pa, la⟩ := ha1 h0a
      rw [py, pa, ly, la]
      by_cases hc : IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 (Φa.br (z.parent hz)))
      · rw [ite_eq_left hc, ite_eq_left ((member_cfp_iff a mk y hy hG J hcapA hcapY hrepU _).mpr hc)]
      · rw [ite_eq_right hc, ite_eq_right (fun h => hc ((member_cfp_iff a mk y hy hG J hcapA hcapY hrepU _).mp h))]

include hy hG hcapA hcapY in
/-- **The depth of an attached node on the capped stem is common to the run class** (stem-clean representative). -/
theorem member_attached_depth (hc : Stage1MKGate.CleanPt J a)
    (z : GNode (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree)
    (hstA : MkSlotsT.OnStemAddr (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (attachedNode a.prime.data a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).node z)).1)
    (hstY : MkSlotsT.OnStemAddr (layeredReconstruction y.1.data y.1.plain (stateLayer y.1)
      (stateLayer_isLayering y.1)) J (attachedNode y.1.data y.1.plain ((memShape a mk y hy).node z)).1) :
    (attachedNode y.1.data y.1.plain ((memShape a mk y hy).node z)).1.2.length =
      (attachedNode a.prime.data a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).node z)).1.2.length := by
  by_cases hz : z.1.2 = []
  · rw [(attached_root_iff (memShape a mk y hy) y.1.data y.1.plain z).mpr hz,
      (attached_root_iff (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))
        a.prime.data a.prime.prime.1 z).mpr hz]
  · have hR₁ := MkSlotsT.stemRet_congr (VineAlign.sourceLayer_reconstructs a).symm
      (MkSlotsT.stemRet_repMk hc (mk a.prime))
    have hR₂ := MkSlotsT.stemRet_member a mk y hy J hcapA hcapY hc
    obtain ⟨la, sa⟩ := attached_stem_depth (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma
      (mk a.prime)) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J hR₁ z hz hstA
    obtain ⟨ly, -⟩ := attached_stem_depth (memShape a mk y hy) y.1.data y.1.plain (stateLayer y.1)
      (stateLayer_isLayering y.1) J hR₂ z hz hstY
    rw [la, ly, MkSlotsS.stemCore_length_member a mk y hy J hcapA hcapY hG hc (z.parent hz) sa]

include hcapA hcapY in
/-- **The core stem test at a `G_sb` atom is common to the run class** (γ's `onStem_core_iff`). -/
theorem member_coreStem (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    OnCapStem (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
        (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)).toNode ↔
      OnCapStem (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J
        (a.prime.data.coreBranch a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)).toNode := by
  have h1 : OnCapStem (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
      (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)).toNode ↔
      MkSlotsT.OnStemAddr (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
        (y.1.data.corePosition ((memShape a mk y hy).br c)) := MkMark.onCapStem_iff _ J _
  have h2 : OnCapStem (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J
      (a.prime.data.coreBranch a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)).toNode ↔
      MkSlotsT.OnStemAddr (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)) J
        (a.prime.data.corePosition ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma
          (mk a.prime)).br c)) := MkMark.onCapStem_iff _ J _
  exact h1.trans ((MkSlotsT.onStem_core_iff (memShape a mk y hy) y.1.data y.1.plain
    (stateLayer y.1) (stateLayer_isLayering y.1) hcapY c).trans
    ((MkSlotsT.onStem_core_iff (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))
      a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) hcapA c).symm.trans h2.symm))

include hy hG hcapA hcapY in
/-- **The depth of a chain top on the capped stem is common to the run class.** -/
theorem member_chainTop_depth (hc : Stage1MKGate.CleanPt J a)
    (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree)
    (hst : OnCapStem (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)).toNode) :
    (inflatedPosition y.1.skeleton y.1.data.tree ((memShape a mk y hy).br c).toNode).2.length =
      (inflatedPosition a.prime.skeleton a.prime.data.tree
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c).toNode).2.length := by
  have hl := MkSlotsS.stemCore_length_member a mk y hy J hcapA hcapY hG hc c ((MkMark.onCapStem_iff _ J _).mp hst)
  have hch := MkSlotsS.memShape_chain_eq a mk y hy hG c
  unfold ReconstructionData.corePosition at hl
  simp only [addrExt, List.length_append] at hl
  rw [hch] at hl
  omega

variable (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (hrepUP : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
      (a.prime.data.coreBranch a.prime.prime.1 b) = none)

include hG hcapA hcapY hrepUP in
/-- **The clock pin of a chain slot is common to the run class** (β's `member_fixCap_pat`). -/
theorem member_clock (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s
        (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)) =
      fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
        (a.prime.data.coreBranch a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)) :=
  (MkSlotsB.member_fixCap_pat a mk y hy hG J hcapA hcapY pat t s hrepUP c).trans
    (MkSlotsB.fixCap_decoded_eq a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
      (sourceLayer_reconstructs a) a.prime.decodes J pat t s _)

end Class

end WaveTurbulence.Flower.MkSlotsI
