/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsS.SelSpec
public import WaveTurbulence.Foundations.Flower.MkSlotsT.MemberRun
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoChain

/-! # B3s-HELPER4 (δ) S2 (4): the selected vertex is class-common

The selected vertex of tree `j` is the unique capped-stem branch of tree `j` at depth `k = kSel j` (one capped flower
per tree). Helper γ's member transport (`MkSlotsT.stemRet_member`, `kindMember_spec`, `stemB_member_iff`) shows that
whether the core of a `G_sb` atom `c` lies on the capped stem is common to the run class. Here: its DEPTH is common too,
so the selected vertex of every member is the core of the same `G_sb` atom as for the representative (or of none).

* `stem_br_child`: along the stem the skeleton image of a `G_sb` atom is a direct skeleton child of the image of its
  `G_sb` parent (through a hinge: the excluded child of the upper joint; the lower crown children are excluded by
  γ's retention `StemRet`, as in `selROf_not_lowerCrown`);
* `corePosition_length_child`, `corePosition_length_root`: `|core β| = |core β'| + 1 + |lonePath X(β)|`;
* **`stemCore_length_eq`** (two reconstructions with splice shapes onto the same `G_sb`, equal lone-path lengths):
  stem cores of the same `G_sb` atom have the same depth;
* `memShape_chain_eq`: the chains `X(β)` at the `G_sb` atoms are common to the run class (β's `memShape_nativeChain`
  and main's `decodedTree_wf_injective`), hence `stemCore_length_member`;
* `selCap_eq_some_iff`: with one capped flower per tree, `selCap LG J kSel j = some b ↔ b ∈ stemSetCap j ∧
  kSel j = some |b|`;
* **`selCap_member_core_iff`**: for a member `y` of the run class of `a`, `y`'s selected vertex of tree `j` is the core
  of `c` iff the representative's is. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Flower.MkDefs
open WaveTurbulence.VineB WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Flower.MkSlotsT (StemRet OnStemAddr onStemAddr_of_addrBelow owner_corePosition
  onStem_core_iff coreLG StemB)

namespace WaveTurbulence.Flower.MkSlotsS

variable {w : ℕ}

/-! ## The depth of a stem core -/

section Depth

variable {S Gsb : Garden w} {ι : Type} [Fintype ι] [DecidableEq ι] {blk : ι → RedSplice.CLBlock S}
  (Φ : SpliceShape blk Gsb) (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) {J : Finset (Fin w)}

/-- `|core β| = |core β'| + 1 + |lonePath X(β)|` for a skeleton child `β` of `β'`. -/
theorem corePosition_length_child (β β' : GBranch S.tree) (i : Fin 3) (h : β.toNode = β'.child i) :
    (D.corePosition β).2.length = (D.corePosition β').2.length + 1 + (D.tree β).lonePath.length := by
  unfold ReconstructionData.corePosition
  rw [h, inflatedPosition_child]
  simp [addrExt, List.length_append]
  omega

/-- At a `G_sb` root, `|core| = |lonePath|`. -/
theorem corePosition_length_root (c : GBranch Gsb.tree) (hc : c.1.2 = []) :
    (D.corePosition (Φ.br c)).2.length = (D.tree (Φ.br c)).lonePath.length := by
  have hroot : (Φ.br c).toNode = GNode.root S.tree c.1.1 := by
    rw [Φ.br_node]
    have : c.toNode = GNode.root Gsb.tree c.1.1 := Subtype.ext (Prod.ext rfl hc)
    rw [this, Φ.root]
  unfold ReconstructionData.corePosition
  rw [hroot, inflatedPosition_root]
  simp [addrExt]

/-- A lower crown child of a unit is never the image of a `G_sb` atom with a stem core. -/
theorem not_lowerCrown_of_stem (hR : StemRet S D.tree blk (layeredReconstruction D hS layer hLayer) J)
    (β : GBranch S.tree) (j : ι) (i : Fin 3) (hβ : β.toNode = (blk j).lower.child i)
    (hst : OnStemAddr (layeredReconstruction D hS layer hLayer) J (D.corePosition β)) : False := by
  have hbelow := addrBelow_corePosition_of_child D (blk j).lower β i hβ
  have hlow := onStemAddr_of_addrBelow hst hbelow
  have heq := hR.upper j _ hlow (blk j).lower (owner_corePosition D (blk j).lower) (blk j).isBlock.2.2.1
  exact (blk j).isBlock.2.2.2.1 heq.symm

/-- **Along the stem, the image of a `G_sb` atom is a skeleton child of the image of its `G_sb` parent.** -/
theorem stem_br_child (hR : StemRet S D.tree blk (layeredReconstruction D hS layer hLayer) J)
    (c : GBranch Gsb.tree) (hc : c.1.2 ≠ [])
    (hst : OnStemAddr (layeredReconstruction D hS layer hLayer) J (D.corePosition (Φ.br c))) :
    ∃ i : Fin 3, (Φ.br c).toNode = (Φ.br (c.toNode.parent hc)).child i := by
  set c' := c.toNode.parent hc
  have hcc : c'.child (c.1.2.getLast hc) = c.toNode := child_parent c.toNode hc
  by_cases hup : ∀ j, Φ.br c' ≠ (blk j).upper
  · refine ⟨c.1.2.getLast hc, ?_⟩
    rw [Φ.br_node, ← hcc, Φ.child c' _ hup]
  · push Not at hup
    obtain ⟨j, hj⟩ := hup
    have hcr := Φ.crown c' j hj (c.1.2.getLast hc)
    rw [hcc, ← Φ.br_node] at hcr
    rcases hcr with h | h | h
    · exact ⟨(regionOf (blk j)).excluded, by rw [h, hj]⟩
    · exact (not_lowerCrown_of_stem D hS layer hLayer hR (Φ.br c) j _ h hst).elim
    · exact (not_lowerCrown_of_stem D hS layer hLayer hR (Φ.br c) j _ h hst).elim

end Depth

section Compare

variable {S₁ S₂ Gsb : Garden w} {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  {blk₁ : ι₁ → RedSplice.CLBlock S₁} {blk₂ : ι₂ → RedSplice.CLBlock S₂}
  (Φ₁ : SpliceShape blk₁ Gsb) (Φ₂ : SpliceShape blk₂ Gsb)
  (D₁ : ReconstructionData S₁) (hS₁ : S₁.IsPlain) (layer₁ : GNode (D₁.forest hS₁) → ℕ)
  (hLayer₁ : IsLayering (D₁.garden hS₁) layer₁)
  (D₂ : ReconstructionData S₂) (hS₂ : S₂.IsPlain) (layer₂ : GNode (D₂.forest hS₂) → ℕ)
  (hLayer₂ : IsLayering (D₂.garden hS₂) layer₂) {J : Finset (Fin w)}

/-- **Stem cores of the same `G_sb` atom have the same depth** in two reconstructions onto the same `G_sb` whose
chains at the `G_sb` atoms have equal lone-path lengths. -/
theorem stemCore_length_eq
    (hcap₁ : ∀ j ∈ J, (D₁.garden hS₁).tree j = TTree.leaf) (hcap₂ : ∀ j ∈ J, (D₂.garden hS₂).tree j = TTree.leaf)
    (hR₁ : StemRet S₁ D₁.tree blk₁ (layeredReconstruction D₁ hS₁ layer₁ hLayer₁) J)
    (hR₂ : StemRet S₂ D₂.tree blk₂ (layeredReconstruction D₂ hS₂ layer₂ hLayer₂) J)
    (hlone : ∀ c, (D₁.tree (Φ₁.br c)).lonePath.length = (D₂.tree (Φ₂.br c)).lonePath.length) :
    ∀ c : GBranch Gsb.tree,
      OnStemAddr (layeredReconstruction D₁ hS₁ layer₁ hLayer₁) J (D₁.corePosition (Φ₁.br c)) →
      (D₁.corePosition (Φ₁.br c)).2.length = (D₂.corePosition (Φ₂.br c)).2.length := by
  intro c
  induction hn : c.1.2.length using Nat.strong_induction_on generalizing c with
  | _ n ih =>
  intro hst₁
  have hst₂ : OnStemAddr (layeredReconstruction D₂ hS₂ layer₂ hLayer₂) J (D₂.corePosition (Φ₂.br c)) :=
    (onStem_core_iff Φ₂ D₂ hS₂ layer₂ hLayer₂ hcap₂ c).2 ((onStem_core_iff Φ₁ D₁ hS₁ layer₁ hLayer₁ hcap₁ c).1 hst₁)
  by_cases hc : c.1.2 = []
  · rw [corePosition_length_root Φ₁ D₁ c hc, corePosition_length_root Φ₂ D₂ c hc, hlone c]
  · obtain ⟨i₁, h₁⟩ := stem_br_child Φ₁ D₁ hS₁ layer₁ hLayer₁ hR₁ c hc hst₁
    obtain ⟨i₂, h₂⟩ := stem_br_child Φ₂ D₂ hS₂ layer₂ hLayer₂ hR₂ c hc hst₂
    have hst₁' := onStemAddr_of_addrBelow hst₁ (addrBelow_corePosition_of_child D₁ _ _ i₁ h₁)
    have hlen : (c.toNode.parent hc).1.2.length < n := by
      show c.1.2.dropLast.length < n
      rw [List.length_dropLast, ← hn]
      have : c.1.2.length ≠ 0 := fun h0 => hc (List.length_eq_zero_iff.mp h0)
      omega
    rw [corePosition_length_child D₁ _ _ i₁ h₁, corePosition_length_child D₂ _ _ i₂ h₂,
      ih _ hlen (c.toNode.parent hc) rfl hst₁', hlone c]

end Compare

/-! ## Selected vertices by depth -/

section Sel

variable {LG : LayeredGarden w} {J : Finset (Fin w)}

/-- One capped flower per tree (`CapGeo.one_flower`). -/
def OneFlower (LG : LayeredGarden w) (J : Finset (Fin w)) : Prop :=
  ∀ ℓ ℓ' : GLeaf LG.garden.tree, IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ.1.1 = ℓ'.1.1 → ℓ = ℓ'

theorem stem_eq_of_length (hone : OneFlower LG J) {j : Fin w} {b b' : GBranch LG.garden.tree}
    (hb : b ∈ stemSetCap LG J j) (hb' : b' ∈ stemSetCap LG J j) (hl : b.1.2.length = b'.1.2.length) : b = b' := by
  obtain ⟨hbj, ⟨ℓ, hℓ, hd⟩, -⟩ := mem_stemSetCap_iff'.1 hb
  obtain ⟨hbj', ⟨ℓ', hℓ', hd'⟩, -⟩ := mem_stemSetCap_iff'.1 hb'
  have hℓℓ : ℓ = ℓ' := hone ℓ ℓ' hℓ hℓ' (hd.1.symm.trans (hbj.trans (hbj'.symm.trans hd'.1)))
  subst hℓℓ
  have hp : b.1.2 <+: b'.1.2 := List.prefix_of_prefix_length_le hd.2 hd'.2 hl.le
  have hpe : b.1.2 = b'.1.2 := hp.eq_of_length hl
  exact Subtype.ext (Prod.ext (hbj.trans hbj'.symm) hpe)

theorem stemAt_spec {j : Fin w} {k : ℕ} {b : GBranch LG.garden.tree} (h : stemAt LG J j k = some b) :
    b ∈ stemSetCap LG J j ∧ b.1.2.length = k := by
  unfold stemAt at h
  split_ifs at h with hc
  have hspec := Classical.choose_spec (Finset.card_eq_one.mp hc)
  have hmem : Classical.choose (Finset.card_eq_one.mp hc) ∈
      ({Classical.choose (Finset.card_eq_one.mp hc)} : Finset (GBranch LG.garden.tree)) :=
    Finset.mem_singleton_self _
  rw [← hspec] at hmem
  obtain rfl := Option.some.inj h
  exact Finset.mem_filter.1 hmem

theorem stemAt_of_mem (hone : OneFlower LG J) {j : Fin w} {b : GBranch LG.garden.tree}
    (hb : b ∈ stemSetCap LG J j) : stemAt LG J j b.1.2.length = some b := by
  have hfilt : (stemSetCap LG J j).filter (fun b' => b'.1.2.length = b.1.2.length) = {b} := by
    ext b'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hb', hl⟩; exact stem_eq_of_length hone hb' hb hl
    · rintro rfl; exact ⟨hb, rfl⟩
  have hc : ((stemSetCap LG J j).filter fun b' => b'.1.2.length = b.1.2.length).card = 1 := by
    rw [hfilt]; rfl
  unfold stemAt
  rw [dif_pos hc]
  have hspec := Classical.choose_spec (Finset.card_eq_one.mp hc)
  exact congrArg some (Finset.singleton_inj.mp (hspec.symm.trans hfilt))

/-- **The selected vertex by depth.** -/
theorem selCap_eq_some_iff (hone : OneFlower LG J) (kSel : Fin w → Option ℕ) (j : Fin w)
    (b : GBranch LG.garden.tree) :
    selCap LG J kSel j = some b ↔ b ∈ stemSetCap LG J j ∧ kSel j = some b.1.2.length := by
  unfold selCap
  constructor
  · intro h
    cases hk : kSel j with
    | none => rw [hk] at h; exact absurd h (by simp)
    | some k =>
      rw [hk] at h
      obtain ⟨hb, hl⟩ := stemAt_spec h
      exact ⟨hb, by rw [hl]⟩
  · rintro ⟨hb, hk⟩
    rw [hk]
    exact stemAt_of_mem hone hb

end Sel

/-! ## The run class -/

open WaveTurbulence.LFTwist WaveTurbulence.RedSplice WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
  WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.Stage1MKGate (CleanPt)

/-- **The chains at the `G_sb` atoms are common to the run class.** -/
theorem memShape_chain_eq {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    y.1.data.tree ((memShape a mk y hy).br c) =
      a.prime.data.tree ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c) := by
  have h := MkSlotsB.memShape_nativeChain a mk y hy hG c
  have hg : decodedTree (y.1.data.tree ((memShape a mk y hy).br c))
        (nodeSign y.1.skeleton.sig ((memShape a mk y hy).br c).1) =
      decodedTree (a.prime.data.tree ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma
          (mk a.prime)).br c))
        (nodeSign a.prime.skeleton.sig ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma
          (mk a.prime)).br c).1) :=
    congrArg LayeredGarden.garden h
  have hs := congrArg (fun G : Garden 1 => G.sig 0) hg
  simp only [decodedTree_sign] at hs
  rw [hs] at hg
  exact congrArg Subtype.val (decodedTree_wf_injective _ (a₁ := ⟨_, y.1.data.tree_wf _⟩)
    (a₂ := ⟨_, a.prime.data.tree_wf _⟩) hg)

section Class

variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (J : Finset (Fin (2 * R)))
  (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
  (hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)

include hy hcapA hcapY hG in
/-- **The depth of a stem core is common to the run class.** -/
theorem stemCore_length_member (hc : CleanPt J a)
    (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree)
    (hst : OnStemAddr (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
      J (a.prime.data.corePosition
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c))) :
    (a.prime.data.corePosition
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)).2.length =
      (y.1.data.corePosition ((memShape a mk y hy).br c)).2.length := by
  have hR₁ := MkSlotsT.stemRet_congr (VineAlign.sourceLayer_reconstructs a).symm
    (MkSlotsT.stemRet_repMk hc (mk a.prime))
  have hR₂ := MkSlotsT.stemRet_member a mk y hy J hcapA hcapY hc
  refine stemCore_length_eq (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))
    (memShape a mk y hy) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) hcapA hcapY hR₁ hR₂ (fun c' => ?_) c hst
  rw [memShape_chain_eq a mk y hy hG c']

variable (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))

include hy hcapA hcapY hG hrepU in
/-- **S2, class-common**: for a member `y` of the run class of the representative `a`, the selected vertex of tree `j`
of `y` is the core of the `G_sb` atom `c` iff the representative's is (both reconstructions with one capped flower
per tree, `a` stem-clean). -/
theorem selCap_member_core_iff (hc : CleanPt J a)
    (honeA : OneFlower (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J)
    (honeY : OneFlower (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J)
    (kSel : Fin (2 * R) → Option ℕ) (j : Fin (2 * R))
    (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    selCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J kSel j =
        some (coreLG y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) ((memShape a mk y hy).br c)) ↔
      selCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J kSel j =
        some (coreLG a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)) := by
  set bY := coreLG y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) ((memShape a mk y hy).br c)
  set bA := coreLG a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)
  have htY : bY.1.1 = c.1.1 :=
    (MkSlots.IntRest.coreBranch_fst y.1.data y.1.plain _).trans (MkSlotsT.shape_br_fst (memShape a mk y hy) c)
  have htA : bA.1.1 = c.1.1 :=
    (MkSlots.IntRest.coreBranch_fst a.prime.data a.prime.prime.1 _).trans
      (MkSlotsT.shape_br_fst (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) c)
  have hsB := MkSlotsT.stemB_member_iff a mk y hy J hcapA hcapY hG hrepU c
  -- stem membership in tree `j`
  have hmem : bY ∈ stemSetCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1)
      (stateLayer_isLayering y.1)) J j ↔
      bA ∈ stemSetCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)) J j := by
    constructor
    · intro h
      obtain ⟨j', hj'⟩ := hsB.1 ⟨j, h⟩
      have h1 := (mem_stemSetCap_iff'.1 hj').1
      have h2 := (mem_stemSetCap_iff'.1 h).1
      rwa [show j = j' by rw [← h1, ← h2, htY, htA]]
    · intro h
      obtain ⟨j', hj'⟩ := hsB.2 ⟨j, h⟩
      have h1 := (mem_stemSetCap_iff'.1 hj').1
      have h2 := (mem_stemSetCap_iff'.1 h).1
      rwa [show j = j' by rw [← h1, ← h2, htY, htA]]
  -- equal depths for stem cores
  have hlen : bA ∈ stemSetCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J j → bA.1.2.length = bY.1.2.length := fun h =>
    stemCore_length_member a mk y hy J hcapA hcapY hG hc c
      (MkSlotsT.onStemAddr_of_mem_stemSetCap h)
  rw [selCap_eq_some_iff honeY, selCap_eq_some_iff honeA]
  constructor
  · rintro ⟨h, hk⟩
    have hA := hmem.1 h
    exact ⟨hA, by rw [hk, hlen hA]⟩
  · rintro ⟨h, hk⟩
    exact ⟨hmem.2 h, by rw [hk, hlen h]⟩

end Class

end WaveTurbulence.Flower.MkSlotsS
