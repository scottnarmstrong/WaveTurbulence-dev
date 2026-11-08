/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.CoreW2
public import WaveTurbulence.Foundations.Flower.MkSlots.IntCapT
public import WaveTurbulence.Foundations.Flower.MkSlots.IntAsm1

/-! # B3s-HELPER7 WP7 (part 3): the depth of the capped flowers of a reconstruction

The selected vertex of tree `j` exists iff the capped stem of tree `j` reaches depth `kSel j` (one capped flower per
tree): **`exists_stem_depth_iff`** — a stem branch at depth `k` exists iff the capped flower `ℓ` of tree `j` has
`k + 2 ≤ |ℓ|` (the stem is the set of proper ancestors of `ℓ` other than its parent) — and **`selCap_isSome_iff`**.

On the reconstruction of a skeleton with a splice shape `Φ : SpliceShape blk Gsb` (single-leaf cap trees), the capped
flowers are read inside the native couples of the `Gsb` pairs (**`exists_capFlower_iff`**): for a `Gsb` pair `q`
(skeleton pair `cwPair q`, main's `iota`), with the layered native couple `cwN q`, the tree `cwTr q c` and the depth
`cwDp q c` of its root of side `c`, a capped flower of tree `j` at depth `≥ k + 2` is a couple leaf `l` that is a
capped flower of `cwN q` read through the root trees (α's `capT_IsFl`) with `cwTr q l.1 = j` and
`k + 2 ≤ cwDp q l.1 + |l|` (`FlowerAtDepth`).

The root depth of the flower side (**`attach_depth`**, under γ's retention `StemRet`): it is `0` at a `Gsb` root,
and `|core (Φ.br c)| + 1` with the core of the `Gsb` parent `c` on the capped stem otherwise (through a hinge, the
flower hangs at the excluded child of the upper joint: a lower crown child would put the lower joint on the stem,
`not_lowerCrown_leaf`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs
open WaveTurbulence.VineB (SpliceShape Ret Disj crownSet regionOf)
open WaveTurbulence.RedSplice (CLBlock)
open WaveTurbulence.Flower.MkSlots.IntCapT (capT_IsFl)
open WaveTurbulence.Flower.MkSlotsT (OnStemAddr StemRet onStemAddr_of_addrBelow)

namespace WaveTurbulence.Flower.MkSlotsI

variable {w : ℕ}

/-! ## Stem depths and selected vertices -/

section Depth

variable {LG : LayeredGarden w} {J : Finset (Fin w)}

/-- **A stem branch of tree `j` at depth `k` exists iff the capped flower of tree `j` has depth `≥ k + 2`.** -/
theorem exists_stem_depth_iff (hone : MkSlotsS.OneFlower LG J) (j : Fin w) (k : ℕ) :
    (∃ b ∈ stemSetCap LG J j, b.1.2.length = k) ↔
      ∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.1.1 = j ∧ k + 2 ≤ ℓ.1.2.length := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨hbj, ⟨ℓ, hℓ, hd⟩, hncfp⟩ := MkSlotsS.mem_stemSetCap_iff'.1 hb
    obtain ⟨s, hs⟩ := hd.2
    refine ⟨ℓ, hℓ, hd.1.symm.trans hbj, ?_⟩
    have hs' : b.1.2 ++ s = ℓ.1.2 := hs
    have hlen : ℓ.1.2.length = b.1.2.length + s.length := by
      rw [← hs', List.length_append]
    rcases s with _ | ⟨i, _ | ⟨i', s⟩⟩
    · exfalso
      have hbr : ℓ.1.2 ∈ (LG.garden.tree ℓ.1.1).branching := by
        have h1 : b.1.2 = ℓ.1.2 := by
          have h0 := hs
          rw [List.append_nil] at h0
          exact h0
        have h2 : b.1.1 = ℓ.1.1 := hd.1
        have := b.2
        rw [h1, h2] at this
        exact this
      exact Comb.TreePath.not_mem_branching_of_mem_leaves _ ℓ.2 hbr
    · exact absurd ⟨ℓ, hℓ, hd.1.symm, i, hs.symm⟩ hncfp
    · simp only [List.length_cons] at hlen
      omega
  · rintro ⟨ℓ, hℓ, hj, hk⟩
    have hlt : k < ℓ.1.2.length := by omega
    obtain ⟨i, r, hdr⟩ : ∃ i r, ℓ.1.2.drop k = i :: r := by
      cases h : ℓ.1.2.drop k with
      | nil =>
        have := congrArg List.length h
        simp only [List.length_drop, List.length_nil] at this
        omega
      | cons i r => exact ⟨i, r, rfl⟩
    have hsplit : ℓ.1.2.take k ++ (i :: r) = ℓ.1.2 := by rw [← hdr, List.take_append_drop]
    have hnode : ℓ.1.2.take k ++ [i] ∈ (LG.garden.tree ℓ.1.1).nodes :=
      TTree.mem_nodes_of_prefix _ (TTree.leaves_subset_nodes _ ℓ.2)
        ⟨r, by rw [List.append_assoc, List.singleton_append, hsplit]⟩
    have hbr := TTree.branching_of_append_mem _ hnode
    have hlen : (ℓ.1.2.take k).length = k := by rw [List.length_take]; omega
    refine ⟨⟨(ℓ.1.1, ℓ.1.2.take k), hbr⟩, MkSlotsS.mem_stemSetCap_iff'.2 ⟨hj, ⟨ℓ, hℓ, rfl, List.take_prefix k _⟩,
      ?_⟩, hlen⟩
    rintro ⟨ℓ', hℓ', h1, i', h2⟩
    have he : ℓ' = ℓ := hone ℓ' ℓ hℓ' hℓ h1
    subst he
    have := congrArg List.length h2
    simp only [List.length_append, List.length_singleton] at this
    have e : (⟨(ℓ'.1.1, ℓ'.1.2.take k), hbr⟩ : GBranch LG.garden.tree).1.2.length = k := hlen
    omega

/-- **The selected vertex of tree `j` exists iff a selection is requested in tree `j` and the capped flower of tree `j`
is deep enough.** -/
theorem selCap_isSome_iff (hone : MkSlotsS.OneFlower LG J) (kSel : Fin w → Option ℕ) (j : Fin w) :
    (selCap LG J kSel j).isSome ↔
      ∃ k, kSel j = some k ∧ ∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.1.1 = j ∧ k + 2 ≤ ℓ.1.2.length := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨hbs, hk⟩ := (MkSlotsS.selCap_eq_some_iff hone kSel j b).1 hb
    exact ⟨_, hk, (exists_stem_depth_iff hone j _).1 ⟨b, hbs, rfl⟩⟩
  · rintro ⟨k, hk, h⟩
    obtain ⟨b, hbs, rfl⟩ := (exists_stem_depth_iff hone j k).2 h
    rw [(MkSlotsS.selCap_eq_some_iff hone kSel j b).2 ⟨hbs, hk⟩]
    rfl

end Depth

/-! ## The flower in a native couple -/

/-- A capped flower of a layered couple `N` (root trees `ri`) of tree `j` whose depth in the ambient garden (root depths
`rd`) is at least `k + 2`. -/
def FlowerAtDepth (N : LayeredGarden 2) (ri : Fin 2 → Fin w) (rd : Fin 2 → ℕ) (J : Finset (Fin w)) (j : Fin w)
    (k : ℕ) : Prop :=
  ∃ l : GLeaf N.garden.tree, capT_IsFl N ri J l ∧ ri l.1.1 = j ∧ k + 2 ≤ rd l.1.1 + l.1.2.length

/-- `FlowerAtDepth` is read on equal couples, equal root trees, and root depths equal on the flower sides. -/
theorem flowerAtDepth_congr {N N' : LayeredGarden 2} (hN : N = N') {ri ri' : Fin 2 → Fin w} (hri : ri = ri')
    {rd rd' : Fin 2 → ℕ} {J : Finset (Fin w)}
    (hrd : ∀ l : GLeaf N.garden.tree, capT_IsFl N ri J l → rd l.1.1 = rd' l.1.1) (j : Fin w) (k : ℕ) :
    FlowerAtDepth N ri rd J j k ↔ FlowerAtDepth N' ri' rd' J j k := by
  subst hN hri
  unfold FlowerAtDepth
  exact exists_congr fun l => ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by rw [← hrd l h1]; exact h3⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by rw [hrd l h1]; exact h3⟩⟩

section Shape

variable {S Gsb : Garden w} {ι : Type} [Fintype ι] [DecidableEq ι] {blk : ι → CLBlock S}
  (Φ : SpliceShape blk Gsb) (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (hG : Gsb.IsPlain)

/-- The side leaves of a `Gsb` pair. -/
def cwSide (q : SourcePair Gsb) (c : Fin 2) : GLeaf Gsb.tree := ![q.firstLeaf hG, q.secondLeaf hG] c

/-- The skeleton pair of a `Gsb` pair (main's `iota`). -/
abbrev cwPair (q : SourcePair Gsb) : SourcePair S := pairOfLeaf S hS (Φ.leaf (q.firstLeaf hG))

/-- The layered native couple of a `Gsb` pair. -/
abbrev cwN (q : SourcePair Gsb) : LayeredGarden 2 := nativeCoupleLayered D hS layer hLayer (cwPair Φ hS hG q)

/-- The tree of the root of side `c` of the native couple of a `Gsb` pair. -/
def cwTr (q : SourcePair Gsb) (c : Fin 2) : Fin w := ((nativeCoupleForest D hS (cwPair Φ hS hG q)).root c).1.1

/-- The depth of the root of side `c` of the native couple of a `Gsb` pair. -/
def cwDp (q : SourcePair Gsb) (c : Fin 2) : ℕ := ((nativeCoupleForest D hS (cwPair Φ hS hG q)).root c).1.2.length

/-- The root of side `c` of the native couple is the attachment address of the image of the side leaf. -/
theorem cwRoot_val (q : SourcePair Gsb) (c : Fin 2) :
    ((nativeCoupleForest D hS (cwPair Φ hS hG q)).root c).1 =
      inflatedPosition S D.tree (Φ.leaf (cwSide hG q c)).toNode := by
  fin_cases c
  · show inflatedPosition S D.tree ((cwPair Φ hS hG q).firstLeaf hS).toNode = _
    rw [Φ.iota_first hS hG q]
    rfl
  · show inflatedPosition S D.tree ((cwPair Φ hS hG q).secondLeaf hS).toNode = _
    rw [Φ.iota_second hS hG q]
    rfl

theorem cwTr_eq (q : SourcePair Gsb) (c : Fin 2) : cwTr Φ D hS hG q c = (cwSide hG q c).1.1 := by
  unfold cwTr
  rw [cwRoot_val, MkMark.inflatedPosition_fst, Φ.leaf_node, Φ.tree_eq]
  rfl

theorem cwDp_eq (q : SourcePair Gsb) (c : Fin 2) :
    cwDp Φ D hS hG q c = (inflatedPosition S D.tree (Φ.leaf (cwSide hG q c)).toNode).2.length := by
  unfold cwDp
  rw [cwRoot_val]

/-- The other side leaf is the partner. -/
theorem cwSide_pair (q : SourcePair Gsb) (c c' : Fin 2) (hcc : c ≠ c') :
    cwSide hG q c' = Gsb.pair (cwSide hG q c) := by
  have h2 : Gsb.pair (q.firstLeaf hG) = q.secondLeaf hG := sourcePair_partner Gsb _ _ (Or.inl q.2)
  fin_cases c <;> fin_cases c'
  · exact absurd rfl hcc
  · show q.secondLeaf hG = Gsb.pair (q.firstLeaf hG)
    exact h2.symm
  · show q.firstLeaf hG = Gsb.pair (q.secondLeaf hG)
    rw [← h2, Gsb.pair_pair]
  · exact absurd rfl hcc

variable {J : Finset (Fin w)} (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)

include hcap in
/-- **The capped flowers lie in the native couples of the `Gsb` pairs.** -/
theorem exists_capFlower_iff (j : Fin w) (k : ℕ) :
    (∃ ℓ : GLeaf (layeredReconstruction D hS layer hLayer).garden.tree,
        IsCapFlower (layeredReconstruction D hS layer hLayer) J ℓ ∧ ℓ.1.1 = j ∧ k + 2 ≤ ℓ.1.2.length) ↔
      ∃ q : SourcePair Gsb, FlowerAtDepth (cwN Φ D hS layer hLayer hG q) (cwTr Φ D hS hG q) (cwDp Φ D hS hG q) J j k := by
  constructor
  · rintro ⟨ℓ, hℓ, hj, hk⟩
    obtain ⟨m, hmJ, hm2, hown⟩ := MkSlotsT.flower_owner Φ D hS layer hLayer hcap (ℓ := ℓ.1) ⟨ℓ.2, hℓ.1, hℓ.2⟩
    set q := pairOfLeaf Gsb hG (Gsb.pair m)
    set E := nativeCoupleForest D hS (cwPair Φ hS hG q)
    have hbelow : AddrBelow (inflatedPosition S D.tree (Φ.leaf (Gsb.pair m)).toNode) ℓ.1 :=
      ((MkMark.mem_ownRegion_iff S D.tree).2 hown).1
    obtain ⟨c, hc⟩ : ∃ c, cwSide hG q c = Gsb.pair m := by
      rcases MkSlots.IntRest.pairOfLeaf_sides hG (Gsb.pair m) with ⟨e1, -⟩ | ⟨-, e2⟩
      · exact ⟨0, e1⟩
      · exact ⟨1, e2⟩
    have hmem : ℓ ∈ E.leafSet := by
      refine (Comb.RootedSubforest.mem_leafSet_iff (G := D.garden hS) E ℓ).2 ⟨c, ?_⟩
      have hr := cwRoot_val Φ D hS hG q c
      rw [hc] at hr
      exact ⟨by rw [hr]; exact hbelow.1, by rw [hr]; exact hbelow.2⟩
    have hmem' : ℓ ∈ (Finset.univ : Finset (GLeaf E.shape)).image E.leafEmbedding := hmem
    obtain ⟨l, -, hl⟩ := Finset.mem_image.1 hmem'
    refine ⟨q, l, ?_, ?_, ?_⟩
    · exact (MkSlots.IntCapT.capT_isCapFlower_iffE (layeredReconstruction D hS layer hLayer) E
        (nativeCoupleForest_closed D hS _) J (cwTr Φ D hS hG q) (fun _ => rfl) l).1
          (Eq.mpr (congrArg (IsCapFlower (layeredReconstruction D hS layer hLayer) J) hl) hℓ)
    · have e2 : (E.leafEmbedding l).1.1 = ℓ.1.1 := congrArg (fun x => x.1.1) hl
      exact e2.trans hj
    · have e3 : (E.leafEmbedding l).1.2 = ℓ.1.2 := congrArg (fun x => x.1.2) hl
      have e : (E.leafEmbedding l).1.2 = (E.root l.1.1).1.2 ++ l.1.2 := rfl
      rw [e3] at e
      rw [e, List.length_append] at hk
      exact hk
  · rintro ⟨q, l, hl, hj, hk⟩
    set E := nativeCoupleForest D hS (cwPair Φ hS hG q)
    refine ⟨E.leafEmbedding l,
      (MkSlots.IntCapT.capT_isCapFlower_iffE (layeredReconstruction D hS layer hLayer) E
        (nativeCoupleForest_closed D hS _) J (cwTr Φ D hS hG q) (fun _ => rfl) l).2 hl, hj, ?_⟩
    have e : (E.leafEmbedding l).1.2 = (E.root l.1.1).1.2 ++ l.1.2 := rfl
    rw [e, List.length_append]
    exact hk

variable (hR : StemRet S D.tree blk (layeredReconstruction D hS layer hLayer) J)

omit [Fintype ι] [DecidableEq ι] in
include hR in
/-- A lower crown child of a unit never has its attachment address on the capped stem. -/
theorem not_lowerCrown_leaf (j : ι) (i : Fin 3) (x : GNode S.tree) (hx : x = (blk j).lower.child i)
    (hst : OnStemAddr (layeredReconstruction D hS layer hLayer) J (inflatedPosition S D.tree x)) : False := by
  subst hx
  have hcb : AddrBelow (D.corePosition (blk j).lower) (inflatedPosition S D.tree ((blk j).lower.child i)) := by
    rw [inflatedPosition_child]
    unfold ReconstructionData.corePosition
    exact ⟨rfl, ⟨[i], by simp [addrExt, List.append_assoc]⟩⟩
  have heq := hR.upper j _ (onStemAddr_of_addrBelow hst hcb) (blk j).lower
    (MkSlotsT.owner_corePosition D (blk j).lower) (blk j).isBlock.2.2.1
  exact (blk j).isBlock.2.2.2.1 heq.symm

omit [Fintype ι] [DecidableEq ι] in
/-- The attachment address of a `Gsb` root leaf is a root. -/
theorem attach_depth_root (ℓ' : GLeaf Gsb.tree) (h : ℓ'.1.2 = []) :
    (inflatedPosition S D.tree (Φ.leaf ℓ').toNode).2.length = 0 := by
  have hr : (Φ.leaf ℓ').toNode = GNode.root S.tree ℓ'.1.1 := MkSlotsT.leaf_root_node Φ ℓ' h
  rw [hr, inflatedPosition_root]
  rfl

include hcap hR in
/-- **The attachment depth of the flower side.** For a `Gsb` leaf `ℓ'` off the cap trees whose partner is a cap root
and which is not a root, the core of its `Gsb` parent `c` is on the capped stem and the attachment address of the
image of `ℓ'` has depth `|core (Φ.br c)| + 1`. -/
theorem attach_depth (ℓ' : GLeaf Gsb.tree) (hJ : ℓ'.1.1 ∉ J) (hJ' : (Gsb.pair ℓ').1.1 ∈ J) (h : ℓ'.1.2 ≠ []) :
    OnStemAddr (layeredReconstruction D hS layer hLayer) J (D.corePosition (Φ.br (ℓ'.toNode.parent h))) ∧
      (inflatedPosition S D.tree (Φ.leaf ℓ').toNode).2.length =
        (D.corePosition (Φ.br (ℓ'.toNode.parent h))).2.length + 1 := by
  set c := ℓ'.toNode.parent h
  have hci : c.child (ℓ'.1.2.getLast h) = ℓ'.toNode := child_parent ℓ'.toNode h
  have hσ : (Φ.leaf ℓ').toNode = Φ.node (c.child (ℓ'.1.2.getLast h)) := by rw [Φ.leaf_node, hci]
  -- the cap root partner is a `Gsb` root
  have hm2 : (Gsb.pair ℓ').1.2 = [] := by
    have hl : Gsb.tree (Gsb.pair ℓ').1.1 = TTree.leaf :=
      MkSlots.IntAsm.shape_tree_leaf Φ (MkSlots.IntAsm.skel_tree_leaf D hS (hcap _ hJ'))
    have := (Gsb.pair ℓ').2
    rw [hl] at this
    simpa [TTree.leaves] using this
  -- the flower owned by the image of `ℓ'`: the attachment address of `ℓ'` is on the stem
  obtain ⟨fl, hfl, hown⟩ := MkSlotsT.flower_exists Φ D hS layer hLayer hcap (Gsb.pair ℓ') hJ' hm2
    (by rw [Gsb.pair_pair]; exact hJ)
  rw [Gsb.pair_pair] at hown
  have hstσ : OnStemAddr (layeredReconstruction D hS layer hLayer) J
      (inflatedPosition S D.tree (Φ.leaf ℓ').toNode) := ⟨fl, hfl, ((MkMark.mem_ownRegion_iff S D.tree).2 hown).1⟩
  -- the image of `ℓ'` is a skeleton child of `Φ.br c`
  obtain ⟨i', hi'⟩ : ∃ i', (Φ.leaf ℓ').toNode = (Φ.br c).child i' := by
    by_cases hup : ∀ j, Φ.br c ≠ (blk j).upper
    · exact ⟨_, by rw [hσ, Φ.child c _ hup]⟩
    · push Not at hup
      obtain ⟨j, hj⟩ := hup
      have hcr := Φ.crown c j hj (ℓ'.1.2.getLast h)
      rw [← hσ] at hcr
      rcases hcr with h1 | h1 | h1
      · exact ⟨_, by rw [h1, hj]⟩
      · exact (not_lowerCrown_leaf D hS layer hLayer hR j _ _ h1 hstσ).elim
      · exact (not_lowerCrown_leaf D hS layer hLayer hR j _ _ h1 hstσ).elim
  have hpos : inflatedPosition S D.tree (Φ.leaf ℓ').toNode =
      addrExt (inflatedPosition S D.tree (Φ.br c).toNode) ((D.tree (Φ.br c)).lonePath ++ [i']) := by
    rw [hi', inflatedPosition_child]
  have hcb : AddrBelow (D.corePosition (Φ.br c)) (inflatedPosition S D.tree (Φ.leaf ℓ').toNode) := by
    rw [hpos]
    unfold ReconstructionData.corePosition
    exact ⟨rfl, ⟨[i'], by simp [addrExt, List.append_assoc]⟩⟩
  refine ⟨onStemAddr_of_addrBelow hstσ hcb, ?_⟩
  rw [hpos]
  show ((inflatedPosition S D.tree (Φ.br c).toNode).2 ++ ((D.tree (Φ.br c)).lonePath ++ [i'])).length =
    ((inflatedPosition S D.tree (Φ.br c).toNode).2 ++ (D.tree (Φ.br c)).lonePath).length + 1
  simp only [List.length_append, List.length_singleton]
  omega

end Shape

end WaveTurbulence.Flower.MkSlotsI
