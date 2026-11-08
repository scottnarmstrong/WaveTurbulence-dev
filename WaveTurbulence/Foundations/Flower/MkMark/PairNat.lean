/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.CoordIso
public import WaveTurbulence.Foundations.RegStruct.LocalPairNaturality
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairAtSides

/-! # B2b MK-MARK: pairs across a coordinate correspondence

If the regular tree and its sign agree at every transported branch slot, and the regular couple and the orientation
agree at every transported leaf-pair slot (`PairData`), then the coordinate map sends pairs of `dec(S, D)` off the
replaced region to pairs of `dec(S', D')` (`PairData.pair_map`), by main's local pair naturality
(`chain_pairsAt_map_local`, `couple_pairsAt_map_local`). In particular the partner tree is preserved
(`PairData.pairTree`), the missing field of `CoordData.toOutIso`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

/-- Translation of the addresses below `a` to the addresses below `a'`. -/
def trAddr (a a' : Address w) (y : Address w) : Address w := addrExt a' (y.2.drop a.2.length)

theorem trAddr_respects (a a' : Address w) : RespectsAt (trAddr a a') a := by
  intro p
  simp [trAddr, addrExt]

theorem trAddr_self (a a' : Address w) : trAddr a a' a = a' := by
  simp [trAddr, addrExt]

/-- Two-root translation. -/
def trAddr2 (a a' b b' : Address w) (y : Address w) : Address w :=
  if AddrBelow a y then trAddr a a' y else trAddr b b' y

section Slots
variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G)
include hd

/-- Endpoints of a regular-tree pair are owned by its branch. -/
theorem chain_endpoint_owner (b : GBranch S.tree) (y : Address w)
    (hy : y ∈ leafAddresses ((D.tree b).plug (nodeSign S.sig b.1) .leaf) (inflatedPosition S D.tree b.toNode))
    (hyl : y.2 ∈ (G.tree y.1).leaves) : owner S D.tree y = b.toNode := by
  refine owner_eq_branch S D.tree (addrBelow_of_mem_leafAddresses hy) ?_
  intro hb
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨-, s, hs⟩ := hb
  have hs' : (D.tree b).lonePath ++ s = r := by
    simp only [addrExt, List.append_assoc] at hs
    exact List.append_cancel_left hs
  have hlone := lonePath_mem_leaves (D.tree b) (nodeSign S.sig b.1)
  have hs0 : s = [] := eq_nil_of_leaf_append _ hlone (by
    rw [hs']
    exact (TTree.mem_nodes_iff _ _).mpr (Or.inl hr))
  subst hs0
  simp only [List.append_nil] at hs'
  subst hs'
  have hbr := (D.coreBranch hS b).2
  change (D.corePosition b).2 ∈ (D.forest hS (D.corePosition b).1).branching at hbr
  rw [decodes_tree hd] at hbr
  exact TTree.not_mem_branching_of_mem_leaves _ hyl hbr

end Slots

/-- The first leaf of a source pair is positive, and the pair is the pair of its first leaf. -/
theorem firstLeaf_sign {S : Garden w} (hS : S.IsPlain) (p : SourcePair S) :
    nodeSign S.sig (p.firstLeaf hS).1 = 1 := by
  obtain ⟨ℓ, hℓ, he⟩ := Finset.mem_image.mp p.2
  have h1 : p.firstLeaf hS = ℓ := Subtype.ext (by
    show p.1.1 = ℓ.1
    rw [← he])
  rw [h1]
  exact (Finset.mem_filter.mp hℓ).2

/-- Slot data of a correspondence. -/
structure PairData {S S' : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {D' : ReconstructionData S'}
    {hS' : S'.IsPlain} (C : CoordData D hS D' hS') where
  νB : GBranch S.tree ≃ GBranch S'.tree
  hB : ∀ b, (νB b).toNode = C.ν b.toNode
  νL : GLeaf S.tree ≃ GLeaf S'.tree
  hL : ∀ l, (νL l).toNode = C.ν l.toNode
  treeEq : ∀ b : GBranch S.tree, b.toNode ∉ C.Rsk →
    D'.tree (νB b) = D.tree b ∧ nodeSign S'.sig (νB b).1 = nodeSign S.sig b.1
  leafEq : ∀ l : GLeaf S.tree, l.toNode ∉ C.Rsk →
    D'.couple (pairOfLeaf S' hS' (νL l)) = D.couple (pairOfLeaf S hS l) ∧
      nodeSign S'.sig (νL l).1 = nodeSign S.sig l.1 ∧ S'.pair (νL l) = νL (S.pair l)
  rskPair : ∀ l : GLeaf S.tree, l.toNode ∉ C.Rsk → (S.pair l).toNode ∉ C.Rsk

namespace PairData
variable {S S' : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {D' : ReconstructionData S'}
  {hS' : S'.IsPlain} {C : CoordData D hS D' hS'} (E : PairData C)
  {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden) (hd' : D'.Decodes hS' LG'.garden)
include hd hd'

/-- The map on the endpoints of a slot pair is a translation. -/
theorem map_eq_tr (y : Address w) (o : GNode S.tree) (ho : owner S D.tree y = o) :
    C.map y = trAddr (inflatedPosition S D.tree o) (inflatedPosition S' D'.tree (C.ν o)) y := by
  unfold CoordData.map trAddr localPath
  rw [ho]

include E in
/-- **Pair naturality.** A pair of `dec(S, D)` with an endpoint off the replaced region is carried to a pair of
`dec(S', D')`. -/
theorem pair_map (q : Pair w) (hq : q ∈ sourcePairs LG.garden)
    (hR : owner S D.tree q.1 ∉ C.Rsk) : (C.map q.1, C.map q.2) ∈ sourcePairs LG'.garden := by
  obtain ⟨ℓe, ℓe', hℓ1, hℓ2, -⟩ := sourcePairs_actual_endpoints LG.garden q hq
  have hqe1 : q.1.2 ∈ (LG.garden.tree q.1.1).leaves := by rw [← hℓ1]; exact ℓe.2
  have hqe2 : q.2.2 ∈ (LG.garden.tree q.2.1).leaves := by rw [← hℓ2]; exact ℓe'.2
  rw [← decodes_pairs hd, D.attachmentPairs_eq_blocks hS, Finset.mem_biUnion] at hq
  obtain ⟨slot, -, hslot⟩ := hq
  rw [← decodes_pairs hd', D'.attachmentPairs_eq_blocks hS', Finset.mem_biUnion]
  cases slot with
  | inr b =>
    have hq' : q ∈ (D.tree b).pairsAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode) :=
      List.mem_toFinset.mp hslot
    obtain ⟨e1, e2⟩ := chain_pair_endpoint_leaves (D.tree b) (nodeSign S.sig b.1) .leaf _ q hq'
    have o1 := chain_endpoint_owner D hS hd b q.1 e1 hqe1
    have o2 := chain_endpoint_owner D hS hd b q.2 e2 hqe2
    have hbR : b.toNode ∉ C.Rsk := by rw [← o1]; exact hR
    obtain ⟨ht, hσ⟩ := E.treeEq b hbR
    refine ⟨.inr (E.νB b), Finset.mem_univ _, List.mem_toFinset.mpr ?_⟩
    have hnat := chain_pairsAt_map_local (D.tree b)
      (trAddr (inflatedPosition S D.tree b.toNode) (inflatedPosition S' D'.tree (C.ν b.toNode)))
      (inflatedPosition S D.tree b.toNode) (trAddr_respects _ _) (nodeSign S.sig b.1)
    rw [trAddr_self] at hnat
    rw [map_eq_tr (C := C) hd hd' q.1 _ o1, map_eq_tr (C := C) hd hd' q.2 _ o2, ht, hσ, E.hB, hnat]
    exact List.mem_map.mpr ⟨q, hq', rfl⟩
  | inl p =>
    have hq' : q ∈ (D.couple p).pairsAt (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
        (inflatedPosition S D.tree (p.secondLeaf hS).toNode) := List.mem_toFinset.mp hslot
    obtain ⟨e1, e2⟩ := couple_pair_endpoint_leaves _ _ _ q hq'
    set f := p.firstLeaf hS
    set s := p.secondLeaf hS
    have hfs : S.pair f = s := pair_firstLeaf p
    have side : ∀ y ∈ leafAddresses (D.couple p).trees.1 (inflatedPosition S D.tree f.toNode) ∪
        leafAddresses (D.couple p).trees.2 (inflatedPosition S D.tree s.toNode),
        (AddrBelow (inflatedPosition S D.tree f.toNode) y ∧ owner S D.tree y = f.toNode) ∨
          (AddrBelow (inflatedPosition S D.tree s.toNode) y ∧ owner S D.tree y = s.toNode) := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact Or.inl ⟨addrBelow_of_mem_leafAddresses hy, owner_eq_leaf S D.tree (addrBelow_of_mem_leafAddresses hy)⟩
      · exact Or.inr ⟨addrBelow_of_mem_leafAddresses hy, owner_eq_leaf S D.tree (addrBelow_of_mem_leafAddresses hy)⟩
    have hne : f ≠ s := by
      intro h
      have := Comb.pair_ne_of_plain hS f
      rw [hfs] at this
      exact this h.symm
    -- `f` is not in the replaced set
    have hfR : f.toNode ∉ C.Rsk := by
      rcases side _ e1 with ⟨-, h⟩ | ⟨-, h⟩
      · rw [← h]; exact hR
      · have hsR : s.toNode ∉ C.Rsk := by rw [← h]; exact hR
        intro hf
        have := E.rskPair s hsR
        rw [← hfs, S.pair_pair] at this
        exact this hf
    obtain ⟨hc, hsg, hpr⟩ := E.leafEq f hfR
    have hsg' : nodeSign S'.sig (E.νL f).1 = 1 := by rw [hsg]; exact firstLeaf_sign hS p
    obtain ⟨hf1, hf2⟩ := pairOfLeaf_sides_pos S' hS' (E.νL f) hsg'
    have hpf : pairOfLeaf S hS f = p := pairOfLeaf_firstLeaf S hS p
    set a := inflatedPosition S D.tree f.toNode
    set b := inflatedPosition S D.tree s.toNode
    set a' := inflatedPosition S' D'.tree (C.ν f.toNode)
    set b' := inflatedPosition S' D'.tree (C.ν s.toNode)
    -- the two roots are incomparable
    have hab : ∀ y, AddrBelow a y → AddrBelow b y → False := by
      intro y ha hb
      have h1 := owner_eq_leaf S D.tree ha
      have h2 := owner_eq_leaf S D.tree hb
      exact hne (leaf_toNode_injective (h1.symm.trans h2))
    have hra : RespectsAt (trAddr2 a a' b b') a := by
      intro r
      unfold trAddr2
      rw [if_pos (addrBelow_addrExt a r), if_pos (addrBelow_refl a)]
      simp [trAddr, addrExt]
    have hrb : RespectsAt (trAddr2 a a' b b') b := by
      intro r
      unfold trAddr2
      rw [if_neg (fun h => hab _ h (addrBelow_addrExt b r)), if_neg (fun h => hab _ h (addrBelow_refl b))]
      simp [trAddr, addrExt]
    have hmap : ∀ y ∈ leafAddresses (D.couple p).trees.1 a ∪ leafAddresses (D.couple p).trees.2 b,
        C.map y = trAddr2 a a' b b' y := by
      intro y hy
      rcases side y hy with ⟨hb1, ho⟩ | ⟨hb1, ho⟩
      · rw [map_eq_tr (C := C) hd hd' y _ ho]
        unfold trAddr2
        rw [if_pos hb1]
      · rw [map_eq_tr (C := C) hd hd' y _ ho]
        unfold trAddr2
        rw [if_neg (fun h => hab _ h hb1)]
    refine ⟨.inl (pairOfLeaf S' hS' (E.νL f)), Finset.mem_univ _, List.mem_toFinset.mpr ?_⟩
    show (C.map q.1, C.map q.2) ∈ (D'.couple (pairOfLeaf S' hS' (E.νL f))).pairsAt
      (inflatedPosition S' D'.tree ((pairOfLeaf S' hS' (E.νL f)).firstLeaf hS').toNode)
      (inflatedPosition S' D'.tree ((pairOfLeaf S' hS' (E.νL f)).secondLeaf hS').toNode)
    have ha' : inflatedPosition S' D'.tree ((pairOfLeaf S' hS' (E.νL f)).firstLeaf hS').toNode = a' := by
      rw [hf1, E.hL]
    have hb' : inflatedPosition S' D'.tree ((pairOfLeaf S' hS' (E.νL f)).secondLeaf hS').toNode = b' := by
      rw [hf2, hpr, hfs, E.hL]
    rw [ha', hb', hc, hpf, hmap _ e1, hmap _ e2]
    have h1 : trAddr2 a a' b b' a = a' := by
      unfold trAddr2
      rw [if_pos (addrBelow_refl a)]
      exact trAddr_self a a'
    have h2 : trAddr2 a a' b b' b = b' := by
      unfold trAddr2
      rw [if_neg (fun h => hab _ h (addrBelow_refl b))]
      exact trAddr_self b b'
    have hnat := couple_pairsAt_map_local (D.couple p) (trAddr2 a a' b b') a b hra hrb
    rw [h1, h2] at hnat
    rw [hnat]
    exact List.mem_map.mpr ⟨q, hq', rfl⟩

omit E hd hd' in
/-- The coordinate map preserves tree indices. -/
theorem map_fst (y : Address w) : (C.map y).1 = y.1 := by
  show (inflatedPosition S' D'.tree (C.ν (owner S D.tree y))).1 = y.1
  rw [inflatedPosition_fst, C.tree, owner_fst]

omit hd hd' in
theorem partner_of_mem {G : Garden w} {x y : Address w} (hxy : (x, y) ∈ sourcePairs G) (hx : x.2 ∈ (G.tree x.1).leaves) :
    (G.pair ⟨x, hx⟩).1 = y := by
  obtain ⟨ℓ, ℓ', h1, h2, h3⟩ := sourcePairs_actual_endpoints G _ hxy
  have e : ℓ = ⟨x, hx⟩ := Subtype.ext h1
  rw [← e, h3]
  exact h2

omit hd hd' in
theorem partner_of_mem' {G : Garden w} {x y : Address w} (hxy : (x, y) ∈ sourcePairs G) (hy : y.2 ∈ (G.tree y.1).leaves) :
    (G.pair ⟨y, hy⟩).1 = x := by
  obtain ⟨ℓ, ℓ', h1, h2, h3⟩ := sourcePairs_actual_endpoints G _ hxy
  have e : ℓ' = ⟨y, hy⟩ := Subtype.ext h2
  rw [← e, ← h3, G.pair_pair]
  exact h1

include E in
/-- **Partner trees are preserved** (the `pairTree` field of `CoordData.toOutIso`). -/
theorem pairTree (z : Address w) (h : LeafAt LG z) (h' : LeafAt LG' (C.map z))
    (hR : z ∉ ownedBy S D.tree C.Rsk) :
    (LG'.garden.pair ⟨C.map z, h'⟩).1.1 = (LG.garden.pair ⟨z, h⟩).1.1 := by
  set ℓ : GLeaf LG.garden.tree := ⟨z, h⟩
  have hmem := sourcePairAt_mem LG.garden hd.1 ℓ
  have hR' : owner S D.tree z ∉ C.Rsk := hR
  by_cases hs : nodeSign LG.garden.sig ℓ.1 = 1
  · have e : sourcePairAt LG.garden ℓ = (z, (LG.garden.pair ℓ).1) := by simp [sourcePairAt, hs, ℓ]
    rw [e] at hmem
    have hm := E.pair_map hd hd' _ hmem hR'
    rw [partner_of_mem hm h', map_fst (C := C)]
  · have e : sourcePairAt LG.garden ℓ = ((LG.garden.pair ℓ).1, z) := by simp [sourcePairAt, hs, ℓ]
    rw [e] at hmem
    have hpo : owner S D.tree (LG.garden.pair ℓ).1 ∉ C.Rsk := by
      rcases owner_pair hd ℓ with he | ⟨l, hl1, hl2⟩
      · rw [← he]; exact hR'
      · rw [← hl2]
        exact E.rskPair l (by rw [hl1]; exact hR')
    have hm := E.pair_map hd hd' _ hmem hpo
    rw [partner_of_mem' hm h', map_fst (C := C)]

omit hd hd' in
/-- The reverse slot data. -/
def symm : PairData C.symm where
  νB := E.νB.symm
  hB b' := by
    apply C.ν.injective
    show C.ν (E.νB.symm b').toNode = C.ν (C.ν.symm b'.toNode)
    rw [← E.hB, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  νL := E.νL.symm
  hL l' := by
    apply C.ν.injective
    show C.ν (E.νL.symm l').toNode = C.ν (C.ν.symm l'.toNode)
    rw [← E.hL, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  treeEq b' hb' := by
    have hb : (E.νB.symm b').toNode ∉ C.Rsk := by
      intro h
      apply hb'
      have := (C.rsk _).mpr h
      rwa [← E.hB, Equiv.apply_symm_apply] at this
    obtain ⟨h1, h2⟩ := E.treeEq _ hb
    rw [Equiv.apply_symm_apply] at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  leafEq l' hl' := by
    have hl : (E.νL.symm l').toNode ∉ C.Rsk := by
      intro h
      apply hl'
      have := (C.rsk _).mpr h
      rwa [← E.hL, Equiv.apply_symm_apply] at this
    obtain ⟨h1, h2, h3⟩ := E.leafEq _ hl
    rw [Equiv.apply_symm_apply] at h1 h2 h3
    refine ⟨h1.symm, h2.symm, ?_⟩
    rw [h3, Equiv.symm_apply_apply]
  rskPair l' hl' := by
    have hl : (E.νL.symm l').toNode ∉ C.Rsk := by
      intro h
      apply hl'
      have := (C.rsk _).mpr h
      rwa [← E.hL, Equiv.apply_symm_apply] at this
    have hp := E.rskPair _ hl
    have h3 := (E.leafEq _ hl).2.2
    rw [Equiv.apply_symm_apply] at h3
    intro h
    apply hp
    rw [← C.rsk, ← E.hL, ← h3]
    exact h

end PairData

end WaveTurbulence.Flower.MkMark
