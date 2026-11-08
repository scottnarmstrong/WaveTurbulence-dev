/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.Owner
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedCoreBranches
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CodeEndpointLeaves
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPairBlocks
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PairPartition
public import WaveTurbulence.Foundations.RegStruct.DecodedLeaves

/-! # B2b MK-MARK: owners in a decoded garden

For a garden `G` decoded from a skeleton `S` with replacement data `D` (`D.Decodes hS G`, main
`SkeletonDraft/ReconstructionForest.lean`):

* an address below the inflated position of a skeleton leaf is owned by that leaf (`owner_eq_leaf`);
* an address below the inflated position of a skeleton branch `b` and not below its core position is owned by
  `b` (`owner_eq_branch`);
* **the two leaves of a pair of `G` are owned by one skeleton node, or by two paired skeleton leaves**
  (`owner_pair`): a pair of `G` is an internal pair of one regular tree, or a pair of one regular couple sitting
  on a skeleton leaf pair (main `attachmentPairs_eq_blocks`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

/-! ## Tree facts -/

/-- Node sets are prefix closed. -/
theorem prefix_mem_nodes (t : TTree) {p : TTree.Path} : ∀ {s : TTree.Path}, p ++ s ∈ t.nodes → p ∈ t.nodes := by
  intro s
  induction s using List.reverseRecOn with
  | nil => intro h; simpa using h
  | append_singleton s i ih =>
    intro h
    apply ih
    have h2 := TTree.dropLast_mem_nodes t h
    rwa [← List.append_assoc, List.dropLast_concat] at h2

/-- Nothing lies strictly below a leaf. -/
theorem eq_nil_of_leaf_append (t : TTree) {p s : TTree.Path} (hl : p ∈ t.leaves) (h : p ++ s ∈ t.nodes) :
    s = [] := by
  cases s with
  | nil => rfl
  | cons i s =>
    exfalso
    have h1 : p ++ [i] ∈ t.nodes := prefix_mem_nodes t (s := s) (by simpa using h)
    exact TTree.not_mem_branching_of_mem_leaves t hl (TTree.branching_of_append_mem t h1)

theorem addrBelow_addrExt (a : Address w) (q : TTree.Path) : AddrBelow a (addrExt a q) :=
  ⟨rfl, List.prefix_append _ _⟩

theorem addrBelow_iff_below {a z : Address w} : AddrBelow a z ↔ Below a z :=
  ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩

/-! ## Owners of addresses below a slot -/

section Slots
variable (S : Garden w) (X : GBranch S.tree → RegChain)

/-- The own region of a skeleton leaf is everything below its inflated position. -/
theorem owner_eq_leaf {l : GLeaf S.tree} {y : Address w}
    (hy : AddrBelow (inflatedPosition S X l.toNode) y) : owner S X y = l.toNode := by
  rw [← mem_ownRegion_iff]
  refine ⟨hy, fun c hc hne => ?_⟩
  exfalso
  apply hne
  obtain ⟨h1, r, hr⟩ := hc
  have hl : l.1.2 ∈ (S.tree c.1.1).leaves := by
    have e : l.toNode.1.1 = l.1.1 := rfl
    rw [← h1, e]
    exact l.2
  have hr' : r = [] := eq_nil_of_leaf_append (S.tree c.1.1) hl (by
    have e : l.toNode.1.2 = l.1.2 := rfl
    rw [← e, hr]
    exact c.2)
  subst hr'
  exact gnode_eq_of_val h1.symm (by simpa using hr.symm)

/-- An address below the inflated position of `b` and not below its core position is owned by `b`. -/
theorem owner_eq_branch {b : GBranch S.tree} {y : Address w}
    (hy : AddrBelow (inflatedPosition S X b.toNode) y)
    (hn : ¬ AddrBelow (addrExt (inflatedPosition S X b.toNode) (X b).lonePath) y) :
    owner S X y = b.toNode := by
  rw [← mem_ownRegion_iff]
  refine ⟨hy, fun c hc hne hcy => hn ?_⟩
  obtain ⟨h1, r, hr⟩ := hc
  cases r with
  | nil => exact absurd (gnode_eq_of_val h1.symm (by simpa using hr.symm)) hne
  | cons i r =>
    have hci : (b.child i).IsDesc c := ⟨h1, r, by
      show b.1.2 ++ [i] ++ r = c.1.2
      rw [← hr]
      simp only [List.append_assoc, List.singleton_append]
      rfl⟩
    have h2 := addrBelow_inflatedPosition S X hci
    rw [inflatedPosition_child] at h2
    have h3 : AddrBelow (addrExt (inflatedPosition S X b.toNode) (X b).lonePath)
        (addrExt (inflatedPosition S X b.toNode) ((X b).lonePath ++ [i])) := by
      refine ⟨rfl, ?_⟩
      show (inflatedPosition S X b.toNode).2 ++ (X b).lonePath <+:
        (inflatedPosition S X b.toNode).2 ++ ((X b).lonePath ++ [i])
      rw [← List.append_assoc]
      exact List.prefix_append _ _
    exact addrBelow_trans h3 (addrBelow_trans h2 hcy)

end Slots

/-! ## The decoded garden -/

section Decodes
variable {S : Garden w} {hS : S.IsPlain} {D : ReconstructionData S} {G : Garden w}

theorem decodes_tree (hd : D.Decodes hS G) : D.forest hS = G.tree := congrArg Raw.tree hd.2

theorem decodes_pairs (hd : D.Decodes hS G) : D.attachmentPairs hS = sourcePairs G := congrArg Raw.pairs hd.2

theorem decodes_sig (hd : D.Decodes hS G) : S.sig = G.sig := congrArg Raw.sig hd.2

/-- The owner relation of a pair: one owner, or two paired skeleton leaves. -/
def PairedOwners (S : Garden w) (o o' : GNode S.tree) : Prop :=
  o = o' ∨ ∃ l : GLeaf S.tree, l.toNode = o ∧ (S.pair l).toNode = o'

theorem PairedOwners.symm {S : Garden w} {o o' : GNode S.tree} (h : PairedOwners S o o') :
    PairedOwners S o' o := by
  rcases h with h | ⟨l, h1, h2⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨S.pair l, h2, by rw [S.pair_pair]; exact h1⟩

/-- The first leaf of a source pair is paired with its second leaf. -/
theorem pair_firstLeaf (p : SourcePair S) : S.pair (p.firstLeaf hS) = p.secondLeaf hS := by
  obtain ⟨ℓ, -, he⟩ := Finset.mem_image.mp p.2
  have h1 : p.firstLeaf hS = ℓ := Subtype.ext (by
    show p.1.1 = ℓ.1
    rw [← he])
  apply Subtype.ext
  show (S.pair (p.firstLeaf hS)).1 = p.1.2
  rw [h1, ← he]

/-- Leaf addresses of a regular tree attached at `a` are below `a`. -/
theorem addrBelow_of_mem_leafAddresses {t : TTree} {a z : Address w} (hz : z ∈ leafAddresses t a) :
    AddrBelow a z := by
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hz
  exact addrBelow_addrExt a q

/-- The lone path of a chain is a leaf of the chain plugged with a leaf. -/
theorem lonePath_mem_leaves (X : RegChain) (ζ : ℤˣ) : X.lonePath ∈ (X.plug ζ .leaf).leaves := by
  have h := chain_leafAddresses (w := 1) X ζ .leaf ((0 : Fin 1), [])
  have hm : addrExt ((0 : Fin 1), ([] : TTree.Path)) X.lonePath ∈
      leafAddresses (X.plug ζ .leaf) ((0 : Fin 1), []) := by
    rw [h]
    apply Finset.mem_union_right
    rw [leafAddresses_leaf]
    exact Finset.mem_singleton_self _
  obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hm
  have : q = X.lonePath := by simpa [addrExt] using he
  rw [← this]
  exact hq

/-- A pair of a replacement slot has paired owners (given that both endpoints are leaves of `G`). -/
theorem pairedOwners_of_slot (hd : D.Decodes hS G) (slot : ReplacementSlot S) (q : Pair w)
    (hq : q ∈ D.pairBlock hS slot) (h1 : q.1.2 ∈ (G.tree q.1.1).leaves) (h2 : q.2.2 ∈ (G.tree q.2.1).leaves) :
    PairedOwners S (owner S D.tree q.1) (owner S D.tree q.2) := by
  cases slot with
  | inl p =>
    have hq' : q ∈ (D.couple p).pairsAt (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
        (inflatedPosition S D.tree (p.secondLeaf hS).toNode) := List.mem_toFinset.mp hq
    obtain ⟨e1, e2⟩ := couple_pair_endpoint_leaves _ _ _ q hq'
    have side : ∀ z ∈ leafAddresses (D.couple p).trees.1 (inflatedPosition S D.tree (p.firstLeaf hS).toNode) ∪
        leafAddresses (D.couple p).trees.2 (inflatedPosition S D.tree (p.secondLeaf hS).toNode),
        owner S D.tree z = (p.firstLeaf hS).toNode ∨ owner S D.tree z = (p.secondLeaf hS).toNode := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact Or.inl (owner_eq_leaf S D.tree (addrBelow_of_mem_leafAddresses hz))
      · exact Or.inr (owner_eq_leaf S D.tree (addrBelow_of_mem_leafAddresses hz))
    have hp1 := pair_firstLeaf (hS := hS) p
    have hp2 : S.pair (p.secondLeaf hS) = p.firstLeaf hS := by rw [← hp1, S.pair_pair]
    rcases side _ e1 with a1 | a1 <;> rcases side _ e2 with a2 | a2
    · exact Or.inl (a1.trans a2.symm)
    · exact Or.inr ⟨p.firstLeaf hS, a1.symm, by rw [hp1, a2]⟩
    · exact Or.inr ⟨p.secondLeaf hS, a1.symm, by rw [hp2, a2]⟩
    · exact Or.inl (a1.trans a2.symm)
  | inr b =>
    have hq' : q ∈ (D.tree b).pairsAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode) :=
      List.mem_toFinset.mp hq
    obtain ⟨e1, e2⟩ := chain_pair_endpoint_leaves (D.tree b) (nodeSign S.sig b.1) .leaf _ q hq'
    have own : ∀ z, z.2 ∈ (G.tree z.1).leaves →
        z ∈ leafAddresses ((D.tree b).plug (nodeSign S.sig b.1) .leaf) (inflatedPosition S D.tree b.toNode) →
        owner S D.tree z = b.toNode := by
      intro z hzl hz
      refine owner_eq_branch S D.tree (addrBelow_of_mem_leafAddresses hz) ?_
      intro hb
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
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
      exact TTree.not_mem_branching_of_mem_leaves _ hzl hbr
    have o1 := own q.1 h1 e1
    have o2 := own q.2 h2 e2
    exact Or.inl (o1.trans o2.symm)

/-- **The two leaves of a pair of the decoded garden have paired owners.** -/
theorem owner_pair (hd : D.Decodes hS G) (ℓ : GLeaf G.tree) :
    PairedOwners S (owner S D.tree ℓ.1) (owner S D.tree (G.pair ℓ).1) := by
  have hmem : sourcePairAt G ℓ ∈ D.attachmentPairs hS := by
    rw [decodes_pairs hd]
    exact sourcePairAt_mem G hd.1 ℓ
  rw [D.attachmentPairs_eq_blocks hS, Finset.mem_biUnion] at hmem
  obtain ⟨slot, -, hslot⟩ := hmem
  by_cases hs : nodeSign G.sig ℓ.1 = 1
  · have e : sourcePairAt G ℓ = (ℓ.1, (G.pair ℓ).1) := by simp [sourcePairAt, hs]
    rw [e] at hslot
    exact pairedOwners_of_slot hd slot _ hslot ℓ.2 (G.pair ℓ).2
  · have e : sourcePairAt G ℓ = ((G.pair ℓ).1, ℓ.1) := by simp [sourcePairAt, hs]
    rw [e] at hslot
    exact (pairedOwners_of_slot hd slot _ hslot (G.pair ℓ).2 ℓ.2).symm

end Decodes

end WaveTurbulence.Flower.MkMark
