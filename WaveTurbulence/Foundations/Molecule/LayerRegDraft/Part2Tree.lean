/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.LayerReg2Tree

/-!
# TARGET Prop `layerreg1` (2) for regular trees: the characterization

A regular tree (chain code `X`, root sign `ζ`) embedded at `a` (`ChainEmb`), with lone position
`n = a · lonePath`. Its region is `InTree a n` (below `a`, not below `n`); the subtree at `n` belongs to the
rest of the garden. `TreePattern` is the layering of part (1) (coherent, `ChainPairLayers`, chain layers
between `𝔏_n = q'` and `q = 𝔏_{a^pr}`).

**`layerreg1_part2_tree`**: for such a tree in a plain layered garden,

  `CanonCriterion p ↔ (i) ∧ CritOutT ∧ CritAttachT`,

where `CritOutT` is criterion (ii) for pairs of nodes outside the region other than `n`, and `CritAttachT`
is criterion (ii) at `n` against an outside node, with the parent layer of `n` read as `q` (the tree
collapsed to the single node `n`). Neither looks inside the tree.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {w : ℕ}

/-- `z` lies in the region of an embedded tree with root `a` and lone position `n`. -/
def InTree (a n z : Fin w × Path) : Prop := Under a z ∧ ¬ Under n z

variable (LG : LayeredGarden w) (p : ℕ)

/-- **The criterion (ii) away from an embedded tree** (and its lone position). -/
def CritOutT (a n : Fin w × Path) : Prop :=
  ∀ x y : GNode LG.garden.tree, ¬ InTree a n x.1 → ¬ InTree a n y.1 → x.1 ≠ n → y.1 ≠ n →
    x.Incomparable y → LG.garden.CompletelyPaired (x.leavesBelow ∪ y.leavesBelow) →
    min (LG.parentLayer p x) (LG.parentLayer p y) ≤ max (LG.layer x) (LG.layer y)

/-- **The criterion (ii) at the lone position, the tree collapsed** (parent layer of `n` read as the
parent layer `q` of the root `a`). -/
def CritAttachT (a n : Fin w × Path) : Prop :=
  ∀ x y : GNode LG.garden.tree, x.1 = n → ¬ InTree a n y.1 → x.Incomparable y →
    LG.garden.CompletelyPaired (x.leavesBelow ∪ y.leavesBelow) →
    min (parAt LG p a) (LG.parentLayer p y) ≤ max (LG.layer x) (LG.layer y)

/-- **The layering of TARGET `layerreg1` (1)** on an embedded regular tree. -/
def TreePattern (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) : Prop :=
  CohOn LG (X.linksAt ζ a) ∧ ChainPairLayers LG X ζ a ∧
  ∀ z ∈ chainNodesSet X ζ a,
    layerAt LG (addrExt a X.lonePath) ≤ layerAt LG z ∧ layerAt LG z ≤ parAt LG p a

variable {LG p}

/-- **Part (1) gives the pattern.** -/
theorem treePattern_of_canon (hcan : LG.CanonCriterion p) (hplain : LG.garden.IsPlain)
    {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree} (hwf : X.wf = true)
    (hC : ChainEmb LG.garden X ζ a h) (hcoh : CohOn LG (X.linksAt ζ a)) : TreePattern LG p X ζ a :=
  ⟨hcoh, (layerreg1_tree hcan hplain hwf hC hcoh).1, (layerreg1_tree hcan hplain hwf hC hcoh).2.1⟩

/-! ### The region of an embedded tree -/

/-- The pair endpoints of a chain are not below its lone position. -/
theorem chain_pairs_not_under_lone : ∀ (X : RegChain) (ζ : ℤˣ) (a z : Fin w × Path),
    z ∈ pairEndpoints (X.pairsAt ζ a) → ¬ Under (addrExt a X.lonePath) z
  | .nil, _, _, z, hz => by simp [RegChain.pairsAt] at hz
  | .pair m Qr Qg inner rest, ζ, a, z, hz => by
    have hl : Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))
        (addrExt a (RegChain.pair m Qr Qg inner rest).lonePath) := by
      rw [chain_lonePath_eq]; exact under_ext _ _
    rw [RegChain.pairsAt, pairEndpoints_append, pairEndpoints_append, pairEndpoints_append] at hz
    simp only [Finset.mem_union] at hz
    rcases hz with ((hz | hz) | hz) | hz
    · exact fun h => local_not_under_rest m Qr Qg inner ζ a z (Or.inl hz) (under_trans hl h)
    · exact fun h => local_not_under_rest m Qr Qg inner ζ a z (Or.inr (Or.inl hz)) (under_trans hl h)
    · exact fun h => local_not_under_rest m Qr Qg inner ζ a z (Or.inr (Or.inr hz)) (under_trans hl h)
    · have := chain_pairs_not_under_lone rest _ _ z hz
      rwa [← chain_lonePath_eq] at this

section Garden

variable {G : Garden w}

/-- Every carrier leaf of the region of an embedded tree is a decoded leaf of the chain. -/
theorem ChainEmb.leaf_mem {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}
    (hC : ChainEmb G X ζ a h) (ℓ : GLeaf G.tree) (hℓ : InTree a (addrExt a X.lonePath) ℓ.1) :
    ℓ.1 ∈ pairEndpoints (X.pairsAt ζ a) := by
  have := leafAddresses_of_leaf hC.node hC.tree ℓ hℓ.1
  rw [chain_leafAddresses] at this
  rcases Finset.mem_union.1 this with h1 | h1
  · exact h1
  · obtain ⟨q, -, e⟩ := mem_image_addrExt h1
    exact absurd (by rw [e]; exact under_ext _ _) hℓ.2

/-- Every node of the region of an embedded tree is a node of the chain. -/
theorem ChainEmb.mem_chainNodesSet {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}
    (hC : ChainEmb G X ζ a h) {z : Fin w × Path} (hz : z.2 ∈ (G.tree z.1).nodes)
    (hr : InTree a (addrExt a X.lonePath) z) : z ∈ chainNodesSet X ζ a := by
  obtain ⟨q, rfl⟩ := under_of_addrExt hr.1
  have hq := (node_iff_of_subtree hC.node hC.tree q).1.1 hz
  unfold chainNodesSet
  rcases (Comb.TreePath.mem_nodes_iff _ _).1 hq with hl | hb
  · have h1 : addrExt a q ∈ leafAddresses (X.plug ζ h) a := addrExt_mem_image a q hl
    rw [chain_leafAddresses] at h1
    rcases Finset.mem_union.1 h1 with h2 | h2
    · exact Finset.mem_union_right _ h2
    · obtain ⟨t, -, e⟩ := mem_image_addrExt h2
      exact absurd (by rw [e]; exact under_ext _ _) hr.2
  · have h1 : addrExt a q ∈ branchAddresses (X.plug ζ h) a := addrExt_mem_image a q hb
    rw [chain_branchAddresses] at h1
    rcases Finset.mem_union.1 h1 with h2 | h2
    · exact Finset.mem_union_left _ h2
    · obtain ⟨t, -, e⟩ := mem_image_addrExt h2
      exact absurd (by rw [e]; exact under_ext _ _) hr.2

/-- The partner of a leaf of the region of an embedded tree is given by a decoded pair. -/
theorem ChainEmb.partner {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}
    (hC : ChainEmb G X ζ a h) (ℓ : GLeaf G.tree) (hℓ : InTree a (addrExt a X.lonePath) ℓ.1) :
    ∃ q ∈ X.pairsAt ζ a, (ℓ.1 = q.1 ∧ (G.pair ℓ).1 = q.2) ∨ (ℓ.1 = q.2 ∧ (G.pair ℓ).1 = q.1) := by
  obtain ⟨q, hq, hqe⟩ := (mem_pairEndpoints_iff _ _).1 (hC.leaf_mem ℓ hℓ)
  refine ⟨q, hq, ?_⟩
  rcases hqe with e | e
  · exact Or.inl ⟨e, hC.pairs q hq ℓ e⟩
  · have l1 := hC.leaf_of_mem ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩)
    let ℓ' : GLeaf G.tree := ⟨q.1, l1⟩
    have hp := hC.pairs q hq ℓ' rfl
    have hpl : G.pair ℓ' = ℓ := Subtype.ext (hp.trans e.symm)
    have : G.pair ℓ = ℓ' := by rw [← hpl]; exact G.pair_pair ℓ'
    exact Or.inr ⟨e, by rw [this]⟩

/-- **The region of an embedded tree is closed under the pairing.** -/
theorem ChainEmb.pair_region {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}
    (hC : ChainEmb G X ζ a h) (ℓ : GLeaf G.tree) (hℓ : InTree a (addrExt a X.lonePath) ℓ.1) :
    InTree a (addrExt a X.lonePath) (G.pair ℓ).1 := by
  obtain ⟨q, hq, e⟩ := hC.partner ℓ hℓ
  have m1 : q.1 ∈ pairEndpoints (X.pairsAt ζ a) := (mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩
  have m2 : q.2 ∈ pairEndpoints (X.pairsAt ζ a) := (mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inr rfl⟩
  have r : ∀ z ∈ pairEndpoints (X.pairsAt ζ a), InTree a (addrExt a X.lonePath) z := fun z hz =>
    ⟨(chain_endpoints_region X ζ a z (Finset.mem_union_right _ hz)).1,
      chain_pairs_not_under_lone X ζ a z hz⟩
  rcases e with ⟨-, e⟩ | ⟨-, e⟩
  · rw [e]; exact r _ m2
  · rw [e]; exact r _ m1

theorem ChainEmb.pair_out {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}
    (hC : ChainEmb G X ζ a h) (ℓ : GLeaf G.tree) (hℓ : ¬ InTree a (addrExt a X.lonePath) ℓ.1) :
    ¬ InTree a (addrExt a X.lonePath) (G.pair ℓ).1 := by
  intro h'
  have := hC.pair_region (G.pair ℓ) h'
  rw [G.pair_pair] at this
  exact hℓ this

/-- **Completely paired sets around an embedded tree**: for an address predicate constant on the region,
complete pairing only depends on the leaves outside the region. -/
theorem cp_iff_tree (hplain : G.IsPlain) {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}
    (hC : ChainEmb G X ζ a h) (σ : Fin w × Path → Prop)
    (hσ : ∀ z₁ z₂, InTree a (addrExt a X.lonePath) z₁ → InTree a (addrExt a X.lonePath) z₂ →
      (σ z₁ ↔ σ z₂))
    (S : Finset (GLeaf G.tree)) (hS : ∀ ℓ, ℓ ∈ S ↔ σ ℓ.1) :
    G.CompletelyPaired S ↔
      ∀ ℓ : GLeaf G.tree, ¬ InTree a (addrExt a X.lonePath) ℓ.1 → σ ℓ.1 → σ (G.pair ℓ).1 := by
  constructor
  · intro hcp ℓ _ h'
    exact (hS _).1 (hcp ℓ ((hS ℓ).2 h')).2
  · intro hout ℓ hℓ
    refine ⟨fun e => ((G.pair_eq_iff ℓ).1 e) (hplain ℓ), (hS _).2 ?_⟩
    have hσℓ := (hS ℓ).1 hℓ
    by_cases hr : InTree a (addrExt a X.lonePath) ℓ.1
    · exact (hσ _ _ hr (hC.pair_region ℓ hr)).1 hσℓ
    · exact hout ℓ hr hσℓ

end Garden

/-! ### The characterization -/

variable {LG : LayeredGarden w} {p : ℕ}

/-- An address outside the region of a tree sees the whole region or none of it. -/
theorem under_const_tree {a n x z₁ z₂ : Fin w × Path} (hx : ¬ InTree a n x) (h₁ : InTree a n z₁)
    (h₂ : InTree a n z₂) : Under x z₁ ↔ Under x z₂ := by
  have key : ∀ {z₁ z₂ : Fin w × Path}, InTree a n z₁ → InTree a n z₂ → Under x z₁ → Under x z₂ := by
    intro z₁ z₂ h₁ h₂ hu
    rcases under_total hu h₁.1 with h | h
    · exact under_trans h h₂.1
    · have hxn : Under n x := by
        by_contra hn; exact hx ⟨h, hn⟩
      exact absurd (under_trans hxn hu) h₁.2
  exact ⟨key h₁ h₂, key h₂ h₁⟩

/-- **TARGET Prop `layerreg1` (2), regular trees, characterization.** -/
theorem layerreg1_part2_tree (hplain : LG.garden.IsPlain) {X : RegChain} {ζ : ℤˣ}
    {a : Fin w × Path} {h : TTree} (hC : ChainEmb LG.garden X ζ a h) (hP : TreePattern LG p X ζ a) :
    LG.CanonCriterion p ↔ (∀ x, LG.layer x ≤ p) ∧ CritOutT LG p a (addrExt a X.lonePath) ∧
      CritAttachT LG p a (addrExt a X.lonePath) := by
  obtain ⟨-, hL, -⟩ := hP
  set n := addrExt a X.lonePath with hn
  have nn : n.2 ∈ (LG.garden.tree n.1).nodes := nodeOfChainEmb hC
  have han : Under a n := under_ext _ _
  -- leaves below `n` or an outside node `y` incomparable with `n`
  constructor
  · intro hcan
    refine ⟨hcan.1, fun x y _ _ _ _ hinc hcp => hcan.2 x y hinc hcp, ?_⟩
    intro x y hx hy hinc hcp
    have hyx : ¬ Under y.1 n := fun h' => hinc.2 (show Under y.1 x.1 by rw [hx]; exact h')
    have hxy : ¬ Under n y.1 := fun h' => hinc.1 (show Under x.1 y.1 by rw [hx]; exact h')
    rw [← parAt_node, ← layerAt_node, ← layerAt_node, hx]
    by_contra hlt
    rw [not_le] at hlt
    set t := min (parAt LG p a) (parAt LG p y.1)
    obtain ⟨s, hs, hls, hps⟩ := spine_cut_lt X ζ a h hC hL t
      (lt_of_le_of_lt (le_max_left _ _) hlt) (min_le_left _ _)
    have sn := spinePos_node hC hs
    obtain ⟨has, hsn⟩ := spinePos_under X a s hs
    have hsy : Indep s y.1 := by
      refine ⟨fun h' => ?_, fun h' => ?_⟩
      · have hay := under_trans has h'
        have : Under n y.1 := by by_contra hn'; exact hy ⟨hay, hn'⟩
        exact hxy this
      · exact hyx (under_trans h' hsn)
    have hcp' : LG.garden.CompletelyPaired
        (GNode.leavesBelow (⟨s, sn⟩ : GNode LG.garden.tree) ∪ y.leavesBelow) := by
      apply cp_of hplain
      intro ℓ hℓ
      by_cases hr : InTree a n ℓ.1
      · rcases hℓ with h' | h'
        · obtain ⟨q, hq, e⟩ := hC.partner ℓ hr
          have cl := spine_closed X ζ a s hs q hq
          rcases e with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · exact Or.inl (by rw [e2]; exact cl.1 (by rw [← e1]; exact h'))
          · exact Or.inl (by rw [e2]; exact cl.2 (by rw [← e1]; exact h'))
        · exfalso
          rcases under_total h' hr.1 with h'' | h''
          · exact hyx (under_trans h'' han)
          · have : Under n y.1 := by by_contra hn'; exact hy ⟨h'', hn'⟩
            exact hr.2 (under_trans this h')
      · have hℓ' : Under n ℓ.1 ∨ Under y.1 ℓ.1 := by
          rcases hℓ with h' | h'
          · left; by_contra hn'; exact hr ⟨under_trans has h', hn'⟩
          · exact Or.inr h'
        rcases cp_to hcp ℓ (by rw [hx]; exact hℓ') with h' | h'
        · have h'' := h'
          rw [hx] at h''
          exact Or.inl (under_trans hsn h'')
        · exact Or.inr h'
    have := hcan.2 ⟨s, sn⟩ y ⟨hsy.1, hsy.2⟩ hcp'
    rw [← parAt_of_mem LG p sn, ← layerAt_of_mem LG sn, ← parAt_node, ← layerAt_node] at this
    have ht : t ≤ min (parAt LG p s) (parAt LG p y.1) := le_min hps (min_le_right _ _)
    exact absurd this (not_le.2 (max_lt (hls.trans_le ht)
      ((lt_of_le_of_lt (le_max_right _ _) hlt).trans_le ht)))
  · rintro ⟨hp, hout, hatt⟩
    refine ⟨hp, fun x y hinc hcp => ?_⟩
    rw [← parAt_node, ← parAt_node, ← layerAt_node, ← layerAt_node]
    have hqa : parAt LG p n ≤ parAt LG p a := parAt_le_parAt LG p hp hC.node nn han
    -- the instance `(n, y)`, `y` outside
    have attach : ∀ y : GNode LG.garden.tree, ¬ InTree a n y.1 →
        GNode.Incomparable (⟨n, nn⟩ : GNode LG.garden.tree) y →
        LG.garden.CompletelyPaired (GNode.leavesBelow (⟨n, nn⟩ : GNode LG.garden.tree) ∪
          y.leavesBelow) →
        min (parAt LG p a) (parAt LG p y.1) ≤ max (layerAt LG n) (layerAt LG y.1) := by
      intro y hy hi hc
      have := hatt ⟨n, nn⟩ y rfl hy hi hc
      rwa [← parAt_node, ← layerAt_of_mem LG nn, ← layerAt_node] at this
    -- `x` in the region on the spine, `y` outside, not `n`
    have side : ∀ x y : GNode LG.garden.tree, InTree a n x.1 → Under x.1 n → ¬ InTree a n y.1 →
        x.Incomparable y → LG.garden.CompletelyPaired (x.leavesBelow ∪ y.leavesBelow) →
        min (parAt LG p x.1) (parAt LG p y.1) ≤ max (layerAt LG x.1) (layerAt LG y.1) := by
      intro x y hxr hxn hy hinc hcp
      have hyx : ¬ Under y.1 n := fun h' => by
        rcases under_total h' hxn with h'' | h''
        · exact hinc.2 h''
        · exact hinc.1 h''
      have hny : ¬ Under n y.1 := fun h' => hinc.1 (under_trans hxn h')
      have hc : LG.garden.CompletelyPaired
          (GNode.leavesBelow (⟨n, nn⟩ : GNode LG.garden.tree) ∪ y.leavesBelow) := by
        apply cp_of hplain
        intro ℓ hℓ
        have hr : ¬ InTree a n ℓ.1 := by
          rintro ⟨h1, h2⟩
          rcases hℓ with h' | h'
          · exact h2 h'
          · rcases under_total h' h1 with h'' | h''
            · exact hinc.2 (under_trans h'' hxr.1)
            · have : Under n y.1 := by by_contra hn'; exact hy ⟨h'', hn'⟩
              exact hny this
        have hpo := hC.pair_out ℓ hr
        rcases cp_to hcp ℓ (hℓ.imp (fun h' => under_trans hxn h') id) with h' | h'
        · left; by_contra hn'; exact hpo ⟨under_trans hxr.1 h', hn'⟩
        · exact Or.inr h'
      have h1 := attach y hy ⟨hny, hyx⟩ hc
      have h2 : parAt LG p x.1 ≤ parAt LG p a := parAt_le_parAt LG p hp hC.node x.2 hxr.1
      have h3 : layerAt LG n ≤ layerAt LG x.1 := layerAt_le_of_under LG x.2 nn hxn
      calc min (parAt LG p x.1) (parAt LG p y.1) ≤ min (parAt LG p a) (parAt LG p y.1) :=
            min_le_min h2 le_rfl
        _ ≤ max (layerAt LG n) (layerAt LG y.1) := h1
        _ ≤ max (layerAt LG x.1) (layerAt LG y.1) := max_le_max h3 le_rfl
    -- `x = n`, `y` outside
    have atn : ∀ x y : GNode LG.garden.tree, x.1 = n → ¬ InTree a n y.1 → x.Incomparable y →
        LG.garden.CompletelyPaired (x.leavesBelow ∪ y.leavesBelow) →
        min (parAt LG p x.1) (parAt LG p y.1) ≤ max (layerAt LG x.1) (layerAt LG y.1) := by
      intro x y hx hy hinc hcp
      have hx' : x = ⟨n, nn⟩ := Subtype.ext hx
      subst hx'
      exact (min_le_min hqa le_rfl).trans (attach y hy hinc hcp)
    -- flatness in the region
    have hfl : ∀ z : GNode LG.garden.tree, InTree a n z.1 →
        Under z.1 n ∨ parAt LG p z.1 = layerAt LG z.1 := fun z hz =>
      chain_flat X ζ a h hC hL z.1 (hC.mem_chainNodesSet z.2 hz)
    have flatL : ∀ x y : GNode LG.garden.tree, parAt LG p x.1 = layerAt LG x.1 →
        min (parAt LG p x.1) (parAt LG p y.1) ≤ max (layerAt LG x.1) (layerAt LG y.1) :=
      fun x y hf => by rw [hf]; exact (min_le_left _ _).trans (le_max_left _ _)
    have flatR : ∀ x y : GNode LG.garden.tree, parAt LG p y.1 = layerAt LG y.1 →
        min (parAt LG p x.1) (parAt LG p y.1) ≤ max (layerAt LG x.1) (layerAt LG y.1) :=
      fun x y hf => by rw [hf]; exact (min_le_right _ _).trans (le_max_right _ _)
    have swap : min (parAt LG p y.1) (parAt LG p x.1) ≤ max (layerAt LG y.1) (layerAt LG x.1) →
        min (parAt LG p x.1) (parAt LG p y.1) ≤ max (layerAt LG x.1) (layerAt LG y.1) := by
      intro h'; rwa [min_comm, max_comm]
    have hinc' : y.Incomparable x := ⟨hinc.2, hinc.1⟩
    have hcp' : LG.garden.CompletelyPaired (y.leavesBelow ∪ x.leavesBelow) := by
      rwa [Finset.union_comm]
    by_cases hxr : InTree a n x.1 <;> by_cases hyr : InTree a n y.1
    · rcases hfl x hxr with hxn | hf
      · rcases hfl y hyr with hyn | hf
        · exfalso
          rcases under_total hxn hyn with h' | h'
          · exact hinc.1 h'
          · exact hinc.2 h'
        · exact flatR x y hf
      · exact flatL x y hf
    · rcases hfl x hxr with hxn | hf
      · exact side x y hxr hxn hyr hinc hcp
      · exact flatL x y hf
    · rcases hfl y hyr with hyn | hf
      · exact swap (side y x hyr hyn hxr hinc' hcp')
      · exact flatR x y hf
    · by_cases hxn : x.1 = n
      · exact atn x y hxn hyr hinc hcp
      · by_cases hyn : y.1 = n
        · exact swap (atn y x hyn hxr hinc' hcp')
        · have := hout x y hxr hyr hxn hyn hinc hcp
          rwa [← parAt_node, ← parAt_node, ← layerAt_node, ← layerAt_node] at this

end WaveTurbulence.Links
