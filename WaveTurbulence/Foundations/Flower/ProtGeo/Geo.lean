/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs
public import WaveTurbulence.Foundations.Flower.MkDefs.Intrinsic
public import WaveTurbulence.Foundations.RegStruct.ChainNodeBounds
public import WaveTurbulence.Foundations.IncohInst.LayerReg.Embed2

/-! # D2b PROT-GEO (1): the capped geometry and o73 Proposition 3.1 on main's embeddings

A capped component `LG` with cap trees `J` (`CapGeo`): cap trees are single leaves, all layers are at most `p`,
capped stems lie in layer `p` (T2261), and each tree carries at most one capped flower. A regular object is one of
main's embeddings: a paired tree `ChainEmb LG.garden X ζ u h` (chain code `X` rooted at `u`, the subtree `h` at its
lone position) or a couple `Embeds LG.garden Q a b`. Its branching vertices are `branchAddresses (X.plug ζ .leaf) u`
(main's `chain_branchAddresses`: `= pairEndpoints (X.linksAt ζ u)`), resp. `branchAddresses Q.trees.1 a ∪
branchAddresses Q.trees.2 b` (`= pairEndpoints (Q.linksAt a b)`).

o73 Prop 3.1 (paired trees): if an object has a branching vertex above a capped flower `f`, its lone position is
at or above `f` (`port_below_flower`); hence its chain lies on the stem, in layer `p` (`chain_layer`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.ProtGeo

variable {w : ℕ}

/-! ## The setting -/

/- `CapGeo` and `CapPatValid` moved verbatim to `WaveTurbulence.Flower.MkDefs` (MkDefs/Defs.lean; ruling R163). -/

/-- An object with branching addresses `B` meets a (capped) stem branching node. -/
def MeetsStem (LG : LayeredGarden w) (J : Finset (Fin w)) (B : Finset (Fin w × Path)) : Prop :=
  ∃ v : GBranch LG.garden.tree, v.1 ∈ B ∧ OnCapStem LG J v.toNode

/-- **A stem chain**: an embedded paired tree (chain code `X`, root `u`, sign `ζ`, subtree `h` at the lone
position) with well-formed code, meeting a capped stem branching node. -/
structure StemChain (LG : LayeredGarden w) (J : Finset (Fin w)) (X : RegChain) (ζ : ℤˣ) (u : Fin w × Path)
    (h : TTree) : Prop where
  emb : ChainEmb LG.garden X ζ u h
  wf : X.wf = true
  meets : MeetsStem LG J (branchAddresses (X.plug ζ .leaf) u)

/-- **A cap chain**: the chain of a cap couple, its lone leaf (a capped flower) paired with the cap root `(c, [])`. -/
structure CapChain (LG : LayeredGarden w) (J : Finset (Fin w)) (X : RegChain) (ζ : ℤˣ) (u : Fin w × Path)
    (c : Fin w) : Prop where
  stem : StemChain LG J X ζ u .leaf
  cap : c ∈ J
  pair : ∀ ℓ : GLeaf LG.garden.tree, ℓ.1 = addrExt u X.lonePath → (LG.garden.pair ℓ).1 = (c, [])

/-- The lone position of the object is a capped flower. -/
def PortFlower (LG : LayeredGarden w) (J : Finset (Fin w)) (X : RegChain) (u : Fin w × Path) : Prop :=
  ∃ f : GLeaf LG.garden.tree, IsCapFlower LG J f ∧ f.1 = addrExt u X.lonePath

/-- The lone position of the object is a capped flower parent. -/
def PortFP (LG : LayeredGarden w) (J : Finset (Fin w)) (X : RegChain) (u : Fin w × Path) : Prop :=
  ∃ c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ c.1 = addrExt u X.lonePath

/-! ## Generic address facts -/

theorem addrExt_injective (u : Fin w × Path) : Function.Injective (addrExt u) := by
  intro p q h
  exact List.append_cancel_left (congrArg Prod.snd h)

theorem addrExt_nil' (u : Fin w × Path) : addrExt u [] = u := by
  simp [addrExt]

theorem addrExt_addrExt (u : Fin w × Path) (p q : Path) : addrExt (addrExt u p) q = addrExt u (p ++ q) := by
  simp [addrExt, List.append_assoc]

theorem mem_branchAddresses' {t : TTree} {u z : Fin w × Path} :
    z ∈ branchAddresses t u ↔ ∃ q ∈ t.branching, z = addrExt u q := by
  unfold branchAddresses
  simp only [Finset.mem_image]
  exact ⟨fun ⟨q, hq, he⟩ => ⟨q, hq, he.symm⟩, fun ⟨q, hq, he⟩ => ⟨q, hq, he.symm⟩⟩

theorem addrExt_mem_branchAddresses {t : TTree} {u : Fin w × Path} {q : Path} :
    addrExt u q ∈ branchAddresses t u ↔ q ∈ t.branching := by
  rw [mem_branchAddresses']
  exact ⟨fun ⟨r, hr, he⟩ => (addrExt_injective u he) ▸ hr, fun hq => ⟨q, hq, rfl⟩⟩

theorem mem_leafAddresses' {t : TTree} {u z : Fin w × Path} :
    z ∈ leafAddresses t u ↔ ∃ q ∈ t.leaves, z = addrExt u q := by
  unfold leafAddresses
  simp only [Finset.mem_image]
  exact ⟨fun ⟨q, hq, he⟩ => ⟨q, hq, he.symm⟩, fun ⟨q, hq, he⟩ => ⟨q, hq, he.symm⟩⟩

/-! ## The chain with a trivial filling -/

section Chain

variable (X : RegChain) (ζ : ℤˣ)

/-- No branching node of the chain is at or below its lone position. -/
theorem lone_not_prefix_branch {q : Path} (hq : q ∈ (X.plug ζ .leaf).branching) : ¬ X.lonePath <+: q := by
  intro hP
  have he := leaf_prefix_node_eq (chain_lone_mem_leaves X ζ) (TTree.branching_subset_nodes _ hq) hP
  subst he
  exact TTree.not_mem_branching_of_mem_leaves _ (chain_lone_mem_leaves X ζ) hq

/-- The strict prefixes of the lone path are branching nodes (the chain nodes). -/
theorem prefix_lone_branching {q : Path} (hq : q <+: X.lonePath) (hne : q ≠ X.lonePath) :
    q ∈ (X.plug ζ .leaf).branching := by
  obtain ⟨r, hr⟩ := hq
  cases r with
  | nil => exact absurd (by simpa using hr) hne
  | cons i r =>
    have hn : q ++ [i] ∈ (X.plug ζ .leaf).nodes := by
      refine Comb.TreePath.mem_nodes_of_prefix _
        (TTree.leaves_subset_nodes _ (chain_lone_mem_leaves X ζ)) ⟨r, ?_⟩
      rw [← hr]; simp
    exact Comb.TreePath.branching_of_append_mem _ hn

/-- A branching node of the chain forces a nonempty lone path. -/
theorem lone_ne_nil_of_branch {q : Path} (hq : q ∈ (X.plug ζ .leaf).branching) : X.lonePath ≠ [] := by
  intro h
  exact lone_not_prefix_branch X ζ hq (h ▸ List.nil_prefix)

theorem branching_plug_leaf (h : TTree) {q : Path} (hq : q ∈ (X.plug ζ .leaf).branching) :
    q ∈ (X.plug ζ h).branching := by
  have h1 : addrExt ((0 : Fin 1), ([] : Path)) q ∈ branchAddresses (X.plug ζ .leaf) ((0 : Fin 1), []) :=
    addrExt_mem_branchAddresses.mpr hq
  rw [chain_branchAddresses, branchAddresses_leaf, Finset.union_empty] at h1
  have h2 : addrExt ((0 : Fin 1), ([] : Path)) q ∈ branchAddresses (X.plug ζ h) ((0 : Fin 1), []) := by
    rw [chain_branchAddresses]; exact Finset.mem_union_left _ h1
  exact addrExt_mem_branchAddresses.mp h2

theorem branching_plug_of (h : TTree) {q : Path} (hq : q ∈ (X.plug ζ h).branching)
    (hP : ¬ X.lonePath <+: q) : q ∈ (X.plug ζ .leaf).branching := by
  have h1 : addrExt ((0 : Fin 1), ([] : Path)) q ∈ branchAddresses (X.plug ζ h) ((0 : Fin 1), []) :=
    addrExt_mem_branchAddresses.mpr hq
  rw [chain_branchAddresses] at h1
  rcases Finset.mem_union.mp h1 with h1 | h1
  · have h2 : addrExt ((0 : Fin 1), ([] : Path)) q ∈ branchAddresses (X.plug ζ .leaf) ((0 : Fin 1), []) := by
      rw [chain_branchAddresses, branchAddresses_leaf, Finset.union_empty]; exact h1
    exact addrExt_mem_branchAddresses.mp h2
  · obtain ⟨r, -, he⟩ := mem_branchAddresses'.mp h1
    rw [addrExt_addrExt] at he
    exact absurd ⟨r, (addrExt_injective _ he).symm⟩ hP

end Chain

/-! ## Embedded chains in the carrier -/

section Emb

variable {G : Garden w} {X : RegChain} {ζ : ℤˣ} {u : Fin w × Path} {h : TTree}

/-- Object branching nodes are carrier branching nodes. -/
theorem emb_branch_mem (hE : ChainEmb G X ζ u h) {q : Path} (hq : q ∈ (X.plug ζ .leaf).branching) :
    (addrExt u q).2 ∈ (G.tree (addrExt u q).1).branching :=
  (node_iff_of_subtree hE.node hE.tree q).2.2.2 (branching_plug_leaf X ζ h hq)

/-- The carrier branch at an object branching position. -/
def embBr (hE : ChainEmb G X ζ u h) (q : Path) (hq : q ∈ (X.plug ζ .leaf).branching) :
    GBranch G.tree :=
  ⟨addrExt u q, (emb_branch_mem hE) hq⟩

/-- Pair endpoints of an embedded chain are carrier leaves under its root. -/
theorem emb_endpoint_leaf (hE : ChainEmb G X ζ u h) {z : Fin w × Path}
    (hz : z ∈ pairEndpoints (X.pairsAt ζ u)) : z.2 ∈ (G.tree z.1).leaves ∧ ∃ q, z = addrExt u q := by
  have h1 : z ∈ leafAddresses (X.plug ζ h) u := by
    rw [chain_leafAddresses]; exact Finset.mem_union_left _ hz
  obtain ⟨q, hq, rfl⟩ := mem_leafAddresses'.mp h1
  exact ⟨(node_iff_of_subtree hE.node hE.tree q).2.1.2 hq, q, rfl⟩

/-- Carrier leaves under the root and not below the lone position are pair endpoints. -/
theorem emb_leaf_endpoint (hE : ChainEmb G X ζ u h) (ℓ : GLeaf G.tree) (hu : Under u ℓ.1)
    (hP : ¬ Under (addrExt u X.lonePath) ℓ.1) : ℓ.1 ∈ pairEndpoints (X.pairsAt ζ u) := by
  have h1 := leafAddresses_of_leaf hE.node hE.tree ℓ hu
  rw [chain_leafAddresses] at h1
  rcases Finset.mem_union.mp h1 with h1 | h1
  · exact h1
  · obtain ⟨r, -, he⟩ := mem_leafAddresses'.mp h1
    exact absurd ⟨by rw [he]; rfl, r, by rw [he]; rfl⟩ hP

/-- The partner of a pair endpoint is a pair endpoint. -/
theorem emb_pair_endpoint (hE : ChainEmb G X ζ u h) (ℓ : GLeaf G.tree)
    (hℓ : ℓ.1 ∈ pairEndpoints (X.pairsAt ζ u)) : (G.pair ℓ).1 ∈ pairEndpoints (X.pairsAt ζ u) := by
  obtain ⟨p, hp, h1 | h1⟩ := (mem_pairEndpoints_iff _ _).mp hℓ
  · rw [hE.pairs p hp ℓ h1]
    exact (mem_pairEndpoints_iff _ _).mpr ⟨p, hp, Or.inr rfl⟩
  · have hm : p.1 ∈ pairEndpoints (X.pairsAt ζ u) := (mem_pairEndpoints_iff _ _).mpr ⟨p, hp, Or.inl rfl⟩
    let g : GLeaf G.tree := ⟨p.1, (emb_endpoint_leaf hE hm).1⟩
    have hg : G.pair g = ℓ := Subtype.ext ((hE.pairs p hp g rfl).trans h1.symm)
    rw [← hg, G.pair_pair]
    exact hm

/-- Pair endpoints of an embedded chain lie in the root's tree, under the root. -/
theorem emb_endpoint_under (hE : ChainEmb G X ζ u h) {z : Fin w × Path}
    (hz : z ∈ pairEndpoints (X.pairsAt ζ u)) : Under u z := by
  obtain ⟨-, q, rfl⟩ := (emb_endpoint_leaf hE) hz
  exact ⟨rfl, q, rfl⟩

/-- Paired leaves of an embedded chain have equal layers. -/
theorem emb_pair_layer {LG : LayeredGarden w} (hE : ChainEmb LG.garden X ζ u h)
    {p : (Fin w × Path) × (Fin w × Path)} (hp : p ∈ X.pairsAt ζ u) : layerAt LG p.1 = layerAt LG p.2 := by
  have h1 : p.1 ∈ pairEndpoints (X.pairsAt ζ u) := (mem_pairEndpoints_iff _ _).2 ⟨p, hp, Or.inl rfl⟩
  have l1 := (emb_endpoint_leaf hE h1).1
  have hq := hE.pairs p hp ⟨p.1, l1⟩ rfl
  have n1 := TTree.leaves_subset_nodes _ l1
  have n2 : p.2.2 ∈ (LG.garden.tree p.2.1).nodes := by
    rw [← hq]; exact TTree.leaves_subset_nodes _ (LG.garden.pair ⟨p.1, l1⟩).2
  rw [layerAt_of_mem LG n1, layerAt_of_mem LG n2]
  have e2 : (⟨p.2, n2⟩ : GNode LG.garden.tree) = GLeaf.toNode (LG.garden.pair ⟨p.1, l1⟩) :=
    Subtype.ext hq.symm
  rw [e2]
  exact LG.isLayering.2 ⟨p.1, l1⟩

end Emb

/-! ## o73 Proposition 3.1 for paired trees -/

section Prop31

variable {LG : LayeredGarden w} {J : Finset (Fin w)} {X : RegChain} {ζ : ℤˣ} {u : Fin w × Path} {h : TTree}

/-- A carrier branching node never lies in a cap tree. -/
theorem branch_not_cap (hcap : ∀ j ∈ J, LG.garden.tree j = TTree.leaf) (v : GBranch LG.garden.tree) :
    v.1.1 ∉ J := by
  intro hj
  have h1 := v.2
  rw [hcap _ hj] at h1
  simp [TTree.branching] at h1

/-- **o73 Prop 3.1 (paired trees).** If a branching vertex of an embedded paired tree lies above a capped flower,
then the object's lone position lies at or above that flower. -/
theorem port_below_flower (hcap : ∀ j ∈ J, LG.garden.tree j = TTree.leaf) (hE : ChainEmb LG.garden X ζ u h)
    {q : Path} (hq : q ∈ (X.plug ζ .leaf).branching) {f : GLeaf LG.garden.tree} (hf : IsCapFlower LG J f)
    (hqf : Under (addrExt u q) f.1) : Under (addrExt u X.lonePath) f.1 := by
  by_contra hP
  have hu : Under u f.1 := ⟨hqf.1, (List.prefix_append u.2 q).trans hqf.2⟩
  have h1 := (emb_pair_endpoint hE) f (emb_leaf_endpoint hE f hu hP)
  have h2 := (emb_endpoint_under hE h1).1
  have h3 := hf.2
  rw [← h2] at h3
  exact branch_not_cap hcap (embBr hE q hq) h3

/-- Branching vertices of an embedded paired tree above a capped flower are strict prefixes of its lone path. -/
theorem branch_lt_lone (hcap : ∀ j ∈ J, LG.garden.tree j = TTree.leaf) (hE : ChainEmb LG.garden X ζ u h)
    {q : Path} (hq : q ∈ (X.plug ζ .leaf).branching) {f : GLeaf LG.garden.tree} (hf : IsCapFlower LG J f)
    (hqf : Under (addrExt u q) f.1) : q <+: X.lonePath ∧ q ≠ X.lonePath := by
  have hP := port_below_flower hcap hE hq hf hqf
  have h1 : u.2 ++ q <+: f.1.2 := hqf.2
  have h2 : u.2 ++ X.lonePath <+: f.1.2 := hP.2
  rcases List.prefix_or_prefix_of_prefix h1 h2 with h3 | h3
  · have h4 := (List.prefix_append_right_inj u.2).mp h3
    refine ⟨h4, fun he => lone_not_prefix_branch X ζ hq (he ▸ List.prefix_refl _)⟩
  · exact absurd ((List.prefix_append_right_inj u.2).mp h3) (lone_not_prefix_branch X ζ hq)

/-- A stem chain has a capped flower at or below its lone position. -/
theorem StemChain.flower (hcap : ∀ j ∈ J, LG.garden.tree j = TTree.leaf) (hS : StemChain LG J X ζ u h) :
    ∃ f : GLeaf LG.garden.tree, IsCapFlower LG J f ∧ Under (addrExt u X.lonePath) f.1 := by
  obtain ⟨v, hv, f, hf, hvf⟩ := hS.meets
  obtain ⟨q, hq, hvq⟩ := mem_branchAddresses'.mp hv
  refine ⟨f, hf, port_below_flower hcap hS.emb hq hf ?_⟩
  rw [← hvq]; exact hvf

/-- The chain nodes of a stem chain (strict prefixes of the lone path) are capped stem nodes. -/
theorem StemChain.chain_onStem (hcap : ∀ j ∈ J, LG.garden.tree j = TTree.leaf) (hS : StemChain LG J X ζ u h)
    {q : Path} (hq : q <+: X.lonePath) (hne : q ≠ X.lonePath) :
    OnCapStem LG J (embBr hS.emb q (prefix_lone_branching X ζ hq hne)).toNode := by
  obtain ⟨f, hf, hP⟩ := hS.flower hcap
  exact ⟨f, hf, hP.1, ((List.prefix_append_right_inj u.2).mpr hq).trans hP.2⟩

/-- **The chain of a stem chain is in layer `p`** (o73 Prop 3.1, T2261). -/
theorem StemChain.chain_layer {p : ℕ} (hG : CapGeo LG J p) (hS : StemChain LG J X ζ u h)
    {q : Path} (hq : q <+: X.lonePath) (hne : q ≠ X.lonePath) : layerAt LG (addrExt u q) = p := by
  have hb := (emb_branch_mem hS.emb) (prefix_lone_branching X ζ hq hne)
  rw [layerAt_of_mem LG (TTree.branching_subset_nodes _ hb)]
  exact hG.stem_layer _ (hS.chain_onStem hG.cap_leaf hq hne)

end Prop31

end WaveTurbulence.Flower.ProtGeo
