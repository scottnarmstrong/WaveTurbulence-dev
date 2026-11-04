/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Coherence
public import WaveTurbulence.Foundations.IncohInst.Links.Construct3

/-!
# Embedded regular couples and regular trees (packet C4)

TARGET Def `subobject` (L846): two nodes `𝔫, 𝔫'` of a garden whose trees have all their leaves paired to
each other form a sub-couple; a regular couple `𝒬` is *embedded* with roots at `𝔫^±` if this sub-couple
is `𝒬`. With the B2 codes this is `Embeds G Q a b`: the subtrees of the carrier at the addresses `a`,
`b` are the decoded trees `Q.trees`, and the carrier's pairing agrees with the decoded leaf pairs
`Q.pairsAt a b`. `ChainEmb G X ζ a h` is the analogue for a chain code rooted at `a` whose lone
position carries the subtree `h` (TARGET's sub-paired-trees with the lone leaf replaced by `h`).

Both notions pass to every component of the structure decomposition (`Embeds.type1₁`, …,
`ChainEmb.red`, `ChainEmb.rest`) by computing subtrees; and every node of the embedded object is a node
of the carrier, every carrier leaf below its roots is one of its decoded leaves
(`Embeds.mem_cplNodes`, `Embeds.leaf_mem`).

On the layered carrier, `layerAt LG z` is the layer at an address and `parAt LG p z` its parent layer
(a root's parent layer read as `p`, T Prop `canonequiv`); `crit_apply` applies the canonicity criterion
(ii) to two incomparable nodes of an embedded couple whose subtrees are closed under its leaf pairs.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {w : ℕ}

theorem ite_pos_of {α : Sort*} {c : Prop} [Decidable c] {x y : α} (h : c) :
    (if c then x else y) = x := by simp [h]

theorem ite_neg_of {α : Sort*} {c : Prop} [Decidable c] {x y : α} (h : ¬c) :
    (if c then x else y) = y := by simp [h]

/-! ### Subtrees -/

theorem cons_mem_nodes_node (l m r : TTree) (i : Fin 3) (s : Path) :
    i :: s ∈ (TTree.node l m r).nodes ↔ s ∈ (![l, m, r] i).nodes := by
  fin_cases i <;> simp [TTree.nodes, mem_pre]

theorem cons_mem_leaves_node (l m r : TTree) (i : Fin 3) (s : Path) :
    i :: s ∈ (TTree.node l m r).leaves ↔ s ∈ (![l, m, r] i).leaves := by
  fin_cases i <;> simp [TTree.leaves, mem_pre]

theorem cons_mem_branching_node (l m r : TTree) (i : Fin 3) (s : Path) :
    i :: s ∈ (TTree.node l m r).branching ↔ s ∈ (![l, m, r] i).branching := by
  fin_cases i <;> simp [TTree.branching, mem_pre]

theorem subtreeAt_append : ∀ (t : TTree) (p q : Path),
    t.subtreeAt (p ++ q) = (t.subtreeAt p).subtreeAt q
  | t, [], q => rfl
  | .leaf, i :: p, q => by cases q <;> rfl
  | .node l m r, i :: p, q => by
    simp only [List.cons_append, TTree.subtreeAt]
    exact subtreeAt_append _ p q

theorem subtreeAt_cons_node (l m r : TTree) (i : Fin 3) (p : Path) :
    (TTree.node l m r).subtreeAt (i :: p) = (![l, m, r] i).subtreeAt p := rfl

theorem node3_subtreeAt (f : Fin 3 → TTree) (i : Fin 3) (p : Path) :
    (node3 f).subtreeAt (i :: p) = (f i).subtreeAt p := by
  show (TTree.node (f 0) (f 1) (f 2)).subtreeAt (i :: p) = _
  rw [subtreeAt_cons_node]
  congr 1
  fin_cases i <;> rfl

/-- Membership below a node, read in the subtree. -/
theorem mem_subtreeAt : ∀ (t : TTree) (p : Path), p ∈ t.nodes → ∀ q : Path,
    (q ∈ (t.subtreeAt p).nodes ↔ p ++ q ∈ t.nodes) ∧
    (q ∈ (t.subtreeAt p).leaves ↔ p ++ q ∈ t.leaves) ∧
    (q ∈ (t.subtreeAt p).branching ↔ p ++ q ∈ t.branching)
  | t, [], _, q => by simp [TTree.subtreeAt]
  | .leaf, i :: p, h, q => by simp [TTree.nodes] at h
  | .node l m r, i :: p, h, q => by
    rw [cons_mem_nodes_node] at h
    have ih := mem_subtreeAt _ p h q
    simp only [subtreeAt_cons_node, List.cons_append, cons_mem_nodes_node, cons_mem_leaves_node,
      cons_mem_branching_node]
    exact ih

/-- `lonePath` leads to the plugged subtree. -/
theorem plug_subtreeAt_lonePath : ∀ (X : RegChain) (ζ : ℤˣ) (h : TTree),
    (X.plug ζ h).subtreeAt X.lonePath = h
  | .nil, _, _ => rfl
  | .pair m Qr Qg inner rest, ζ, h => by
    simp only [RegChain.plug, RegChain.lonePath, List.append_assoc, List.cons_append,
      List.nil_append]
    rw [node3_subtreeAt]
    simp only [↓reduceIte]
    rw [subtreeAt_append, plug_subtreeAt_lonePath, node3_subtreeAt]
    simp only [↓reduceIte]
    rw [plug_subtreeAt_lonePath]

/-! ### Addresses and nodes of a placed code -/

/-- **The nodes of a couple code placed at `(a, b)`** (link endpoints = branching nodes, pair endpoints =
leaves). -/
def cplNodes (Q : RegCpl) (a b : Fin w × Path) : Finset (Fin w × Path) :=
  pairEndpoints (Q.linksAt a b) ∪ pairEndpoints (Q.pairsAt a b)

/-- The nodes of a chain code rooted at `a` (its lone position excluded). -/
def chainNodesSet (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) : Finset (Fin w × Path) :=
  pairEndpoints (X.linksAt ζ a) ∪ pairEndpoints (X.pairsAt ζ a)

theorem under_of_addrExt {a z : Fin w × Path} (h : Under a z) : ∃ q, z = addrExt a q := by
  obtain ⟨h1, q, hq⟩ := h
  exact ⟨q, Prod.ext h1.symm (by simp [addrExt, hq])⟩

theorem addrExt_mem_image {S : Finset Path} (a : Fin w × Path) (q : Path) (h : q ∈ S) :
    addrExt a q ∈ S.image (addrExt a) := Finset.mem_image_of_mem _ h

theorem mem_image_addrExt {S : Finset Path} {a z : Fin w × Path} (h : z ∈ S.image (addrExt a)) :
    ∃ q ∈ S, z = addrExt a q := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 h
  exact ⟨q, hq, rfl⟩

/-! ### Embeddings -/

/-- **An embedded regular couple** (TARGET Def `subobject`) with code `Q`, `+` root at `a` and `-` root
at `b`. -/
structure Embeds (G : Garden w) (Q : RegCpl) (a b : Fin w × Path) : Prop where
  indep : Indep a b
  nodeA : a.2 ∈ (G.tree a.1).nodes
  nodeB : b.2 ∈ (G.tree b.1).nodes
  treeA : (G.tree a.1).subtreeAt a.2 = Q.trees.1
  treeB : (G.tree b.1).subtreeAt b.2 = Q.trees.2
  pairs : ∀ p ∈ Q.pairsAt a b, ∀ ℓ : GLeaf G.tree, ℓ.1 = p.1 → (G.pair ℓ).1 = p.2

/-- **An embedded chain** with code `X`, root sign `ζ`, root at `a`, and the subtree `h` at its lone
position. -/
structure ChainEmb (G : Garden w) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (h : TTree) : Prop where
  node : a.2 ∈ (G.tree a.1).nodes
  tree : (G.tree a.1).subtreeAt a.2 = X.plug ζ h
  pairs : ∀ p ∈ X.pairsAt ζ a, ∀ ℓ : GLeaf G.tree, ℓ.1 = p.1 → (G.pair ℓ).1 = p.2

variable {G : Garden w}

/-- Addresses below a node with known subtree. -/
theorem node_iff_of_subtree {r : Fin w × Path} {T : TTree} (hr : r.2 ∈ (G.tree r.1).nodes)
    (ht : (G.tree r.1).subtreeAt r.2 = T) (q : Path) :
    ((addrExt r q).2 ∈ (G.tree (addrExt r q).1).nodes ↔ q ∈ T.nodes) ∧
    ((addrExt r q).2 ∈ (G.tree (addrExt r q).1).leaves ↔ q ∈ T.leaves) ∧
    ((addrExt r q).2 ∈ (G.tree (addrExt r q).1).branching ↔ q ∈ T.branching) := by
  have := mem_subtreeAt _ _ hr q
  rw [ht] at this
  exact ⟨this.1.symm, this.2.1.symm, this.2.2.symm⟩

theorem mem_nodes_of_branchAddresses {r : Fin w × Path} {T : TTree} (hr : r.2 ∈ (G.tree r.1).nodes)
    (ht : (G.tree r.1).subtreeAt r.2 = T) {z : Fin w × Path} (hz : z ∈ branchAddresses T r) :
    z.2 ∈ (G.tree z.1).nodes := by
  obtain ⟨q, hq, rfl⟩ := mem_image_addrExt hz
  have := (node_iff_of_subtree hr ht q).2.2.2 hq
  exact TTree.branching_subset_nodes _ this

theorem mem_nodes_of_leafAddresses {r : Fin w × Path} {T : TTree} (hr : r.2 ∈ (G.tree r.1).nodes)
    (ht : (G.tree r.1).subtreeAt r.2 = T) {z : Fin w × Path} (hz : z ∈ leafAddresses T r) :
    z.2 ∈ (G.tree z.1).nodes := by
  obtain ⟨q, hq, rfl⟩ := mem_image_addrExt hz
  have := (node_iff_of_subtree hr ht q).2.1.2 hq
  exact TTree.leaves_subset_nodes _ this

theorem leafAddresses_of_leaf {r : Fin w × Path} {T : TTree} (hr : r.2 ∈ (G.tree r.1).nodes)
    (ht : (G.tree r.1).subtreeAt r.2 = T) (ℓ : GLeaf G.tree) (hℓ : Under r ℓ.1) :
    ℓ.1 ∈ leafAddresses T r := by
  obtain ⟨q, hq⟩ := under_of_addrExt hℓ
  have h2 := ℓ.2
  rw [hq] at h2
  exact hq ▸ addrExt_mem_image r q ((node_iff_of_subtree hr ht q).2.1.1 h2)

/-- Every node of an embedded couple is a node of the carrier. -/
theorem Embeds.mem_nodes {Q : RegCpl} {a b : Fin w × Path} (hE : Embeds G Q a b)
    {z : Fin w × Path} (hz : z ∈ cplNodes Q a b) : z.2 ∈ (G.tree z.1).nodes := by
  unfold cplNodes at hz
  rw [← couple_branchAddresses Q a b, ← couple_leafAddresses Q a b] at hz
  simp only [Finset.mem_union] at hz
  rcases hz with (h | h) | (h | h)
  · exact mem_nodes_of_branchAddresses hE.nodeA hE.treeA h
  · exact mem_nodes_of_branchAddresses hE.nodeB hE.treeB h
  · exact mem_nodes_of_leafAddresses hE.nodeA hE.treeA h
  · exact mem_nodes_of_leafAddresses hE.nodeB hE.treeB h

/-- Every carrier leaf below the roots of an embedded couple is one of its decoded leaves. -/
theorem Embeds.leaf_mem {Q : RegCpl} {a b : Fin w × Path} (hE : Embeds G Q a b) (ℓ : GLeaf G.tree)
    (hℓ : Under a ℓ.1 ∨ Under b ℓ.1) : ℓ.1 ∈ pairEndpoints (Q.pairsAt a b) := by
  rw [← couple_leafAddresses Q a b, Finset.mem_union]
  rcases hℓ with h | h
  · exact Or.inl (leafAddresses_of_leaf hE.nodeA hE.treeA ℓ h)
  · exact Or.inr (leafAddresses_of_leaf hE.nodeB hE.treeB ℓ h)

/-- Decoded leaves of an embedded couple are carrier leaves. -/
theorem Embeds.leaf_of_mem {Q : RegCpl} {a b : Fin w × Path} (hE : Embeds G Q a b)
    {z : Fin w × Path} (hz : z ∈ pairEndpoints (Q.pairsAt a b)) : z.2 ∈ (G.tree z.1).leaves := by
  rw [← couple_leafAddresses Q a b, Finset.mem_union] at hz
  rcases hz with h | h
  · obtain ⟨q, hq, rfl⟩ := mem_image_addrExt h
    exact (node_iff_of_subtree hE.nodeA hE.treeA q).2.1.2 hq
  · obtain ⟨q, hq, rfl⟩ := mem_image_addrExt h
    exact (node_iff_of_subtree hE.nodeB hE.treeB q).2.1.2 hq

/-! ### Components -/

theorem node_ext {r : Fin w × Path} {T : TTree} (hr : r.2 ∈ (G.tree r.1).nodes)
    (ht : (G.tree r.1).subtreeAt r.2 = T) {q : Path} (hq : q ∈ T.nodes) :
    (addrExt r q).2 ∈ (G.tree (addrExt r q).1).nodes :=
  (node_iff_of_subtree hr ht q).1.2 hq

theorem subtree_ext {r : Fin w × Path} (q : Path) :
    (G.tree (addrExt r q).1).subtreeAt (addrExt r q).2 = ((G.tree r.1).subtreeAt r.2).subtreeAt q := by
  simp [addrExt, subtreeAt_append]

theorem child_mem_nodes_node (l m r : TTree) (i : Fin 3) :
    [i] ∈ (TTree.node l m r).nodes := by
  rw [cons_mem_nodes_node]
  exact TTree.nil_mem_nodes _

theorem mem_nodes_node3 (f : Fin 3 → TTree) (i : Fin 3) (q : Path) (h : q ∈ (f i).nodes) :
    i :: q ∈ (node3 f).nodes := by
  show i :: q ∈ (TTree.node (f 0) (f 1) (f 2)).nodes
  rw [cons_mem_nodes_node]
  fin_cases i <;> exact h

theorem lonePath_append_mem : ∀ (X : RegChain) (ζ : ℤˣ) (h : TTree) (s : Path), s ∈ h.nodes →
    X.lonePath ++ s ∈ (X.plug ζ h).nodes
  | .nil, _, _, _, hs => hs
  | .pair m Qr Qg inner rest, ζ, h, s, hs => by
    simp only [RegChain.plug, RegChain.lonePath, List.append_assoc, List.cons_append,
      List.nil_append]
    apply mem_nodes_node3
    simp only [↓reduceIte]
    apply lonePath_append_mem inner
    apply mem_nodes_node3
    simp only [↓reduceIte]
    exact lonePath_append_mem rest _ h s hs

theorem lonePath_mem_plug (X : RegChain) (ζ : ℤˣ) (h : TTree) : X.lonePath ∈ (X.plug ζ h).nodes := by
  have := lonePath_append_mem X ζ h [] (TTree.nil_mem_nodes h)
  simpa using this

theorem child_facts {r : Fin w × Path} {l m n : TTree} (hr : r.2 ∈ (G.tree r.1).nodes)
    (ht : (G.tree r.1).subtreeAt r.2 = .node l m n) (i : Fin 3) :
    (addrExt r [i]).2 ∈ (G.tree (addrExt r [i]).1).nodes ∧
      (G.tree (addrExt r [i]).1).subtreeAt (addrExt r [i]).2 = ![l, m, n] i :=
  ⟨node_ext hr ht (child_mem_nodes_node l m n i), by rw [subtree_ext, ht]; rfl⟩

/-- Type 1: the three components. -/
theorem Embeds.type1 {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {a b : Fin w × Path}
    (hE : Embeds G (.type1 c Q₁ Q₂ Q₃) a b) :
    Embeds G Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) ∧
    Embeds G Q₂ (addrExt b [1]) (addrExt a [1]) ∧
    Embeds G Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) := by
  have pr := hE.pairs
  simp only [RegCpl.pairsAt, List.mem_append] at pr
  have tA : (G.tree a.1).subtreeAt a.2 = .node Q₁.trees.1 Q₂.trees.2 Q₃.trees.1 := hE.treeA
  have cA := child_facts hE.nodeA tA
  have hB : ∀ i : Fin 3, (addrExt b [i]).2 ∈ (G.tree (addrExt b [i]).1).nodes ∧
      (G.tree (addrExt b [i]).1).subtreeAt (addrExt b [i]).2 =
        (if c = 0 then ![Q₁.trees.2, Q₂.trees.1, Q₃.trees.2]
          else ![Q₃.trees.2, Q₂.trees.1, Q₁.trees.2]) i := by
    intro i
    have tB := hE.treeB
    simp only [RegCpl.trees] at tB
    split_ifs at tB ⊢ with hc
    · exact child_facts hE.nodeB tB i
    · exact child_facts hE.nodeB tB i
  have e0 : (if c = 0 then ![Q₁.trees.2, Q₂.trees.1, Q₃.trees.2]
      else ![Q₃.trees.2, Q₂.trees.1, Q₁.trees.2]) (c.partner 0) = Q₁.trees.2 := by
    fin_cases c <;> rfl
  have e1 : (if c = 0 then ![Q₁.trees.2, Q₂.trees.1, Q₃.trees.2]
      else ![Q₃.trees.2, Q₂.trees.1, Q₁.trees.2]) 1 = Q₂.trees.1 := by
    split_ifs <;> rfl
  have e2 : (if c = 0 then ![Q₁.trees.2, Q₂.trees.1, Q₃.trees.2]
      else ![Q₃.trees.2, Q₂.trees.1, Q₁.trees.2]) (c.partner 2) = Q₃.trees.2 := by
    fin_cases c <;> rfl
  exact ⟨⟨hE.indep.ext _ _, (cA 0).1, (hB _).1, (cA 0).2, (hB _).2.trans e0,
      fun p hp => pr p (Or.inl (Or.inl hp))⟩,
    ⟨hE.indep.symm.ext _ _, (hB 1).1, (cA 1).1, (hB 1).2.trans e1, (cA 1).2,
      fun p hp => pr p (Or.inl (Or.inr hp))⟩,
    ⟨hE.indep.ext _ _, (cA 2).1, (hB _).1, (cA 2).2, (hB _).2.trans e2,
      fun p hp => pr p (Or.inr hp)⟩⟩

/-- Type 2: the two chains and the lone-pair couple. -/
theorem Embeds.type2 {Xp Xm : RegChain} {Qlp : RegCpl} {a b : Fin w × Path}
    (hE : Embeds G (.type2 Xp Xm Qlp) a b) :
    ChainEmb G Xp 1 a Qlp.trees.1 ∧ ChainEmb G Xm (-1) b Qlp.trees.2 ∧
    Embeds G Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) := by
  have tA : (G.tree a.1).subtreeAt a.2 = Xp.plug 1 Qlp.trees.1 := hE.treeA
  have tB : (G.tree b.1).subtreeAt b.2 = Xm.plug (-1) Qlp.trees.2 := hE.treeB
  have pr := hE.pairs
  simp only [RegCpl.pairsAt, List.mem_append] at pr
  refine ⟨⟨hE.nodeA, tA, fun p hp => pr p (Or.inl (Or.inl hp))⟩,
    ⟨hE.nodeB, tB, fun p hp => pr p (Or.inl (Or.inr hp))⟩,
    ⟨hE.indep.ext _ _, node_ext hE.nodeA tA (lonePath_mem_plug _ _ _),
      node_ext hE.nodeB tB (lonePath_mem_plug _ _ _), ?_, ?_, fun p hp => pr p (Or.inr hp)⟩⟩
  · rw [subtree_ext, tA, plug_subtreeAt_lonePath]
  · rw [subtree_ext, tB, plug_subtreeAt_lonePath]

end WaveTurbulence.Links
