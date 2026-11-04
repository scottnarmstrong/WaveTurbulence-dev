/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.LayerReg.Embed

/-!
# Embedded chains and the layered carrier (packet C4)

* `ChainEmb.parts`: an embedded chain passes to its red and green couples (oriented as in the
  decoding), its inner chain and its remaining chain;
* `layerAt_le_of_under`: layers do not increase downwards (T Def `deflayer`);
* `parAt_child`, `layerAt_le_parAt`: parent layers (T Prop `canonequiv`, roots read as `p`);
* `Embeds.pair_layer`: paired leaves have equal layers;
* `crit_apply`: the canonicity criterion (ii) at two incomparable nodes of an embedded couple whose
  subtrees are closed under its decoded leaf pairs (`PairedUnder`).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {w : ℕ} {G : Garden w}

theorem red_sign' (m : MiniTreeCode) (ζ : ℤˣ) :
    slotSign (slotSign ζ m.c) m.red.2 = -slotSign ζ m.red.1 := by
  obtain ⟨c, b⟩ := m
  rcases Int.units_eq_one_or ζ with rfl | rfl <;> fin_cases c <;> fin_cases b <;> decide

theorem green_sign' (m : MiniTreeCode) (ζ : ℤˣ) :
    slotSign (slotSign ζ m.c) m.green.2 = -slotSign ζ m.green.1 := by
  obtain ⟨c, b⟩ := m
  rcases Int.units_eq_one_or ζ with rfl | rfl <;> fin_cases c <;> fin_cases b <;> decide

theorem green_ne_red_fst (m : MiniTreeCode) : m.green.1 ≠ m.red.1 := (red_ne_green m).symm

theorem red2_ne_lone' (m : MiniTreeCode) : m.red.2 ≠ m.lone := by
  obtain ⟨c, b⟩ := m; fin_cases c <;> fin_cases b <;> decide

theorem green2_ne_lone' (m : MiniTreeCode) : m.green.2 ≠ m.lone := by
  obtain ⟨c, b⟩ := m; fin_cases c <;> fin_cases b <;> decide

theorem green2_ne_red2 (m : MiniTreeCode) : m.green.2 ≠ m.red.2 := by
  obtain ⟨c, b⟩ := m; fin_cases c <;> fin_cases b <;> decide

theorem treeOfSign_one (T : TTree × TTree) : treeOfSign T 1 = T.1 := rfl

theorem treeOfSign_neg_one (T : TTree × TTree) : treeOfSign T (-1) = T.2 := by
  unfold treeOfSign; rw [ite_neg_of (by decide)]

/-- The bottom node of a chain pair's mini-tree, at `a.([c] ++ inner.lonePath)`, as the plugged subtree. -/
def pairBottom (m : MiniTreeCode) (Qr Qg : RegCpl) (rest : RegChain) (ζ : ℤˣ) (h : TTree) : TTree :=
  node3 fun k => if k = m.lone then rest.plug (slotSign (slotSign ζ m.c) k) h
    else if k = m.red.2 then treeOfSign Qr.trees (slotSign (slotSign ζ m.c) k)
    else treeOfSign Qg.trees (slotSign (slotSign ζ m.c) k)

theorem plug_pair_eq (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (ζ : ℤˣ) (h : TTree) :
    (RegChain.pair m Qr Qg inner rest).plug ζ h = node3 fun i =>
      if i = m.c then inner.plug (slotSign ζ m.c) (pairBottom m Qr Qg rest ζ h)
      else if i = m.red.1 then treeOfSign Qr.trees (slotSign ζ i)
      else treeOfSign Qg.trees (slotSign ζ i) := rfl

theorem plug_pair_bottom (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (ζ : ℤˣ)
    (h : TTree) (k : Fin 3) :
    ((RegChain.pair m Qr Qg inner rest).plug ζ h).subtreeAt ([m.c] ++ inner.lonePath ++ [k]) =
      (pairBottom m Qr Qg rest ζ h).subtreeAt [k] := by
  rw [plug_pair_eq, List.append_assoc, List.singleton_append, node3_subtreeAt]
  simp only [↓reduceIte]
  rw [subtreeAt_append, plug_subtreeAt_lonePath]

theorem pairBottom_sub (m : MiniTreeCode) (Qr Qg : RegCpl) (rest : RegChain) (ζ : ℤˣ) (h : TTree)
    (k : Fin 3) : (pairBottom m Qr Qg rest ζ h).subtreeAt [k] =
      if k = m.lone then rest.plug (slotSign (slotSign ζ m.c) k) h
      else if k = m.red.2 then treeOfSign Qr.trees (slotSign (slotSign ζ m.c) k)
      else treeOfSign Qg.trees (slotSign (slotSign ζ m.c) k) := by
  rw [pairBottom, node3_subtreeAt]; rfl

theorem plug_pair_top (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (ζ : ℤˣ)
    (h : TTree) (i : Fin 3) (hi : i ≠ m.c) :
    ((RegChain.pair m Qr Qg inner rest).plug ζ h).subtreeAt [i] =
      if i = m.red.1 then treeOfSign Qr.trees (slotSign ζ i) else treeOfSign Qg.trees (slotSign ζ i) := by
  rw [plug_pair_eq, node3_subtreeAt]
  simp only [hi, ↓reduceIte]
  rfl

theorem bottom_mem (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (ζ : ℤˣ) (h : TTree)
    (k : Fin 3) : [m.c] ++ inner.lonePath ++ [k] ∈ ((RegChain.pair m Qr Qg inner rest).plug ζ h).nodes := by
  rw [plug_pair_eq, List.append_assoc, List.singleton_append]
  apply mem_nodes_node3
  simp only [↓reduceIte]
  apply lonePath_append_mem
  exact child_mem_nodes_node _ _ _ _

theorem top_mem (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (ζ : ℤˣ) (h : TTree)
    (i : Fin 3) : [i] ∈ ((RegChain.pair m Qr Qg inner rest).plug ζ h).nodes :=
  child_mem_nodes_node _ _ _ _

/-- **An embedded chain passes to its components.** -/
theorem ChainEmb.parts {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} {ζ : ℤˣ}
    {a : Fin w × Path} {h : TTree} (hC : ChainEmb G (.pair m Qr Qg inner rest) ζ a h) :
    (if slotSign ζ m.red.1 = 1 then
        Embeds G Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Embeds G Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) ∧
    (if slotSign ζ m.green.1 = 1 then
        Embeds G Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else Embeds G Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) ∧
    ChainEmb G inner (slotSign ζ m.c) (addrExt a [m.c]) (pairBottom m Qr Qg rest ζ h) ∧
    ChainEmb G rest (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))
      h := by
  have pr := hC.pairs
  simp only [RegChain.pairsAt, List.mem_append] at pr
  have tr := hC.tree
  have nB : ∀ k, (addrExt a ([m.c] ++ inner.lonePath ++ [k])).2 ∈
      (G.tree (addrExt a ([m.c] ++ inner.lonePath ++ [k])).1).nodes :=
    fun k => node_ext hC.node tr (bottom_mem m Qr Qg inner rest ζ h k)
  have tB : ∀ k, (G.tree (addrExt a ([m.c] ++ inner.lonePath ++ [k])).1).subtreeAt
      (addrExt a ([m.c] ++ inner.lonePath ++ [k])).2 = (pairBottom m Qr Qg rest ζ h).subtreeAt [k] :=
    fun k => by rw [subtree_ext, tr, plug_pair_bottom]
  have nT : ∀ i, (addrExt a [i]).2 ∈ (G.tree (addrExt a [i]).1).nodes :=
    fun i => node_ext hC.node tr (top_mem m Qr Qg inner rest ζ h i)
  have tT : ∀ i, i ≠ m.c → (G.tree (addrExt a [i]).1).subtreeAt (addrExt a [i]).2 =
      if i = m.red.1 then treeOfSign Qr.trees (slotSign ζ i)
      else treeOfSign Qg.trees (slotSign ζ i) :=
    fun i hi => by rw [subtree_ext, tr, plug_pair_top _ _ _ _ _ _ _ _ hi]
  have bR : (pairBottom m Qr Qg rest ζ h).subtreeAt [m.red.2] =
      treeOfSign Qr.trees (-slotSign ζ m.red.1) := by
    rw [pairBottom_sub, ite_neg_of (red2_ne_lone' m), ite_pos_of rfl, red_sign']
  have bG : (pairBottom m Qr Qg rest ζ h).subtreeAt [m.green.2] =
      treeOfSign Qg.trees (-slotSign ζ m.green.1) := by
    rw [pairBottom_sub, ite_neg_of (green2_ne_lone' m), ite_neg_of (green2_ne_red2 m), green_sign']
  have tR : (G.tree (addrExt a [m.red.1]).1).subtreeAt (addrExt a [m.red.1]).2 =
      treeOfSign Qr.trees (slotSign ζ m.red.1) := by
    rw [tT _ (red_ne_c m), ite_pos_of rfl]
  have tG : (G.tree (addrExt a [m.green.1]).1).subtreeAt (addrExt a [m.green.1]).2 =
      treeOfSign Qg.trees (slotSign ζ m.green.1) := by
    rw [tT _ (green_ne_c m), ite_neg_of (green_ne_red_fst m)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · split_ifs with hs
    · refine ⟨indep_red m _ a, nT _, nB _, ?_, ?_, fun p hp => pr p (Or.inl (Or.inl (Or.inl ?_)))⟩
      · rw [tR, hs]; rfl
      · rw [tB, bR, hs]; exact treeOfSign_neg_one _
      · rwa [ite_pos_of hs]
    · have hs' := slotSign_eq_neg_one hs
      refine ⟨(indep_red m _ a).symm, nB _, nT _, ?_, ?_,
        fun p hp => pr p (Or.inl (Or.inl (Or.inl ?_)))⟩
      · rw [tB, bR, hs', neg_neg]; rfl
      · rw [tR, hs']; exact treeOfSign_neg_one _
      · rwa [ite_neg_of hs]
  · split_ifs with hs
    · refine ⟨indep_green m _ a, nT _, nB _, ?_, ?_, fun p hp => pr p (Or.inl (Or.inl (Or.inr ?_)))⟩
      · rw [tG, hs]; rfl
      · rw [tB, bG, hs]; exact treeOfSign_neg_one _
      · rwa [ite_pos_of hs]
    · have hs' := slotSign_eq_neg_one hs
      refine ⟨(indep_green m _ a).symm, nB _, nT _, ?_, ?_,
        fun p hp => pr p (Or.inl (Or.inl (Or.inr ?_)))⟩
      · rw [tB, bG, hs', neg_neg]; rfl
      · rw [tG, hs']; exact treeOfSign_neg_one _
      · rwa [ite_neg_of hs]
  · refine ⟨nT _, ?_, fun p hp => pr p (Or.inl (Or.inr hp))⟩
    rw [subtree_ext, tr, plug_pair_eq, node3_subtreeAt]
    simp only [↓reduceIte]
    rfl
  · refine ⟨nB _, ?_, fun p hp => pr p (Or.inr hp)⟩
    rw [tB, pairBottom_sub, ite_pos_of rfl]

/-! ### Layers on the carrier -/

variable (LG : LayeredGarden w) (p : ℕ)

/-- The parent layer at an address (a root's parent layer read as `p`; `0` away from the nodes). -/
def parAt (z : Fin w × Path) : ℕ :=
  if h : z.2 ∈ (LG.garden.tree z.1).nodes then LG.parentLayer p ⟨z, h⟩ else 0

theorem layerAt_of_mem {z : Fin w × Path} (h : z.2 ∈ (LG.garden.tree z.1).nodes) :
    layerAt LG z = LG.layer ⟨z, h⟩ := by
  unfold layerAt; simp only [h, ↓reduceDIte]

theorem parAt_of_mem {z : Fin w × Path} (h : z.2 ∈ (LG.garden.tree z.1).nodes) :
    parAt LG p z = LG.parentLayer p ⟨z, h⟩ := by
  unfold parAt; simp only [h, ↓reduceDIte]

/-- Layers do not increase from a node to its descendants (T Def `deflayer`). -/
theorem layer_le_of_isDesc' {a c : GNode LG.garden.tree} (h : a.IsDesc c) :
    LG.layer c ≤ LG.layer a := by
  obtain ⟨hj, q, hq⟩ := h
  induction q using List.reverseRecOn generalizing c with
  | nil =>
    have : c = a := Subtype.ext (Prod.ext hj.symm (by simpa using hq.symm))
    rw [this]
  | append_singleton q i ih =>
    have hmem : a.1.2 ++ q ++ [i] ∈ (LG.garden.tree c.1.1).nodes := by
      rw [← List.append_assoc] at hq
      rw [hq]
      exact c.2
    let b : GBranch LG.garden.tree :=
      ⟨(c.1.1, a.1.2 ++ q), Comb.TreePath.branching_of_append_mem _ hmem⟩
    have hcb : c = b.child i := by
      apply Subtype.ext
      refine Prod.ext rfl ?_
      simp only [GBranch.child, b]
      rw [← hq, List.append_assoc]
    rw [hcb]
    refine (LG.isLayering.1 b i).trans (ih (c := b.toNode) hj ?_)
    rfl

/-- **Layers do not increase downwards.** -/
theorem layerAt_le_of_under {x z : Fin w × Path} (hx : x.2 ∈ (LG.garden.tree x.1).nodes)
    (hz : z.2 ∈ (LG.garden.tree z.1).nodes) (h : Under x z) : layerAt LG z ≤ layerAt LG x := by
  rw [layerAt_of_mem LG hx, layerAt_of_mem LG hz]
  exact layer_le_of_isDesc' LG h

/-- The parent layer of a child is the layer of its parent. -/
theorem parAt_child {x : Fin w × Path} (i : Fin 3)
    (h : (addrExt x [i]).2 ∈ (LG.garden.tree (addrExt x [i]).1).nodes) :
    parAt LG p (addrExt x [i]) = layerAt LG x := by
  have hx : x.2 ∈ (LG.garden.tree x.1).nodes := by
    have := TTree.dropLast_mem_nodes _ h
    simpa [addrExt] using this
  rw [parAt_of_mem LG p h, layerAt_of_mem LG hx]
  unfold LayeredGarden.parentLayer
  rw [ite_neg_of (by simp [addrExt])]
  congr 1
  apply Subtype.ext
  simp [addrExt]

/-- A node's layer is at most its parent layer (for a root: at most `p`, criterion (i)). -/
theorem layerAt_le_parAt (hp : ∀ a, LG.layer a ≤ p) {z : Fin w × Path}
    (h : z.2 ∈ (LG.garden.tree z.1).nodes) : layerAt LG z ≤ parAt LG p z := by
  rw [parAt_of_mem LG p h, layerAt_of_mem LG h]
  unfold LayeredGarden.parentLayer
  split_ifs with hr
  · exact hp _
  · apply layer_le_of_isDesc'
    exact ⟨rfl, List.dropLast_prefix _⟩

/-- Paired leaves of an embedded couple have equal layers. -/
theorem Embeds.pair_layer {Q : RegCpl} {a b : Fin w × Path} (hE : Embeds LG.garden Q a b)
    {q : (Fin w × Path) × (Fin w × Path)} (hq : q ∈ Q.pairsAt a b) :
    layerAt LG q.1 = layerAt LG q.2 := by
  have h1 : q.1 ∈ pairEndpoints (Q.pairsAt a b) := (mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩
  have l1 := hE.leaf_of_mem h1
  have hp := hE.pairs q hq ⟨q.1, l1⟩ rfl
  have n1 := TTree.leaves_subset_nodes _ l1
  have n2 : q.2.2 ∈ (LG.garden.tree q.2.1).nodes := by
    rw [← hp]; exact TTree.leaves_subset_nodes _ (LG.garden.pair ⟨q.1, l1⟩).2
  rw [layerAt_of_mem LG n1, layerAt_of_mem LG n2]
  let ℓ₁ : GLeaf LG.garden.tree := ⟨q.1, l1⟩
  have e1 : (⟨q.1, n1⟩ : GNode LG.garden.tree) = GLeaf.toNode ℓ₁ := rfl
  have e2 : (⟨q.2, n2⟩ : GNode LG.garden.tree) = GLeaf.toNode (LG.garden.pair ℓ₁) :=
    Subtype.ext hp.symm
  rw [e1, e2]
  exact LG.isLayering.2 _

/-! ### The canonicity criterion inside an embedded couple -/

/-- No decoded pair leaves the union of the subtrees at `x` and `y`. -/
def PairedUnder (P : List ((Fin w × Path) × (Fin w × Path))) (x y : Fin w × Path) : Prop :=
  ∀ q ∈ P, (Under x q.1 ∨ Under y q.1) ↔ (Under x q.2 ∨ Under y q.2)

/-- **The canonicity criterion (ii) inside an embedded couple.** -/
theorem crit_apply {LG : LayeredGarden w} {p : ℕ} (hcan : LG.CanonCriterion p)
    (hplain : LG.garden.IsPlain) {Q : RegCpl} {a b : Fin w × Path} (hE : Embeds LG.garden Q a b)
    {x y : Fin w × Path} (hx : x.2 ∈ (LG.garden.tree x.1).nodes)
    (hy : y.2 ∈ (LG.garden.tree y.1).nodes) (hxr : Under a x ∨ Under b x)
    (hyr : Under a y ∨ Under b y) (hind : Indep x y) (hpu : PairedUnder (Q.pairsAt a b) x y) :
    min (parAt LG p x) (parAt LG p y) ≤ max (layerAt LG x) (layerAt LG y) := by
  classical
  rw [parAt_of_mem LG p hx, parAt_of_mem LG p hy, layerAt_of_mem LG hx, layerAt_of_mem LG hy]
  refine hcan.2 ⟨x, hx⟩ ⟨y, hy⟩ ⟨hind.1, hind.2⟩ ?_
  intro ℓ hℓ
  have hmem : ∀ ℓ' : GLeaf LG.garden.tree,
      ℓ' ∈ (GNode.leavesBelow ⟨x, hx⟩ ∪ GNode.leavesBelow ⟨y, hy⟩) ↔ (Under x ℓ'.1 ∨ Under y ℓ'.1) := by
    intro ℓ'
    simp only [GNode.leavesBelow, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [hmem] at hℓ
  refine ⟨fun h => ((LG.garden.pair_eq_iff ℓ).1 h) (hplain ℓ), ?_⟩
  rw [hmem]
  have hab : Under a ℓ.1 ∨ Under b ℓ.1 := by
    rcases hℓ with h | h
    · rcases hxr with h' | h'
      · exact Or.inl (under_trans h' h)
      · exact Or.inr (under_trans h' h)
    · rcases hyr with h' | h'
      · exact Or.inl (under_trans h' h)
      · exact Or.inr (under_trans h' h)
  obtain ⟨q, hq, hqe⟩ := (mem_pairEndpoints_iff _ _).1 (hE.leaf_mem ℓ hab)
  rcases hqe with e | e
  · have hp := hE.pairs q hq ℓ e
    rw [hp]
    exact (hpu q hq).1 (e ▸ hℓ)
  · have l1 := hE.leaf_of_mem ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩)
    let ℓ' : GLeaf LG.garden.tree := ⟨q.1, l1⟩
    have hp := hE.pairs q hq ℓ' rfl
    have hpl : LG.garden.pair ℓ' = ℓ := Subtype.ext (hp.trans e.symm)
    have : LG.garden.pair ℓ = ℓ' := by rw [← hpl]; exact LG.garden.pair_pair ℓ'
    rw [this]
    exact (hpu q hq).2 (e ▸ hℓ)

end WaveTurbulence.Links
