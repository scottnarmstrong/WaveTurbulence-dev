/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.LayerReg2

/-!
# TARGET Prop `layerreg1`, part (2): coherent regular couples only matter through `(q, q')`

TARGET L905–L907: "if we fix `(q, q')` and the structure and layering of the rest of the garden, but
replace the regular couple `𝒬` by any other regular couple with layering satisfying all the above
assumptions, then the resulting garden also belongs to `𝒢_{p+1}`." Its proof shows that the
canonicity criterion of a garden containing such a couple is equivalent to the criterion of the garden
in which the couple is collapsed to a leaf pair in layer `min(q, q')`.

Here: `LayerPattern` is the layering described in part (1) (coherent; trivial or type 1: one layer
`r = min(q, q')`; type 2: `𝒬_lp` in layer `r`, every chain pair with its couples in one layer, all
chain nodes between `r` and the parent layer of their root). **`layerreg1_part2`**: for a layered garden with all layers `≤ p` and an
embedded regular couple with `LayerPattern`,

  `CanonCriterion p ↔ CritOut ∧ CritAttach r`,

where `CritOut` is the criterion (ii) for pairs of nodes outside the subtrees at the roots `a, b`, and
`CritAttach r` is the criterion (ii) at `a` or `b` against an outside node, with the layer of the root
read as `r` (the collapsed leaf pair). Neither side of the right-hand side looks inside the couple, so
any two couples with `LayerPattern` and the same `(q, q')` give the same answer.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {w : ℕ}

/-- `z` lies in one of the subtrees at `a`, `b`. -/
def InRegion (a b z : Fin w × Path) : Prop := Under a z ∨ Under b z

variable (LG : LayeredGarden w) (p : ℕ)

/-- **The criterion (ii) away from the embedded couple.** -/
def CritOut (a b : Fin w × Path) : Prop :=
  ∀ x y : GNode LG.garden.tree, ¬ InRegion a b x.1 → ¬ InRegion a b y.1 → x.Incomparable y →
    LG.garden.CompletelyPaired (x.leavesBelow ∪ y.leavesBelow) →
    min (LG.parentLayer p x) (LG.parentLayer p y) ≤ max (LG.layer x) (LG.layer y)

/-- **The criterion (ii) at the roots, the couple collapsed to a leaf pair in layer `r`.** -/
def CritAttach (a b : Fin w × Path) (r : ℕ) : Prop :=
  ∀ x y : GNode LG.garden.tree, (x.1 = a ∨ x.1 = b) → ¬ InRegion a b y.1 → x.Incomparable y →
    LG.garden.CompletelyPaired (x.leavesBelow ∪ y.leavesBelow) →
    min (LG.parentLayer p x) (LG.parentLayer p y) ≤ max r (LG.layer y)

/-- **The layering of TARGET `layerreg1` (1)** on an embedded regular couple. -/
def LayerPattern (Q : RegCpl) (a b : Fin w × Path) : Prop :=
  CohOn LG (Q.linksAt a b) ∧
  match Q with
  | .type2 Xp Xm Qlp =>
    (∀ z ∈ cplNodes Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath),
      layerAt LG z = min (parAt LG p a) (parAt LG p b)) ∧
    ChainPairLayers LG Xp 1 a ∧ ChainPairLayers LG Xm (-1) b ∧
    (∀ z ∈ chainNodesSet Xp 1 a,
      min (parAt LG p a) (parAt LG p b) ≤ layerAt LG z ∧ layerAt LG z ≤ parAt LG p a) ∧
    (∀ z ∈ chainNodesSet Xm (-1) b,
      min (parAt LG p a) (parAt LG p b) ≤ layerAt LG z ∧ layerAt LG z ≤ parAt LG p b)
  | Q => ∀ z ∈ cplNodes Q a b, layerAt LG z = min (parAt LG p a) (parAt LG p b)

variable {LG p}

/-- **Part (1) gives the pattern.** -/
theorem layerPattern_of_canon (hcan : LG.CanonCriterion p) (hplain : LG.garden.IsPlain)
    {Q : RegCpl} {a b : Fin w × Path} (hwf : Q.wf = true) (hE : Embeds LG.garden Q a b)
    (hcoh : CohOn LG (Q.linksAt a b)) : LayerPattern LG p Q a b := by
  refine ⟨hcoh, ?_⟩
  cases Q with
  | triv => exact layerreg1_type1 hcan hplain hwf hE hcoh rfl
  | type1 c Q₁ Q₂ Q₃ => exact layerreg1_type1 hcan hplain hwf hE hcoh rfl
  | type2 Xp Xm Qlp =>
    exact layerreg1_type2 hcan hplain hwf hE hcoh

/-! ### Cross pairs -/

/-- Every couple has a leaf pair between its two trees. -/
theorem exists_cross_pair : ∀ (Q : RegCpl) (a b : Fin w × Path),
    ∃ q ∈ Q.pairsAt a b, (Under a q.1 ∧ Under b q.2) ∨ (Under b q.1 ∧ Under a q.2)
  | .triv, a, b => ⟨(a, b), by simp [RegCpl.pairsAt], Or.inl ⟨under_refl _, under_refl _⟩⟩
  | .type1 c Q₁ Q₂ Q₃, a, b => by
    obtain ⟨q, hq, h⟩ := exists_cross_pair Q₂ (addrExt b [1]) (addrExt a [1])
    refine ⟨q, by simp only [RegCpl.pairsAt, List.mem_append]; exact Or.inl (Or.inr hq), ?_⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨under_trans (under_ext _ _) h1, under_trans (under_ext _ _) h2⟩
    · exact Or.inl ⟨under_trans (under_ext _ _) h1, under_trans (under_ext _ _) h2⟩
  | .type2 Xp Xm Qlp, a, b => by
    obtain ⟨q, hq, h⟩ := exists_cross_pair Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)
    refine ⟨q, by simp only [RegCpl.pairsAt, List.mem_append]; exact Or.inr hq, ?_⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨under_trans (under_ext _ _) h1, under_trans (under_ext _ _) h2⟩
    · exact Or.inr ⟨under_trans (under_ext _ _) h1, under_trans (under_ext _ _) h2⟩


/-- A leaf pair crossing between the subtrees at `x` and `y`. -/
def Crosses (q : (Fin w × Path) × (Fin w × Path)) (x y : Fin w × Path) : Prop :=
  (Under x q.1 ∧ Under y q.2) ∨ (Under y q.1 ∧ Under x q.2)

theorem Crosses.symm {q : (Fin w × Path) × (Fin w × Path)} {x y : Fin w × Path} (h : Crosses q x y) :
    Crosses q y x := Or.symm h

/-! ### Addresses -/

theorem self_mem_spinePos : ∀ (X : RegChain) (a : Fin w × Path), a ∈ spinePos X a
  | .nil, _ => List.mem_singleton_self _
  | .pair .., _ => List.mem_cons_self

theorem ne_of_under_ext {u z : Fin w × Path} {q : Path} (hq : q ≠ []) (h : Under (addrExt u q) z) :
    z ≠ u := by
  rintro rfl
  have h2 := h.2.length_le
  simp only [addrExt, List.length_append] at h2
  exact hq (List.eq_nil_of_length_eq_zero (by omega))

/-- An address above a point of the subtree at `c`, but not below `c`, is above `c`. -/
theorem under_of_out {c y z : Fin w × Path} (hc : ¬ Under c y) (hcz : Under c z) (h : Under y z) :
    Under y c :=
  (under_total h hcz).resolve_right hc

theorem region_of_child {a b x z : Fin w × Path} {k : Fin 3} (e : z = addrExt x [k])
    (h : InRegion a b x) : InRegion a b z := by
  subst e
  rcases h with h | h
  · exact Or.inl (under_trans h (under_ext _ _))
  · exact Or.inr (under_trans h (under_ext _ _))

/-- The parent of a root of an embedded couple lies outside its region. -/
theorem root_parent_out {a b x : Fin w × Path} {k : Fin 3} (hab : Indep a b) (e : a = addrExt x [k]) :
    ¬ InRegion a b x := by
  rintro (h | h)
  · subst e; exact ne_of_under_ext (by simp) h rfl
  · exact hab.2 (by rw [e]; exact under_trans h (under_ext _ _))

theorem oriented_under {P : Prop} [Decidable P] {Q : RegCpl} {x y z : Fin w × Path}
    (h : z ∈ orientedNodes P Q x y) : Under x z ∨ Under y z := by
  unfold orientedNodes at h
  split_ifs at h
  · exact cpl_endpoints_under Q x y z h
  · exact (cpl_endpoints_under Q y x z h).symm

/-! ### Leaves of an embedded couple -/

section Garden

variable {G : Garden w}

/-- The partner of a leaf below the roots of an embedded couple is given by a decoded pair. -/
theorem Embeds.partner {Q : RegCpl} {a b : Fin w × Path} (hE : Embeds G Q a b) (ℓ : GLeaf G.tree)
    (hℓ : InRegion a b ℓ.1) : ∃ q ∈ Q.pairsAt a b,
      (ℓ.1 = q.1 ∧ (G.pair ℓ).1 = q.2) ∨ (ℓ.1 = q.2 ∧ (G.pair ℓ).1 = q.1) := by
  obtain ⟨q, hq, hqe⟩ := (mem_pairEndpoints_iff _ _).1 (hE.leaf_mem ℓ hℓ)
  refine ⟨q, hq, ?_⟩
  rcases hqe with e | e
  · exact Or.inl ⟨e, hE.pairs q hq ℓ e⟩
  · have l1 := hE.leaf_of_mem ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩)
    let ℓ' : GLeaf G.tree := ⟨q.1, l1⟩
    have hp := hE.pairs q hq ℓ' rfl
    have hpl : G.pair ℓ' = ℓ := Subtype.ext (hp.trans e.symm)
    have : G.pair ℓ = ℓ' := by rw [← hpl]; exact G.pair_pair ℓ'
    exact Or.inr ⟨e, by rw [this]⟩

/-- **The region of an embedded couple is closed under the pairing.** -/
theorem Embeds.pair_region {Q : RegCpl} {a b : Fin w × Path} (hE : Embeds G Q a b) (ℓ : GLeaf G.tree)
    (hℓ : InRegion a b ℓ.1) : InRegion a b (G.pair ℓ).1 := by
  obtain ⟨q, hq, h⟩ := hE.partner ℓ hℓ
  have r1 := cpl_endpoints_under Q a b q.1
    (Finset.mem_union_right _ ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩))
  have r2 := cpl_endpoints_under Q a b q.2
    (Finset.mem_union_right _ ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inr rfl⟩))
  rcases h with ⟨-, e⟩ | ⟨-, e⟩
  · rw [e]; exact r2
  · rw [e]; exact r1

theorem Embeds.pair_out {Q : RegCpl} {a b : Fin w × Path} (hE : Embeds G Q a b) (ℓ : GLeaf G.tree)
    (hℓ : ¬ InRegion a b ℓ.1) : ¬ InRegion a b (G.pair ℓ).1 := by
  intro h
  have := hE.pair_region (G.pair ℓ) h
  rw [G.pair_pair] at this
  exact hℓ this

/-- A crossing decoded pair gives a crossing leaf. -/
theorem Embeds.cross_leaf {Q : RegCpl} {a b x y : Fin w × Path} (hE : Embeds G Q a b)
    (h : ∃ q ∈ Q.pairsAt a b, Crosses q x y) :
    ∃ ℓ : GLeaf G.tree, Under x ℓ.1 ∧ Under y (G.pair ℓ).1 := by
  obtain ⟨q, hq, hc⟩ := h
  have l1 := hE.leaf_of_mem ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩)
  let ℓ₁ : GLeaf G.tree := ⟨q.1, l1⟩
  have hp : (G.pair ℓ₁).1 = q.2 := hE.pairs q hq ℓ₁ rfl
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨ℓ₁, h1, by rw [hp]; exact h2⟩
  · refine ⟨G.pair ℓ₁, by rw [hp]; exact h2, ?_⟩
    rw [G.pair_pair]; exact h1

/-- **Every node of the region is a node of the embedded couple.** -/
theorem Embeds.mem_cplNodes {Q : RegCpl} {a b : Fin w × Path} (hE : Embeds G Q a b)
    {z : Fin w × Path} (hz : z.2 ∈ (G.tree z.1).nodes) (hr : InRegion a b z) : z ∈ cplNodes Q a b := by
  unfold cplNodes
  rw [← couple_branchAddresses Q a b, ← couple_leafAddresses Q a b]
  simp only [Finset.mem_union]
  rcases hr with h | h
  · obtain ⟨q, rfl⟩ := under_of_addrExt h
    have hq := (node_iff_of_subtree hE.nodeA hE.treeA q).1.1 hz
    rcases (Comb.TreePath.mem_nodes_iff _ _).1 hq with hl | hb
    · exact Or.inr (Or.inl (addrExt_mem_image a q hl))
    · exact Or.inl (Or.inl (addrExt_mem_image a q hb))
  · obtain ⟨q, rfl⟩ := under_of_addrExt h
    have hq := (node_iff_of_subtree hE.nodeB hE.treeB q).1.1 hz
    rcases (Comb.TreePath.mem_nodes_iff _ _).1 hq with hl | hb
    · exact Or.inr (Or.inr (addrExt_mem_image b q hl))
    · exact Or.inl (Or.inr (addrExt_mem_image b q hb))

theorem Embeds.pu_leaf {Q : RegCpl} {a b : Fin w × Path} (hE : Embeds G Q a b) {x y : Fin w × Path}
    (hpu : PairedUnder (Q.pairsAt a b) x y) (ℓ : GLeaf G.tree) (hr : InRegion a b ℓ.1)
    (h : Under x ℓ.1 ∨ Under y ℓ.1) : Under x (G.pair ℓ).1 ∨ Under y (G.pair ℓ).1 := by
  obtain ⟨q, hq, e⟩ := hE.partner ℓ hr
  rcases e with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e2]; exact (hpu q hq).1 (by rw [← e1]; exact h)
  · rw [e2]; exact (hpu q hq).2 (by rw [← e1]; exact h)

theorem mem_leavesBelow_union (x y : GNode G.tree) (ℓ : GLeaf G.tree) :
    ℓ ∈ x.leavesBelow ∪ y.leavesBelow ↔ (Under x.1 ℓ.1 ∨ Under y.1 ℓ.1) := by
  simp only [GNode.leavesBelow, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem cp_of (hplain : G.IsPlain) (x y : GNode G.tree)
    (h : ∀ ℓ : GLeaf G.tree, (Under x.1 ℓ.1 ∨ Under y.1 ℓ.1) →
      (Under x.1 (G.pair ℓ).1 ∨ Under y.1 (G.pair ℓ).1)) :
    G.CompletelyPaired (x.leavesBelow ∪ y.leavesBelow) := by
  intro ℓ hℓ
  rw [mem_leavesBelow_union] at hℓ
  exact ⟨fun e => ((G.pair_eq_iff ℓ).1 e) (hplain ℓ), (mem_leavesBelow_union _ _ _).2 (h ℓ hℓ)⟩

theorem cp_to {x y : GNode G.tree} (h : G.CompletelyPaired (x.leavesBelow ∪ y.leavesBelow))
    (ℓ : GLeaf G.tree) (hℓ : Under x.1 ℓ.1 ∨ Under y.1 ℓ.1) :
    Under x.1 (G.pair ℓ).1 ∨ Under y.1 (G.pair ℓ).1 :=
  (mem_leavesBelow_union _ _ _).1 (h ℓ ((mem_leavesBelow_union _ _ _).2 hℓ)).2

/-- **Completely paired sets around an embedded couple.** For a set of leaves cut out by an address
predicate `σ` that is constant on the subtrees at `a` and `b`, complete pairing only depends on the
leaves outside these subtrees and on whether both or neither subtree is taken (a regular couple has a leaf
pair between its two trees). -/
theorem cp_iff (hplain : G.IsPlain) {Q : RegCpl} {a b : Fin w × Path} (hE : Embeds G Q a b)
    (σ : Fin w × Path → Prop) (hsa : ∀ z, Under a z → (σ z ↔ σ a))
    (hsb : ∀ z, Under b z → (σ z ↔ σ b)) (S : Finset (GLeaf G.tree)) (hS : ∀ ℓ, ℓ ∈ S ↔ σ ℓ.1) :
    G.CompletelyPaired S ↔
      (∀ ℓ : GLeaf G.tree, ¬ InRegion a b ℓ.1 → σ ℓ.1 → σ (G.pair ℓ).1) ∧ (σ a ↔ σ b) := by
  obtain ⟨ℓ₀, h₁, h₂⟩ := hE.cross_leaf (exists_cross_pair Q a b)
  constructor
  · intro hcp
    have cl : ∀ ℓ : GLeaf G.tree, σ ℓ.1 → σ (G.pair ℓ).1 := fun ℓ h =>
      (hS _).1 (hcp ℓ ((hS ℓ).2 h)).2
    refine ⟨fun ℓ _ h => cl ℓ h, fun ha => ?_, fun hb => ?_⟩
    · exact (hsb _ h₂).1 (cl ℓ₀ ((hsa _ h₁).2 ha))
    · have := cl (G.pair ℓ₀) ((hsb _ h₂).2 hb)
      rw [G.pair_pair] at this
      exact (hsa _ h₁).1 this
  · rintro ⟨hout, hab⟩ ℓ hℓ
    refine ⟨fun e => ((G.pair_eq_iff ℓ).1 e) (hplain ℓ), (hS _).2 ?_⟩
    have hσ := (hS ℓ).1 hℓ
    by_cases hr : InRegion a b ℓ.1
    · have hσr : σ a ∧ σ b := by
        rcases hr with h | h
        · have := (hsa _ h).1 hσ; exact ⟨this, hab.1 this⟩
        · have := (hsb _ h).1 hσ; exact ⟨hab.2 this, this⟩
      rcases hE.pair_region ℓ hr with h | h
      · exact (hsa _ h).2 hσr.1
      · exact (hsb _ h).2 hσr.2
    · exact hout ℓ hr hσ

end Garden

/-! ### Flat nodes -/

variable {LG : LayeredGarden w} {p : ℕ}

theorem parAt_node (LG : LayeredGarden w) (p : ℕ) (x : GNode LG.garden.tree) :
    parAt LG p x.1 = LG.parentLayer p x :=
  parAt_of_mem LG p x.2

theorem layerAt_le_parAt_of_ne {z : Fin w × Path} (h : z.2 ∈ (LG.garden.tree z.1).nodes)
    (hz : z.2 ≠ []) : layerAt LG z ≤ parAt LG p z := by
  rw [parAt_of_mem LG p h, layerAt_of_mem LG h]
  unfold LayeredGarden.parentLayer
  split_ifs with hr
  · exact absurd hr hz
  · apply layer_le_of_isDesc'
    exact ⟨rfl, List.dropLast_prefix _⟩

/-- **A node in the layer of one of its strict ancestors is flat** (its layer is its parent layer). -/
theorem flat_of_anc {u z : Fin w × Path} (hu : u.2 ∈ (LG.garden.tree u.1).nodes)
    (hz : z.2 ∈ (LG.garden.tree z.1).nodes) (h : Under u z) (hne : z ≠ u)
    (he : layerAt LG z = layerAt LG u) : parAt LG p z = layerAt LG z := by
  have hz0 : z.2 ≠ [] := by
    intro h0
    obtain ⟨e1, q, hq⟩ := h
    rw [h0, List.append_eq_nil_iff] at hq
    exact hne (Prod.ext e1.symm (by rw [h0, hq.1]))
  exact le_antisymm ((parAt_le_of_sunder LG p hu hz h hne).trans he.ge) (layerAt_le_parAt_of_ne hz hz0)

/-- **Away from the spine, an embedded chain with `ChainPairLayers` is flat.** -/
theorem chain_flat : ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (h : TTree),
    ChainEmb LG.garden X ζ a h → ChainPairLayers LG X ζ a →
    ∀ z ∈ chainNodesSet X ζ a, Under z (addrExt a X.lonePath) ∨ parAt LG p z = layerAt LG z
  | .nil, _, _, _, _, _, z, hz => by simp [chainNodesSet, RegChain.linksAt, RegChain.pairsAt] at hz
  | .pair m Qr Qg inner rest, ζ, a, h, hC, hL, z, hz => by
    obtain ⟨-, -, EI, ES⟩ := hC.parts
    obtain ⟨hnb, hR, hG, hI, hS⟩ := hL
    have hzn := hC.mem_nodes hz
    have lone_eq : addrExt a (RegChain.pair m Qr Qg inner rest).lonePath =
        addrExt (addrExt a ([m.c] ++ inner.lonePath)) ([m.lone] ++ rest.lonePath) := by
      simp [RegChain.lonePath, addrExt_append]
    rcases mem_chainNodesSet_pair hz with rfl | rfl | h' | h' | h' | h'
    · exact Or.inl (under_ext _ _)
    · left; rw [lone_eq]; exact under_ext _ _
    · right
      have hl := hR z h'
      rcases oriented_under h' with hu | hu
      · exact flat_of_anc hC.node hzn (under_trans (under_ext _ _) hu) (ne_of_under_ext (by simp) hu) hl
      · exact flat_of_anc hC.node hzn (under_trans (under_ext _ _) hu) (ne_of_under_ext (by simp) hu) hl
    · right
      have hl := hG z h'
      rcases oriented_under h' with hu | hu
      · exact flat_of_anc hC.node hzn (under_trans (under_ext _ _) hu) (ne_of_under_ext (by simp) hu) hl
      · exact flat_of_anc hC.node hzn (under_trans (under_ext _ _) hu) (ne_of_under_ext (by simp) hu) hl
    · right
      have hza : Under (addrExt a [m.c]) z := (chain_endpoints_region inner _ _ z h').1
      have lo := chain_lower inner _ _ _ EI hI z h'
      rw [addrExt_append] at lo
      have up := layerAt_le_of_under LG hC.node hzn (under_trans (under_ext _ _) hza)
      exact flat_of_anc hC.node hzn (under_trans (under_ext _ _) hza) (ne_of_under_ext (by simp) hza)
        (by omega)
    · have := chain_flat rest _ _ h ES hS z h'
      rwa [← chain_lonePath_eq] at this

/-- **The cut below a threshold** (proof of TARGET `layerreg1` (2)): if the lone position of a chain
with `ChainPairLayers` is below `t ≤` the parent layer of its root, some spine position is below `t`
while its parent is not. -/
theorem spine_cut_lt : ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (h : TTree),
    ChainEmb LG.garden X ζ a h → ChainPairLayers LG X ζ a →
    ∀ t : ℕ, layerAt LG (addrExt a X.lonePath) < t → t ≤ parAt LG p a →
      ∃ s ∈ spinePos X a, layerAt LG s < t ∧ t ≤ parAt LG p s
  | .nil, _, a, _, _, _, t, hl, hP => ⟨a, List.mem_singleton_self _, by
      rwa [RegChain.lonePath, addrExt_nil] at hl, hP⟩
  | .pair m Qr Qg inner rest, ζ, a, h, hC, hL, t, hl, hP => by
    by_cases ha : layerAt LG a < t
    · exact ⟨a, List.mem_cons_self, ha, hP⟩
    · obtain ⟨-, -, -, hR⟩ := hC.parts
      obtain ⟨hnb, -, -, -, hS⟩ := hL
      have e : addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]) =
          addrExt (addrExt a ([m.c] ++ inner.lonePath)) [m.lone] := by rw [addrExt_append]
      have hpar : parAt LG p (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) =
          layerAt LG (addrExt a ([m.c] ++ inner.lonePath)) := by
        rw [e]; exact parAt_child LG p _ (e ▸ hR.node)
      have hl' : layerAt LG (addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath)
          < t := by rw [← chain_lonePath_eq]; exact hl
      obtain ⟨s, hs, hs1, hs2⟩ := spine_cut_lt rest _ _ h hR hS t hl' (by rw [hpar, hnb]; omega)
      exact ⟨s, List.mem_cons_of_mem _ hs, hs1, hs2⟩

/-! ### What the characterization uses from the layer pattern -/

/-- **The facts about a layered embedded couple used by the characterization.** With
`r = min(q, q')`: (lower) the region is in layers `≥ r`; (spine) there are spine ends `eA`, `eB` below `a`,
`b` with a leaf pair between them, and every node of the region off the paths `a → eA`, `b → eB` is
flat; (cut) for every `r < t ≤ q` there is a node below `a` in layer `< t` with parent layer `≥ t` whose
subtree, together with the subtree at `b`, is closed under the pairs of the couple (and symmetrically);
(upper) the roots are not above their parents. -/
structure PatternFacts (LG : LayeredGarden w) (p : ℕ) (Q : RegCpl) (a b : Fin w × Path) : Prop where
  lower : ∀ z : Fin w × Path, z.2 ∈ (LG.garden.tree z.1).nodes → InRegion a b z →
    min (parAt LG p a) (parAt LG p b) ≤ layerAt LG z
  spine : ∃ eA eB : Fin w × Path, Under a eA ∧ Under b eB ∧ (∃ q ∈ Q.pairsAt a b, Crosses q eA eB) ∧
    (∀ z : Fin w × Path, z.2 ∈ (LG.garden.tree z.1).nodes → Under a z →
      Under z eA ∨ parAt LG p z = layerAt LG z) ∧
    (∀ z : Fin w × Path, z.2 ∈ (LG.garden.tree z.1).nodes → Under b z →
      Under z eB ∨ parAt LG p z = layerAt LG z)
  cutA : ∀ t : ℕ, min (parAt LG p a) (parAt LG p b) < t → t ≤ parAt LG p a →
    ∃ s : Fin w × Path, s.2 ∈ (LG.garden.tree s.1).nodes ∧ Under a s ∧ layerAt LG s < t ∧
      t ≤ parAt LG p s ∧ PairedUnder (Q.pairsAt a b) s b
  cutB : ∀ t : ℕ, min (parAt LG p a) (parAt LG p b) < t → t ≤ parAt LG p b →
    ∃ s : Fin w × Path, s.2 ∈ (LG.garden.tree s.1).nodes ∧ Under b s ∧ layerAt LG s < t ∧
      t ≤ parAt LG p s ∧ PairedUnder (Q.pairsAt a b) a s
  upper : layerAt LG a ≤ parAt LG p a ∧ layerAt LG b ≤ parAt LG p b

/-- Single-layer couples (trivial and type 1). -/
theorem patternFacts_flat {Q : RegCpl} {a b : Fin w × Path} (hE : Embeds LG.garden Q a b)
    (hL : ∀ z ∈ cplNodes Q a b, layerAt LG z = min (parAt LG p a) (parAt LG p b)) :
    PatternFacts LG p Q a b := by
  have La := hL a (left_mem_cplNodes Q a b)
  have Lb := hL b (right_mem_cplNodes Q a b)
  have hpu : PairedUnder (Q.pairsAt a b) a b := by
    intro q hq
    have r1 := cpl_endpoints_under Q a b q.1
      (Finset.mem_union_right _ ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩))
    have r2 := cpl_endpoints_under Q a b q.2
      (Finset.mem_union_right _ ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inr rfl⟩))
    exact ⟨fun _ => r2, fun _ => r1⟩
  refine ⟨fun z hz hr => (hL z (hE.mem_cplNodes hz hr)).ge,
    ⟨a, b, under_refl _, under_refl _, exists_cross_pair Q a b, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro z hz hza
    by_cases he : z = a
    · exact Or.inl (by rw [he]; exact under_refl _)
    · exact Or.inr (flat_of_anc hE.nodeA hz hza he
        ((hL z (hE.mem_cplNodes hz (Or.inl hza))).trans La.symm))
  · intro z hz hzb
    by_cases he : z = b
    · exact Or.inl (by rw [he]; exact under_refl _)
    · exact Or.inr (flat_of_anc hE.nodeB hz hzb he
        ((hL z (hE.mem_cplNodes hz (Or.inr hzb))).trans Lb.symm))
  · intro t ht hta
    exact ⟨a, hE.nodeA, under_refl _, by rw [La]; exact ht, hta, hpu⟩
  · intro t ht htb
    exact ⟨b, hE.nodeB, under_refl _, by rw [Lb]; exact ht, htb, hpu⟩
  · exact ⟨La.le.trans (min_le_left _ _), Lb.le.trans (min_le_right _ _)⟩

/-- Type-2 couples. -/
theorem patternFacts_type2 {Xp Xm : RegChain} {Qlp : RegCpl} {a b : Fin w × Path}
    (hE : Embeds LG.garden (.type2 Xp Xm Qlp) a b)
    (hQ : ∀ z ∈ cplNodes Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath),
      layerAt LG z = min (parAt LG p a) (parAt LG p b))
    (hXp : ChainPairLayers LG Xp 1 a) (hXm : ChainPairLayers LG Xm (-1) b)
    (hBp : ∀ z ∈ chainNodesSet Xp 1 a,
      min (parAt LG p a) (parAt LG p b) ≤ layerAt LG z ∧ layerAt LG z ≤ parAt LG p a)
    (hBm : ∀ z ∈ chainNodesSet Xm (-1) b,
      min (parAt LG p a) (parAt LG p b) ≤ layerAt LG z ∧ layerAt LG z ≤ parAt LG p b) :
    PatternFacts LG p (.type2 Xp Xm Qlp) a b := by
  have hab := hE.indep
  obtain ⟨Cp, Cm, El⟩ := hE.type2
  have LeA := hQ _ (left_mem_cplNodes Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath))
  have LeB := hQ _ (right_mem_cplNodes Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath))
  have notM : ∀ z, Under a z → z ∉ chainNodesSet Xm (-1) b := fun z hza h =>
    hab.not_both hza (chain_endpoints_region Xm (-1) b z h).1
  have notP : ∀ z, Under b z → z ∉ chainNodesSet Xp 1 a := fun z hzb h =>
    hab.not_both (chain_endpoints_region Xp 1 a z h).1 hzb
  refine ⟨?_, ⟨addrExt a Xp.lonePath, addrExt b Xm.lonePath, under_ext _ _, under_ext _ _, ?_, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · intro z hz hr
    rcases mem_cplNodes_type2.1 (hE.mem_cplNodes hz hr) with h | h | h
    · exact (hBp z h).1
    · exact (hBm z h).1
    · exact (hQ z h).ge
  · obtain ⟨q, hq, hc⟩ := exists_cross_pair Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)
    exact ⟨q, by simp only [RegCpl.pairsAt, List.mem_append]; exact Or.inr hq, hc⟩
  · intro z hz hza
    rcases mem_cplNodes_type2.1 (hE.mem_cplNodes hz (Or.inl hza)) with h | h | h
    · exact chain_flat Xp 1 a _ Cp hXp z h
    · exact absurd h (notM z hza)
    · rcases cpl_endpoints_under Qlp _ _ z h with h' | h'
      · by_cases he : z = addrExt a Xp.lonePath
        · exact Or.inl (by rw [he]; exact under_refl _)
        · exact Or.inr (flat_of_anc El.nodeA hz h' he ((hQ z h).trans LeA.symm))
      · exact absurd (under_trans (under_ext _ _) h') (fun h'' => hab.not_both hza h'')
  · intro z hz hzb
    rcases mem_cplNodes_type2.1 (hE.mem_cplNodes hz (Or.inr hzb)) with h | h | h
    · exact absurd h (notP z hzb)
    · exact chain_flat Xm (-1) b _ Cm hXm z h
    · rcases cpl_endpoints_under Qlp _ _ z h with h' | h'
      · exact absurd (under_trans (under_ext _ _) h') (fun h'' => hab.not_both h'' hzb)
      · by_cases he : z = addrExt b Xm.lonePath
        · exact Or.inl (by rw [he]; exact under_refl _)
        · exact Or.inr (flat_of_anc El.nodeB hz h' he ((hQ z h).trans LeB.symm))
  · intro t ht hta
    obtain ⟨s, hs, hls, hps⟩ := spine_cut_lt Xp 1 a _ Cp hXp t (by rw [LeA]; exact ht) hta
    exact ⟨s, spinePos_node Cp hs, (spinePos_under Xp a s hs).1, hls, hps,
      type2_pairedUnder Xp Xm Qlp hab hs (self_mem_spinePos Xm b)⟩
  · intro t ht htb
    obtain ⟨s, hs, hls, hps⟩ := spine_cut_lt Xm (-1) b _ Cm hXm t (by rw [LeB]; exact ht) htb
    exact ⟨s, spinePos_node Cm hs, (spinePos_under Xm b s hs).1, hls, hps,
      type2_pairedUnder Xp Xm Qlp hab (self_mem_spinePos Xp a) hs⟩
  · constructor
    · rcases mem_cplNodes_type2.1 (left_mem_cplNodes (.type2 Xp Xm Qlp) a b) with h | h | h
      · exact (hBp a h).2
      · exact absurd h (notM a (under_refl _))
      · exact (hQ a h).le.trans (min_le_left _ _)
    · rcases mem_cplNodes_type2.1 (right_mem_cplNodes (.type2 Xp Xm Qlp) a b) with h | h | h
      · exact absurd h (notP b (under_refl _))
      · exact (hBm b h).2
      · exact (hQ b h).le.trans (min_le_right _ _)

theorem patternFacts {Q : RegCpl} {a b : Fin w × Path} (hE : Embeds LG.garden Q a b)
    (hP : LayerPattern LG p Q a b) : PatternFacts LG p Q a b := by
  obtain ⟨-, hL⟩ := hP
  cases Q with
  | triv => exact patternFacts_flat hE hL
  | type1 c Q₁ Q₂ Q₃ => exact patternFacts_flat hE hL
  | type2 Xp Xm Qlp =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := hL
    exact patternFacts_type2 hE h1 h2 h3 h4 h5

/-! ### The characterization -/

/-- (⇒) at a root `c` of the couple: a cut `s` below `c` gives a criterion instance with `y`. -/
theorem attach_aux (hcan : LG.CanonCriterion p) (hplain : LG.garden.IsPlain) {c d s : Fin w × Path}
    (hcd : Indep c d)
    (hreg : ∀ ℓ : GLeaf LG.garden.tree, (Under c ℓ.1 ∨ Under d ℓ.1) →
      (Under c (LG.garden.pair ℓ).1 ∨ Under d (LG.garden.pair ℓ).1))
    (hcross : ∃ ℓ : GLeaf LG.garden.tree, Under c ℓ.1 ∧ Under d (LG.garden.pair ℓ).1)
    (hs : s.2 ∈ (LG.garden.tree s.1).nodes) (hcs : Under c s)
    (hpu : ∀ ℓ : GLeaf LG.garden.tree, (Under s ℓ.1 ∨ Under d ℓ.1) →
      (Under s (LG.garden.pair ℓ).1 ∨ Under d (LG.garden.pair ℓ).1))
    (x y : GNode LG.garden.tree) (hx : x.1 = c) (hyc : ¬ Under c y.1) (hyd : ¬ Under d y.1)
    (hinc : x.Incomparable y) (hcp : LG.garden.CompletelyPaired (x.leavesBelow ∪ y.leavesBelow)) :
    min (parAt LG p s) (parAt LG p y.1) ≤ max (layerAt LG s) (layerAt LG y.1) := by
  have hyx : ¬ Under y.1 c := fun h => hinc.2 (show Under y.1 x.1 by rw [hx]; exact h)
  have hyd' : Under y.1 d := by
    obtain ⟨ℓ, h1, h2⟩ := hcross
    rcases cp_to hcp ℓ (Or.inl (by rw [hx]; exact h1)) with h | h
    · exact absurd h2 (fun h' => hcd.not_both (by rw [← hx]; exact h) h')
    · exact under_of_out hyd h2 h
  have hsy : Indep s y.1 := by
    refine ⟨fun h => hyc (under_trans hcs h), fun h => ?_⟩
    rcases under_total h hcs with h' | h'
    · exact hyx h'
    · exact hyc h'
  have hcp' : LG.garden.CompletelyPaired
      (GNode.leavesBelow (⟨s, hs⟩ : GNode LG.garden.tree) ∪ y.leavesBelow) := by
    apply cp_of hplain
    intro ℓ hℓ
    by_cases hr : Under c ℓ.1 ∨ Under d ℓ.1
    · have hsd : Under s ℓ.1 ∨ Under d ℓ.1 := by
        rcases hℓ with h | h
        · exact Or.inl h
        · rcases hr with h' | h'
          · exact absurd (under_of_out hyc h' h) hyx
          · exact Or.inr h'
      rcases hpu ℓ hsd with h | h
      · exact Or.inl h
      · exact Or.inr (under_trans hyd' h)
    · have hy : Under y.1 ℓ.1 := hℓ.resolve_left (fun h => hr (Or.inl (under_trans hcs h)))
      have hout : ¬ (Under c (LG.garden.pair ℓ).1 ∨ Under d (LG.garden.pair ℓ).1) := by
        intro h; apply hr; have := hreg _ h; rwa [LG.garden.pair_pair] at this
      rcases cp_to hcp ℓ (Or.inr hy) with h | h
      · exact absurd (Or.inl (by rw [← hx]; exact h)) hout
      · exact Or.inr h
  have := hcan.2 ⟨s, hs⟩ y ⟨hsy.1, hsy.2⟩ hcp'
  rw [parAt_of_mem LG p hs, layerAt_of_mem LG hs, parAt_node, layerAt_node]
  exact this

/-- (⇐) at a root `c` of the couple: an instance `(x, y)` with `x` on the spine below `c` and `y` outside
reduces to the collapsed instance `(c, y)`. -/
theorem side_aux (hp : ∀ x, LG.layer x ≤ p) (hplain : LG.garden.IsPlain) {c d ec ed : Fin w × Path}
    {r : ℕ} (hcd : Indep c d) (hc : c.2 ∈ (LG.garden.tree c.1).nodes) (hed : Under d ed)
    (hreg : ∀ ℓ : GLeaf LG.garden.tree, (Under c ℓ.1 ∨ Under d ℓ.1) →
      (Under c (LG.garden.pair ℓ).1 ∨ Under d (LG.garden.pair ℓ).1))
    (hcross : ∃ ℓ : GLeaf LG.garden.tree, Under ec ℓ.1 ∧ Under ed (LG.garden.pair ℓ).1)
    (hatt : ∀ y : GNode LG.garden.tree, ¬ Under c y.1 → ¬ Under d y.1 →
      GNode.Incomparable (⟨c, hc⟩ : GNode LG.garden.tree) y →
      LG.garden.CompletelyPaired (GNode.leavesBelow (⟨c, hc⟩ : GNode LG.garden.tree) ∪ y.leavesBelow) →
      min (parAt LG p c) (parAt LG p y.1) ≤ max r (layerAt LG y.1))
    (x y : GNode LG.garden.tree) (hxc : Under c x.1) (hxe : Under x.1 ec) (hxr : r ≤ layerAt LG x.1)
    (hyc : ¬ Under c y.1) (hyd : ¬ Under d y.1) (hinc : x.Incomparable y)
    (hcp : LG.garden.CompletelyPaired (x.leavesBelow ∪ y.leavesBelow)) :
    min (parAt LG p x.1) (parAt LG p y.1) ≤ max (layerAt LG x.1) (layerAt LG y.1) := by
  have hyx : ¬ Under y.1 c := fun h => hinc.2 (under_trans h hxc)
  have hyd' : Under y.1 d := by
    obtain ⟨ℓ, h1, h2⟩ := hcross
    rcases cp_to hcp ℓ (Or.inl (under_trans hxe h1)) with h | h
    · exact absurd (under_trans hed h2) (fun h' => hcd.not_both (under_trans hxc h) h')
    · exact under_of_out hyd (under_trans hed h2) h
  have hcp' : LG.garden.CompletelyPaired
      (GNode.leavesBelow (⟨c, hc⟩ : GNode LG.garden.tree) ∪ y.leavesBelow) := by
    apply cp_of hplain
    intro ℓ hℓ
    by_cases hr : Under c ℓ.1 ∨ Under d ℓ.1
    · rcases hreg ℓ hr with h | h
      · exact Or.inl h
      · exact Or.inr (under_trans hyd' h)
    · have hy : Under y.1 ℓ.1 := hℓ.resolve_left (fun h => hr (Or.inl h))
      have hout : ¬ (Under c (LG.garden.pair ℓ).1 ∨ Under d (LG.garden.pair ℓ).1) := by
        intro h; apply hr; have := hreg _ h; rwa [LG.garden.pair_pair] at this
      rcases cp_to hcp ℓ (Or.inr hy) with h | h
      · exact absurd (Or.inl (under_trans hxc h)) hout
      · exact Or.inr h
  have h1 := hatt y hyc hyd ⟨hyc, hyx⟩ hcp'
  have h2 : parAt LG p x.1 ≤ parAt LG p c := parAt_le_parAt LG p hp hc x.2 hxc
  calc min (parAt LG p x.1) (parAt LG p y.1) ≤ min (parAt LG p c) (parAt LG p y.1) :=
        min_le_min h2 le_rfl
    _ ≤ max r (layerAt LG y.1) := h1
    _ ≤ max (layerAt LG x.1) (layerAt LG y.1) := max_le_max hxr le_rfl

/-- **TARGET Prop `layerreg1` (2), characterization.** For a plain layered garden containing an embedded
regular couple with the layering of part (1) (`LayerPattern`), the canonicity criterion is equivalent to
criterion (i), criterion (ii) away from the couple (`CritOut`), and criterion (ii) at the roots of the
couple with the couple collapsed to a leaf pair in layer `min(q, q')` (`CritAttach`). The right-hand side
does not look inside the couple. -/
theorem layerreg1_part2 (hplain : LG.garden.IsPlain) {Q : RegCpl} {a b : Fin w × Path}
    (hE : Embeds LG.garden Q a b) (hP : LayerPattern LG p Q a b) :
    LG.CanonCriterion p ↔ (∀ x, LG.layer x ≤ p) ∧ CritOut LG p a b ∧
      CritAttach LG p a b (min (parAt LG p a) (parAt LG p b)) := by
  have pf := patternFacts hE hP
  have hab := hE.indep
  have hreg : ∀ ℓ : GLeaf LG.garden.tree, (Under a ℓ.1 ∨ Under b ℓ.1) →
      (Under a (LG.garden.pair ℓ).1 ∨ Under b (LG.garden.pair ℓ).1) := hE.pair_region
  have hreg' : ∀ ℓ : GLeaf LG.garden.tree, (Under b ℓ.1 ∨ Under a ℓ.1) →
      (Under b (LG.garden.pair ℓ).1 ∨ Under a (LG.garden.pair ℓ).1) :=
    fun ℓ h => (hE.pair_region ℓ h.symm).symm
  obtain ⟨ℓ₀, h₁, h₂⟩ := hE.cross_leaf (exists_cross_pair Q a b)
  have hcrossBA : ∃ ℓ : GLeaf LG.garden.tree, Under b ℓ.1 ∧ Under a (LG.garden.pair ℓ).1 :=
    ⟨LG.garden.pair ℓ₀, h₂, by rw [LG.garden.pair_pair]; exact h₁⟩
  constructor
  · intro hcan
    refine ⟨hcan.1, fun x y _ _ hinc hcp => hcan.2 x y hinc hcp, ?_⟩
    intro x y hx hy hinc hcp
    rw [← parAt_node, ← parAt_node, ← layerAt_node]
    have hyo := not_or.1 hy
    by_contra hlt
    rw [not_le] at hlt
    have key : ∀ s : Fin w × Path,
        min (parAt LG p s) (parAt LG p y.1) ≤ max (layerAt LG s) (layerAt LG y.1) →
        layerAt LG s < min (parAt LG p x.1) (parAt LG p y.1) →
        min (parAt LG p x.1) (parAt LG p y.1) ≤ parAt LG p s → False := by
      intro s h hl hps
      have ht : min (parAt LG p x.1) (parAt LG p y.1) ≤ min (parAt LG p s) (parAt LG p y.1) :=
        le_min hps (min_le_right _ _)
      exact absurd h (not_le.2 (max_lt (hl.trans_le ht)
        ((lt_of_le_of_lt (le_max_right _ _) hlt).trans_le ht)))
    have hrt : min (parAt LG p a) (parAt LG p b) < min (parAt LG p x.1) (parAt LG p y.1) :=
      lt_of_le_of_lt (le_max_left _ _) hlt
    rcases hx with hxa | hxb
    · obtain ⟨s, hs, has, hls, hps, hpu⟩ :=
        pf.cutA _ hrt (by rw [← hxa]; exact min_le_left _ _)
      refine key s (attach_aux hcan hplain hab hreg ⟨ℓ₀, h₁, h₂⟩ hs has ?_ x y hxa hyo.1 hyo.2 hinc
        hcp) hls hps
      intro ℓ h
      exact hE.pu_leaf hpu ℓ (h.elim (fun h' => Or.inl (under_trans has h')) Or.inr) h
    · obtain ⟨s, hs, hbs, hls, hps, hpu⟩ :=
        pf.cutB _ hrt (by rw [← hxb]; exact min_le_left _ _)
      refine key s (attach_aux hcan hplain hab.symm hreg' hcrossBA hs hbs ?_ x y hxb hyo.2 hyo.1 hinc
        hcp) hls hps
      intro ℓ h
      exact (hE.pu_leaf hpu ℓ (h.elim (fun h' => Or.inr (under_trans hbs h')) Or.inl) h.symm).symm
  · rintro ⟨hp, hout, hatt⟩
    refine ⟨hp, fun x y hinc hcp => ?_⟩
    rw [← parAt_node, ← parAt_node, ← layerAt_node, ← layerAt_node]
    obtain ⟨eA, eB, haA, hbB, hcrossE, hflA, hflB⟩ := pf.spine
    have hattA : ∀ y : GNode LG.garden.tree, ¬ Under a y.1 → ¬ Under b y.1 →
        GNode.Incomparable (⟨a, hE.nodeA⟩ : GNode LG.garden.tree) y →
        LG.garden.CompletelyPaired (GNode.leavesBelow (⟨a, hE.nodeA⟩ : GNode LG.garden.tree) ∪
          y.leavesBelow) →
        min (parAt LG p a) (parAt LG p y.1) ≤ max (min (parAt LG p a) (parAt LG p b))
          (layerAt LG y.1) := by
      intro y h1 h2 hi hc
      have := hatt ⟨a, hE.nodeA⟩ y (Or.inl rfl) (not_or.2 ⟨h1, h2⟩) hi hc
      rwa [← parAt_of_mem LG p hE.nodeA, ← parAt_node, ← layerAt_node] at this
    have hattB : ∀ y : GNode LG.garden.tree, ¬ Under b y.1 → ¬ Under a y.1 →
        GNode.Incomparable (⟨b, hE.nodeB⟩ : GNode LG.garden.tree) y →
        LG.garden.CompletelyPaired (GNode.leavesBelow (⟨b, hE.nodeB⟩ : GNode LG.garden.tree) ∪
          y.leavesBelow) →
        min (parAt LG p b) (parAt LG p y.1) ≤ max (min (parAt LG p a) (parAt LG p b))
          (layerAt LG y.1) := by
      intro y h1 h2 hi hc
      have := hatt ⟨b, hE.nodeB⟩ y (Or.inr rfl) (not_or.2 ⟨h2, h1⟩) hi hc
      rwa [← parAt_of_mem LG p hE.nodeB, ← parAt_node, ← layerAt_node] at this
    have crossA := hE.cross_leaf hcrossE
    have crossB := hE.cross_leaf (by
      obtain ⟨q, hq, hc⟩ := hcrossE
      exact ⟨q, hq, hc.symm⟩ : ∃ q ∈ Q.pairsAt a b, Crosses q eB eA)
    -- one node in the region, the other outside
    have side : ∀ x y : GNode LG.garden.tree, InRegion a b x.1 → ¬ InRegion a b y.1 →
        x.Incomparable y → LG.garden.CompletelyPaired (x.leavesBelow ∪ y.leavesBelow) →
        min (parAt LG p x.1) (parAt LG p y.1) ≤ max (layerAt LG x.1) (layerAt LG y.1) := by
      intro x y hxr hyr hinc hcp
      have hyo := not_or.1 hyr
      rcases hxr with hxa | hxb
      · rcases hflA x.1 x.2 hxa with he | hfl
        · exact side_aux hp hplain hab hE.nodeA hbB hreg crossA hattA x y hxa he
            (pf.lower _ x.2 (Or.inl hxa)) hyo.1 hyo.2 hinc hcp
        · rw [hfl]; exact (min_le_left _ _).trans (le_max_left _ _)
      · rcases hflB x.1 x.2 hxb with he | hfl
        · exact side_aux hp hplain hab.symm hE.nodeB haA hreg' crossB hattB x y hxb he
            (pf.lower _ x.2 (Or.inr hxb)) hyo.2 hyo.1 hinc hcp
        · rw [hfl]; exact (min_le_left _ _).trans (le_max_left _ _)
    -- both in the region, on opposite sides
    have opp : ∀ x y : GNode LG.garden.tree, Under a x.1 → Under b y.1 →
        min (parAt LG p x.1) (parAt LG p y.1) ≤ max (layerAt LG x.1) (layerAt LG y.1) := by
      intro x y hxa hyb
      calc min (parAt LG p x.1) (parAt LG p y.1) ≤ min (parAt LG p a) (parAt LG p b) :=
            min_le_min (parAt_le_parAt LG p hp hE.nodeA x.2 hxa)
              (parAt_le_parAt LG p hp hE.nodeB y.2 hyb)
        _ ≤ layerAt LG x.1 := pf.lower _ x.2 (Or.inl hxa)
        _ ≤ max (layerAt LG x.1) (layerAt LG y.1) := le_max_left _ _
    by_cases hxr : InRegion a b x.1 <;> by_cases hyr : InRegion a b y.1
    · have hfl : ∀ z : GNode LG.garden.tree, InRegion a b z.1 →
          (Under a z.1 ∧ Under z.1 eA) ∨ (Under b z.1 ∧ Under z.1 eB) ∨
            parAt LG p z.1 = layerAt LG z.1 := by
        intro z hz
        rcases hz with hza | hzb
        · rcases hflA z.1 z.2 hza with h | h
          · exact Or.inl ⟨hza, h⟩
          · exact Or.inr (Or.inr h)
        · rcases hflB z.1 z.2 hzb with h | h
          · exact Or.inr (Or.inl ⟨hzb, h⟩)
          · exact Or.inr (Or.inr h)
      rcases hfl y hyr with ⟨hya, hye⟩ | ⟨hyb, hye⟩ | hfy
      · rcases hfl x hxr with ⟨hxa, hxe⟩ | ⟨hxb, hxe⟩ | hfx
        · exfalso
          rcases under_total hxe hye with h | h
          · exact hinc.1 h
          · exact hinc.2 h
        · rw [min_comm, max_comm]; exact opp y x hya hxb
        · rw [hfx]; exact (min_le_left _ _).trans (le_max_left _ _)
      · rcases hfl x hxr with ⟨hxa, hxe⟩ | ⟨hxb, hxe⟩ | hfx
        · exact opp x y hxa hyb
        · exfalso
          rcases under_total hxe hye with h | h
          · exact hinc.1 h
          · exact hinc.2 h
        · rw [hfx]; exact (min_le_left _ _).trans (le_max_left _ _)
      · rw [hfy]; exact (min_le_right _ _).trans (le_max_right _ _)
    · exact side x y hxr hyr hinc hcp
    · rw [min_comm, max_comm]
      exact side y x hyr hxr ⟨hinc.2, hinc.1⟩ (by rwa [Finset.union_comm])
    · have := hout x y hxr hyr hinc hcp
      rwa [← parAt_node, ← parAt_node, ← layerAt_node, ← layerAt_node] at this

end WaveTurbulence.Links
