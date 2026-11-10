/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueForest
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueGarden
/-! # A2 CAPS-ID: the capped encoding of a flower garden (supplement Lemma 2.1)

For a garden `G` of width `w`, `capGarden G` has width `2 * w`: tree `j` (index `capσ w (inl j)`, value `j`) is
`G.tree j`, and tree `capσ w (inr j)` (value `w + j`) is a trivial tree, the **cap** of tree `j`. The flower of
tree `j` is re-paired with its cap. The cap's sign is opposite to the flower's sign, and the cap's layer is the
flower's layer. All other pairs, marks, signs and layers are unchanged.

The construction is total. When tree `j` has no flower, its cap is left marked (a flower of the capped garden).
"The flower of tree `j`" is `flowerOf G j`, a chosen flower, so other flowers of tree `j` stay marked. On
flower gardens (`Garden.IsFlowerGarden`, exactly one marked leaf per tree, a flower) the capped garden is plain
(`capGarden_isPlain`).

Forest bookkeeping uses FLOWER-P7's glue equivalences `glueNode`/`glueLeaf`/`glueBranch` along `capσ w`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsId
open TTree Finset WaveTurbulence.FlowerP7

variable {w : ℕ}

/-! ## The index equivalence and the cap forest -/

/-- The index equivalence of the capped garden: original tree `j ↦ j`, cap of tree `j ↦ w + j`. -/
def capσ (w : ℕ) : Fin w ⊕ Fin w ≃ Fin (2 * w) :=
  finSumFinEquiv.trans (finCongr (two_mul w).symm)

@[simp] theorem capσ_inl_val (j : Fin w) : (capσ w (.inl j) : ℕ) = j := rfl

@[simp] theorem capσ_inr_val (j : Fin w) : (capσ w (.inr j) : ℕ) = w + j := rfl

/-- The cap trees: indices `≥ w`. -/
def capJ (w : ℕ) : Finset (Fin (2 * w)) := Finset.univ.filter fun c => w ≤ (c : ℕ)

theorem capσ_inl_notMem_capJ (j : Fin w) : capσ w (.inl j) ∉ capJ w := by
  simp [capJ, j.2]

theorem capσ_inr_mem_capJ (j : Fin w) : capσ w (.inr j) ∈ capJ w := by
  simp [capJ]

/-- The cap forest: `w` trivial trees. -/
abbrev capForest (w : ℕ) : Fin w → TTree := fun _ => TTree.leaf

/-- The capped forest. -/
abbrev capTree (T : Fin w → TTree) : Fin (2 * w) → TTree := gT (capσ w) T (capForest w)

/-- The unique leaf of the cap of tree `j`. -/
def capLeafF (j : Fin w) : GLeaf (capForest w) := ⟨(j, []), by simp [TTree.leaves]⟩

/-- The unique node of the cap of tree `j`. -/
def capNodeF (j : Fin w) : GNode (capForest w) := ⟨(j, []), by simp [TTree.nodes]⟩

theorem capLeafF_eq (c : GLeaf (capForest w)) : c = capLeafF c.1.1 := by
  obtain ⟨⟨j, q⟩, hq⟩ := c
  have hq' : q = [] := by simpa [TTree.leaves] using hq
  subst hq'
  rfl

theorem capNodeF_eq (c : GNode (capForest w)) : c = capNodeF c.1.1 := by
  obtain ⟨⟨j, q⟩, hq⟩ := c
  have hq' : q = [] := by simpa [TTree.nodes] using hq
  subst hq'
  rfl

instance capForest_branch_isEmpty : IsEmpty (GBranch (capForest w)) :=
  ⟨fun b => by simpa [TTree.branching] using b.2⟩

/-! ## The chosen flower of a tree -/

/-- The chosen flower of tree `j` (`none` if tree `j` has no flower). -/
def flowerOf (G : Garden w) (j : Fin w) : Option (GLeaf G.tree) :=
  if h : ∃ ℓ : GLeaf G.tree, ℓ.1.1 = j ∧ G.IsFlower ℓ then some h.choose else none

theorem flowerOf_spec {G : Garden w} {j : Fin w} {ℓ : GLeaf G.tree} (h : flowerOf G j = some ℓ) :
    ℓ.1.1 = j ∧ G.IsFlower ℓ := by
  unfold flowerOf at h
  split_ifs at h with hex
  cases h
  exact hex.choose_spec

/-- Exactly one flower in every tree. -/
def OneFlower (G : Garden w) : Prop := ∀ j, ∃! ℓ : GLeaf G.tree, ℓ.1.1 = j ∧ G.IsFlower ℓ

theorem oneFlower_of_isFlowerGarden {G : Garden w} (h : G.IsFlowerGarden) : OneFlower G := by
  intro j
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (h.1 j)
  have haj : a.1.1 = j ∧ G.mark a ≠ none := by
    have : a ∈ Finset.univ.filter fun ℓ : GLeaf G.tree => ℓ.1.1 = j ∧ G.mark ℓ ≠ none := by
      rw [ha]; exact Finset.mem_singleton_self a
    simpa using this
  refine ⟨a, ⟨haj.1, h.2.1 a haj.2⟩, fun ℓ hℓ => ?_⟩
  have hmem : ℓ ∈ Finset.univ.filter fun ℓ : GLeaf G.tree => ℓ.1.1 = j ∧ G.mark ℓ ≠ none := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hℓ.1, ?_⟩
    have hf := hℓ.2
    unfold Garden.IsFlower at hf
    rw [hf]; exact Option.some_ne_none _
  rw [ha] at hmem
  exact Finset.mem_singleton.1 hmem

theorem flowerOf_self_iff {G : Garden w} (hF : OneFlower G) (ℓ : GLeaf G.tree) :
    flowerOf G ℓ.1.1 = some ℓ ↔ G.IsFlower ℓ := by
  constructor
  · intro h; exact (flowerOf_spec h).2
  · intro hfl
    have hex : ∃ ℓ' : GLeaf G.tree, ℓ'.1.1 = ℓ.1.1 ∧ G.IsFlower ℓ' := ⟨ℓ, rfl, hfl⟩
    unfold flowerOf
    rw [dite_eq_left hex]
    congr 1
    exact (hF ℓ.1.1).unique hex.choose_spec ⟨rfl, hfl⟩

theorem flowerOf_isSome {G : Garden w} (hF : OneFlower G) (j : Fin w) :
    ∃ ℓ, flowerOf G j = some ℓ := by
  obtain ⟨ℓ, hℓ, -⟩ := hF j
  refine ⟨ℓ, ?_⟩
  have := (flowerOf_self_iff hF ℓ).2 hℓ.2
  rwa [hℓ.1] at this

/-! ## The capped garden -/

/-- Signs of the caps: opposite to the chosen flower. -/
def capSigCaps (G : Garden w) : Fin w → ℤˣ :=
  fun j => (flowerOf G j).elim 1 fun ℓ => -G.sign ℓ.toNode

/-- The capped signature. -/
def capSig (G : Garden w) : Fin (2 * w) → ℤˣ := gSig (capσ w) G.sig (capSigCaps G)

/-- The capped pairing on `original leaves ⊕ cap leaves`. -/
def capPairS (G : Garden w) : GLeaf G.tree ⊕ GLeaf (capForest w) → GLeaf G.tree ⊕ GLeaf (capForest w)
  | .inl ℓ => if flowerOf G ℓ.1.1 = some ℓ then .inr (capLeafF ℓ.1.1) else .inl (G.pair ℓ)
  | .inr c => (flowerOf G c.1.1).elim (.inr c) .inl

/-- The capped marks on `original leaves ⊕ cap leaves`. -/
def capMarkS (G : Garden w) : GLeaf G.tree ⊕ GLeaf (capForest w) → Option MarkTag
  | .inl ℓ => if flowerOf G ℓ.1.1 = some ℓ then none else G.mark ℓ
  | .inr c => if flowerOf G c.1.1 = none then some .equal else none

/-- Signs on `original leaves ⊕ cap leaves`. -/
def capSgnS (G : Garden w) : GLeaf G.tree ⊕ GLeaf (capForest w) → ℤˣ
  | .inl ℓ => G.sign ℓ.toNode
  | .inr c => capSigCaps G c.1.1

theorem not_flowerOf_pair {G : Garden w} (ℓ : GLeaf G.tree) (h : G.pair ℓ ≠ ℓ) :
    flowerOf G (G.pair ℓ).1.1 ≠ some (G.pair ℓ) := by
  intro hc
  have hfl := (flowerOf_spec hc).2
  have hm : G.mark (G.pair ℓ) ≠ none := by
    unfold Garden.IsFlower at hfl; rw [hfl]; exact Option.some_ne_none _
  have := (G.pair_eq_iff (G.pair ℓ)).2 hm
  rw [G.pair_pair] at this
  exact h this.symm

theorem capPairS_capPairS (G : Garden w) (y : GLeaf G.tree ⊕ GLeaf (capForest w)) :
    capPairS G (capPairS G y) = y := by
  rcases y with ℓ | c
  · by_cases hc : flowerOf G ℓ.1.1 = some ℓ
    · simp only [capPairS, ite_eq_left hc]
      show (flowerOf G ℓ.1.1).elim _ _ = _
      rw [hc]; rfl
    · simp only [capPairS, ite_eq_right hc]
      by_cases hp : G.pair ℓ = ℓ
      · rw [hp, ite_eq_right hc, hp]
      · rw [ite_eq_right (not_flowerOf_pair ℓ hp), G.pair_pair]
  · rcases hf : flowerOf G c.1.1 with _ | ℓ
    · simp only [capPairS, hf, Option.elim_none]
    · simp only [capPairS, hf, Option.elim_some]
      have hj := (flowerOf_spec hf).1
      have hc : flowerOf G ℓ.1.1 = some ℓ := by rw [hj]; exact hf
      rw [ite_eq_left hc, hj]
      exact congrArg Sum.inr (capLeafF_eq c).symm

theorem capPairS_eq_self_iff (G : Garden w) (y : GLeaf G.tree ⊕ GLeaf (capForest w)) :
    capPairS G y = y ↔ capMarkS G y ≠ none := by
  rcases y with ℓ | c
  · by_cases hc : flowerOf G ℓ.1.1 = some ℓ
    · simp [capPairS, capMarkS, hc]
    · simp only [capPairS, capMarkS, ite_eq_right hc, Sum.inl.injEq]
      exact G.pair_eq_iff ℓ
  · rcases hf : flowerOf G c.1.1 with _ | ℓ
    · simp [capPairS, capMarkS, hf]
    · simp [capPairS, capMarkS, hf]

theorem capPairS_sign (G : Garden w) (y : GLeaf G.tree ⊕ GLeaf (capForest w)) (h : capPairS G y ≠ y) :
    capSgnS G (capPairS G y) = -capSgnS G y := by
  rcases y with ℓ | c
  · by_cases hc : flowerOf G ℓ.1.1 = some ℓ
    · simp only [capPairS, ite_eq_left hc, capSgnS, capSigCaps]
      show (flowerOf G (capLeafF ℓ.1.1).1.1).elim 1 _ = _
      change (flowerOf G ℓ.1.1).elim 1 _ = _
      rw [hc]; rfl
    · simp only [capPairS, ite_eq_right hc, capSgnS] at h ⊢
      have hp : G.pair ℓ ≠ ℓ := fun e => h (by rw [e])
      exact G.pair_sign ℓ hp
  · rcases hf : flowerOf G c.1.1 with _ | ℓ
    · simp only [capPairS, hf, Option.elim_none] at h
      exact absurd rfl h
    · simp only [capPairS, hf, Option.elim_some, capSgnS, capSigCaps]
      rw [neg_neg]

/-- Node signs of the capped forest at the glued addresses. -/
theorem nodeSign_capSig_leaf (G : Garden w) (y : GLeaf G.tree ⊕ GLeaf (capForest w)) :
    nodeSign (capSig G) (glueLeaf (capσ w) G.tree (capForest w) y).1 = capSgnS G y := by
  rcases y with ℓ | c
  · show nodeSign (gSig (capσ w) G.sig (capSigCaps G)) (capσ w (.inl ℓ.1.1), ℓ.1.2) = _
    rw [nodeSign_glue_inl]; rfl
  · show nodeSign (gSig (capσ w) G.sig (capSigCaps G)) (capσ w (.inr c.1.1), c.1.2) = _
    rw [nodeSign_glue_inr]
    have hc : c.1.2 = [] := by rw [capLeafF_eq c]; rfl
    simp [nodeSign, TTree.pathSign, hc, capSgnS]

/-- **The capped garden** (supplement Lemma 2.1): width `2 * w`, caps re-paired with the chosen flowers. -/
def capGarden (G : Garden w) : Garden (2 * w) where
  sig := capSig G
  tree := capTree G.tree
  pair := fun ℓ => glueLeaf (capσ w) G.tree (capForest w)
    (capPairS G ((glueLeaf (capσ w) G.tree (capForest w)).symm ℓ))
  mark := fun ℓ => capMarkS G ((glueLeaf (capσ w) G.tree (capForest w)).symm ℓ)
  pair_pair := fun ℓ => by
    simp only [Equiv.symm_apply_apply, capPairS_capPairS, Equiv.apply_symm_apply]
  pair_eq_iff := fun ℓ => by
    rw [← capPairS_eq_self_iff]
    constructor
    · intro h
      have := congrArg (glueLeaf (capσ w) G.tree (capForest w)).symm h
      simpa only [Equiv.symm_apply_apply] using this
    · intro h
      rw [h, Equiv.apply_symm_apply]
  pair_sign := fun ℓ hℓ => by
    have hne : capPairS G ((glueLeaf (capσ w) G.tree (capForest w)).symm ℓ) ≠
        (glueLeaf (capσ w) G.tree (capForest w)).symm ℓ := by
      intro e
      apply hℓ
      rw [e, Equiv.apply_symm_apply]
    have h1 := nodeSign_capSig_leaf G (capPairS G ((glueLeaf (capσ w) G.tree (capForest w)).symm ℓ))
    have h2 := nodeSign_capSig_leaf G ((glueLeaf (capσ w) G.tree (capForest w)).symm ℓ)
    rw [Equiv.apply_symm_apply] at h2
    rw [h1, h2]
    exact capPairS_sign G _ hne

/-! ## Embeddings of nodes, leaves and branching nodes -/

/-- Nodes of the capped garden: original nodes and cap nodes. -/
def cNode (G : Garden w) : GNode G.tree ⊕ GNode (capForest w) ≃ GNode (capGarden G).tree :=
  glueNode (capσ w) G.tree (capForest w)

/-- Leaves of the capped garden: original leaves and cap leaves. -/
def cLeaf (G : Garden w) : GLeaf G.tree ⊕ GLeaf (capForest w) ≃ GLeaf (capGarden G).tree :=
  glueLeaf (capσ w) G.tree (capForest w)

/-- Branching nodes of the capped garden: exactly the original ones. -/
def cBranch (G : Garden w) : GBranch G.tree ≃ GBranch (capGarden G).tree :=
  (Equiv.sumEmpty (GBranch G.tree) (GBranch (capForest w))).symm.trans
    (glueBranch (capσ w) G.tree (capForest w))

/-- An original node in the capped garden. -/
abbrev embN (G : Garden w) (a : GNode G.tree) : GNode (capGarden G).tree := cNode G (.inl a)

/-- The node (root and leaf) of the cap of tree `j`. -/
abbrev capN (G : Garden w) (j : Fin w) : GNode (capGarden G).tree := cNode G (.inr (capNodeF j))

/-- An original leaf in the capped garden. -/
abbrev embL (G : Garden w) (ℓ : GLeaf G.tree) : GLeaf (capGarden G).tree := cLeaf G (.inl ℓ)

/-- The leaf of the cap of tree `j`. -/
abbrev capL (G : Garden w) (j : Fin w) : GLeaf (capGarden G).tree := cLeaf G (.inr (capLeafF j))

@[simp] theorem embN_val (G : Garden w) (a : GNode G.tree) : (embN G a).1 = (capσ w (.inl a.1.1), a.1.2) := rfl

@[simp] theorem capN_val (G : Garden w) (j : Fin w) : (capN G j).1 = (capσ w (.inr j), []) := rfl

@[simp] theorem embL_val (G : Garden w) (ℓ : GLeaf G.tree) : (embL G ℓ).1 = (capσ w (.inl ℓ.1.1), ℓ.1.2) := rfl

@[simp] theorem capL_val (G : Garden w) (j : Fin w) : (capL G j).1 = (capσ w (.inr j), []) := rfl

@[simp] theorem cBranch_val (G : Garden w) (b : GBranch G.tree) :
    (cBranch G b).1 = (capσ w (.inl b.1.1), b.1.2) := rfl

@[simp] theorem cBranch_toNode (G : Garden w) (b : GBranch G.tree) : (cBranch G b).toNode = embN G b.toNode :=
  rfl

@[simp] theorem cBranch_child (G : Garden w) (b : GBranch G.tree) (i : Fin 3) :
    (cBranch G b).child i = embN G (b.child i) := Subtype.ext rfl

@[simp] theorem embL_toNode (G : Garden w) (ℓ : GLeaf G.tree) : (embL G ℓ).toNode = embN G ℓ.toNode := rfl

@[simp] theorem capL_toNode (G : Garden w) (j : Fin w) : (capL G j).toNode = capN G j := rfl

theorem embN_root (G : Garden w) (j : Fin w) :
    embN G (GNode.root G.tree j) = GNode.root (capGarden G).tree (capσ w (.inl j)) := rfl

theorem capN_eq_root (G : Garden w) (j : Fin w) :
    capN G j = GNode.root (capGarden G).tree (capσ w (.inr j)) := rfl

theorem embN_injective (G : Garden w) : Function.Injective (embN G) := fun _ _ h =>
  Sum.inl_injective ((cNode G).injective h)

theorem embL_injective (G : Garden w) : Function.Injective (embL G) := fun _ _ h =>
  Sum.inl_injective ((cLeaf G).injective h)

theorem embL_ne_capL (G : Garden w) (ℓ : GLeaf G.tree) (j : Fin w) : embL G ℓ ≠ capL G j := fun h =>
  Sum.inl_ne_inr ((cLeaf G).injective h)

/-- Every capped node is an original node or a cap node. -/
theorem node_cases (G : Garden w) (x : GNode (capGarden G).tree) :
    (∃ a, x = embN G a) ∨ ∃ j, x = capN G j := by
  obtain ⟨y, rfl⟩ := (cNode G).surjective x
  rcases y with a | c
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr ⟨c.1.1, congrArg (fun z => cNode G (.inr z)) (capNodeF_eq c)⟩

/-- Every capped leaf is an original leaf or a cap leaf. -/
theorem leaf_cases (G : Garden w) (x : GLeaf (capGarden G).tree) :
    (∃ ℓ, x = embL G ℓ) ∨ ∃ j, x = capL G j := by
  obtain ⟨y, rfl⟩ := (cLeaf G).surjective x
  rcases y with ℓ | c
  · exact Or.inl ⟨ℓ, rfl⟩
  · exact Or.inr ⟨c.1.1, congrArg (fun z => cLeaf G (.inr z)) (capLeafF_eq c)⟩

/-! ## Structure of the capped garden -/

@[simp] theorem capGarden_tree_inl (G : Garden w) (j : Fin w) :
    (capGarden G).tree (capσ w (.inl j)) = G.tree j := gT_inl ..

@[simp] theorem capGarden_tree_inr (G : Garden w) (j : Fin w) :
    (capGarden G).tree (capσ w (.inr j)) = TTree.leaf := gT_inr ..

/-- The cap trees are trivial. -/
theorem capGarden_tree_of_mem_capJ (G : Garden w) {c : Fin (2 * w)} (hc : c ∈ capJ w) :
    (capGarden G).tree c = TTree.leaf := by
  obtain ⟨s, rfl⟩ := (capσ w).surjective c
  rcases s with j | j
  · exact absurd hc (capσ_inl_notMem_capJ j)
  · exact capGarden_tree_inr G j

theorem capGarden_sig_inl (G : Garden w) (j : Fin w) : (capGarden G).sig (capσ w (.inl j)) = G.sig j := by
  show gSig (capσ w) G.sig (capSigCaps G) _ = _
  simp [gSig]

theorem capGarden_sig_inr (G : Garden w) (j : Fin w) :
    (capGarden G).sig (capσ w (.inr j)) = capSigCaps G j := by
  show gSig (capσ w) G.sig (capSigCaps G) _ = _
  simp [gSig]

@[simp] theorem capGarden_sign_embN (G : Garden w) (a : GNode G.tree) :
    (capGarden G).sign (embN G a) = G.sign a := by
  show nodeSign (gSig (capσ w) G.sig (capSigCaps G)) (capσ w (.inl a.1.1), a.1.2) = nodeSign G.sig a.1
  rw [nodeSign_glue_inl (capσ w) G.sig (capSigCaps G) a.1]

theorem capGarden_pair_embL (G : Garden w) (ℓ : GLeaf G.tree) :
    (capGarden G).pair (embL G ℓ) =
      if flowerOf G ℓ.1.1 = some ℓ then capL G ℓ.1.1 else embL G (G.pair ℓ) := by
  show glueLeaf (capσ w) G.tree (capForest w)
    (capPairS G ((glueLeaf (capσ w) G.tree (capForest w)).symm (glueLeaf (capσ w) G.tree (capForest w) (.inl ℓ)))) = _
  rw [Equiv.symm_apply_apply]
  by_cases hc : flowerOf G ℓ.1.1 = some ℓ
  · simp only [capPairS, ite_eq_left hc]; rfl
  · simp only [capPairS, ite_eq_right hc]; rfl

theorem capGarden_pair_capL (G : Garden w) (j : Fin w) :
    (capGarden G).pair (capL G j) = (flowerOf G j).elim (capL G j) (embL G) := by
  show glueLeaf (capσ w) G.tree (capForest w)
    (capPairS G ((glueLeaf (capσ w) G.tree (capForest w)).symm
      (glueLeaf (capσ w) G.tree (capForest w) (.inr (capLeafF j))))) = _
  rw [Equiv.symm_apply_apply]
  show glueLeaf (capσ w) G.tree (capForest w) ((flowerOf G j).elim _ _) = _
  rcases flowerOf G j with _ | ℓ <;> rfl

theorem capGarden_mark_embL (G : Garden w) (ℓ : GLeaf G.tree) :
    (capGarden G).mark (embL G ℓ) = if flowerOf G ℓ.1.1 = some ℓ then none else G.mark ℓ := by
  show capMarkS G ((glueLeaf (capσ w) G.tree (capForest w)).symm (glueLeaf (capσ w) G.tree (capForest w) (.inl ℓ))) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem capGarden_mark_capL (G : Garden w) (j : Fin w) :
    (capGarden G).mark (capL G j) = if flowerOf G j = none then some .equal else none := by
  show capMarkS G ((glueLeaf (capσ w) G.tree (capForest w)).symm
    (glueLeaf (capσ w) G.tree (capForest w) (.inr (capLeafF j)))) = _
  rw [Equiv.symm_apply_apply]; rfl

/-- Under `OneFlower`, the flower of tree `j` is paired with the cap of tree `j`. -/
theorem capGarden_pair_flower (G : Garden w) (hF : OneFlower G) {ℓ : GLeaf G.tree} (hℓ : G.IsFlower ℓ) :
    (capGarden G).pair (embL G ℓ) = capL G ℓ.1.1 := by
  rw [capGarden_pair_embL, ite_eq_left ((flowerOf_self_iff hF ℓ).2 hℓ)]

/-- Under `OneFlower`, a non-flower keeps its pair. -/
theorem capGarden_pair_nonflower (G : Garden w) (hF : OneFlower G) {ℓ : GLeaf G.tree} (hℓ : ¬ G.IsFlower ℓ) :
    (capGarden G).pair (embL G ℓ) = embL G (G.pair ℓ) := by
  rw [capGarden_pair_embL, ite_eq_right (fun h => hℓ ((flowerOf_self_iff hF ℓ).1 h))]

theorem capGarden_mark_flower (G : Garden w) (hF : OneFlower G) {ℓ : GLeaf G.tree} (hℓ : G.IsFlower ℓ) :
    (capGarden G).mark (embL G ℓ) = none := by
  rw [capGarden_mark_embL, ite_eq_left ((flowerOf_self_iff hF ℓ).2 hℓ)]

theorem capGarden_mark_nonflower (G : Garden w) (hF : OneFlower G) {ℓ : GLeaf G.tree} (hℓ : ¬ G.IsFlower ℓ) :
    (capGarden G).mark (embL G ℓ) = G.mark ℓ := by
  rw [capGarden_mark_embL, ite_eq_right (fun h => hℓ ((flowerOf_self_iff hF ℓ).1 h))]

theorem capGarden_mark_capL_of (G : Garden w) (hF : OneFlower G) (j : Fin w) :
    (capGarden G).mark (capL G j) = none := by
  obtain ⟨ℓ, hℓ⟩ := flowerOf_isSome hF j
  rw [capGarden_mark_capL, hℓ, ite_eq_right (Option.some_ne_none _)]

theorem capGarden_pair_capL_of (G : Garden w) {j : Fin w} {ℓ : GLeaf G.tree}
    (hℓ : flowerOf G j = some ℓ) : (capGarden G).pair (capL G j) = embL G ℓ := by
  rw [capGarden_pair_capL, hℓ]; rfl

/-- Under `OneFlower`, the capped garden has no flowers. -/
theorem capGarden_not_isFlower (G : Garden w) (hF : OneFlower G) (x : GLeaf (capGarden G).tree) :
    ¬ (capGarden G).IsFlower x := by
  unfold Garden.IsFlower
  rcases leaf_cases G x with ⟨ℓ, rfl⟩ | ⟨j, rfl⟩
  · by_cases hℓ : G.IsFlower ℓ
    · rw [capGarden_mark_flower G hF hℓ]; exact (Option.some_ne_none _).symm
    · rw [capGarden_mark_nonflower G hF hℓ]; exact hℓ
  · rw [capGarden_mark_capL_of G hF]; exact (Option.some_ne_none _).symm

/-- **Lemma 2.1(1)**: the order is unchanged. -/
theorem capGarden_order (G : Garden w) : (capGarden G).order = G.order := by
  unfold Garden.order
  rw [← (capσ w).sum_comp, Fintype.sum_sum_type]
  simp [TTree.order]

/-- **Lemma 2.1(1)**: the signs of the caps are opposite to their flowers. -/
theorem capSigCaps_of_flower (G : Garden w) (hF : OneFlower G) {ℓ : GLeaf G.tree} (hℓ : G.IsFlower ℓ) :
    capSigCaps G ℓ.1.1 = -G.sign ℓ.toNode := by
  unfold capSigCaps
  rw [(flowerOf_self_iff hF ℓ).2 hℓ]; rfl

/-- On the carrier (flower signs `ζ · ζ_j`) the cap of tree `j` has sign `-(ζ · ζ_j)`. -/
theorem capSigCaps_eq (G : Garden w) (hF : OneFlower G) (ζ : ℤˣ)
    (hζ : ∀ ℓ : GLeaf G.tree, G.IsFlower ℓ → G.sign ℓ.toNode = ζ * G.sig ℓ.1.1) (j : Fin w) :
    capSigCaps G j = -(ζ * G.sig j) := by
  obtain ⟨ℓ, hℓ⟩ := flowerOf_isSome hF j
  obtain ⟨hj, hfl⟩ := flowerOf_spec hℓ
  unfold capSigCaps
  rw [hℓ]
  show -G.sign ℓ.toNode = _
  rw [hζ ℓ hfl, hj]

/-! ## The capped layered garden -/

/-- Layers on `original nodes ⊕ cap nodes`: a cap carries the layer of its flower (`p` if there is none). -/
def capLayerS (LG : LayeredGarden w) (p : ℕ) : GNode LG.garden.tree ⊕ GNode (capForest w) → ℕ
  | .inl a => LG.layer a
  | .inr c => (flowerOf LG.garden c.1.1).elim p fun ℓ => LG.layer ℓ.toNode

/-- The capped layering. -/
def capLayer (LG : LayeredGarden w) (p : ℕ) : GNode (capGarden LG.garden).tree → ℕ :=
  fun x => capLayerS LG p ((cNode LG.garden).symm x)

@[simp] theorem capLayer_embN (LG : LayeredGarden w) (p : ℕ) (a : GNode LG.garden.tree) :
    capLayer LG p (embN LG.garden a) = LG.layer a := by
  simp [capLayer, capLayerS]

@[simp] theorem capLayer_capN (LG : LayeredGarden w) (p : ℕ) (j : Fin w) :
    capLayer LG p (capN LG.garden j) = (flowerOf LG.garden j).elim p fun ℓ => LG.layer ℓ.toNode := by
  simp only [capLayer, Equiv.symm_apply_apply, capLayerS]; rfl

theorem capLayer_isLayering (LG : LayeredGarden w) (p : ℕ) :
    IsLayering (capGarden LG.garden) (capLayer LG p) := by
  constructor
  · intro b i
    obtain ⟨b, rfl⟩ := (cBranch LG.garden).surjective b
    rw [cBranch_child, cBranch_toNode, capLayer_embN, capLayer_embN]
    exact LG.isLayering.1 b i
  · intro x
    rcases leaf_cases LG.garden x with ⟨ℓ, rfl⟩ | ⟨j, rfl⟩
    · rw [capGarden_pair_embL]
      by_cases hc : flowerOf LG.garden ℓ.1.1 = some ℓ
      · rw [ite_eq_left hc, embL_toNode, capL_toNode, capLayer_embN, capLayer_capN, hc]; rfl
      · rw [ite_eq_right hc, embL_toNode, embL_toNode, capLayer_embN, capLayer_embN]
        exact LG.isLayering.2 ℓ
    · rw [capGarden_pair_capL]
      rcases hf : flowerOf LG.garden j with _ | ℓ
      · rfl
      · show capLayer LG p (capL LG.garden j).toNode = capLayer LG p (embL LG.garden ℓ).toNode
        rw [embL_toNode, capL_toNode, capLayer_embN, capLayer_capN, hf]; rfl

/-- **The capped layered garden** `capLayered LG p` (supplement Lemma 2.1): width `2 * w`; caps in the layer of
their flowers (`p` on the carrier, `capLayered_layer_capN_of`). -/
@[reducible] def capLayered (LG : LayeredGarden w) (p : ℕ) : LayeredGarden (2 * w) where
  garden := capGarden LG.garden
  layer := capLayer LG p
  isLayering := capLayer_isLayering LG p

theorem capLayered_layer_embN (LG : LayeredGarden w) (p : ℕ) (a : GNode LG.garden.tree) :
    (capLayered LG p).layer (embN LG.garden a) = LG.layer a := capLayer_embN LG p a

/-- On the carrier (flowers in layer `p`) the caps are in layer `p`. -/
theorem capLayered_layer_capN_of (LG : LayeredGarden w) (p : ℕ)
    (hfl : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ → LG.layer ℓ.toNode = p) (j : Fin w) :
    (capLayered LG p).layer (capN LG.garden j) = p := by
  show capLayer LG p (capN LG.garden j) = p
  rw [capLayer_capN]
  rcases hf : flowerOf LG.garden j with _ | ℓ
  · rfl
  · exact hfl ℓ (flowerOf_spec hf).2

end WaveTurbulence.Flower.CapsId
