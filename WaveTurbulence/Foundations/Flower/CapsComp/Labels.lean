/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsComp.Components
public import WaveTurbulence.Foundations.Flower.CapsId.Transport
/-! # A3b CAPS-COMP: the per-original-tree labels of a capped garden (supplement Lemma 2.1(4))

The kind (`FlowerKindOK`), pattern (`PatValid`) and stem-layer conditions of the flower carrier read only one original
tree. On a capped garden (caps `J`) they are written with capped flowers (`IsCapFlower`) in place of flowers:
`CapKindOK`, `CapPatExist`, `CapStem`. They are transported
* through capping (`capLayered`, caps `capJ w`): `flowerKindOK_iff_cap`, `patValid_iff_cap`, `stem_iff_cap`;
* through the n-ary glue (caps `resJ σ J c` in component `c`): `capKindOK_glueN`, `capPatExist_glueN`,
  `capStem_glueN`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsComp
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue WaveTurbulence.Flower.CapsId
open WaveTurbulence.Flower.MkDefs

section Defs

variable {w : ℕ}

/-- A capped flower node. -/
def IsCapFlowerNode (LG : LayeredGarden w) (J : Finset (Fin w)) (a : GNode LG.garden.tree) : Prop :=
  ∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.toNode = a

/-- The kind restriction of the original tree `j` of a capped garden (`FlowerKindOK` with capped flowers). -/
def CapKindOK (LG : LayeredGarden w) (J : Finset (Fin w)) (p Ntr : ℕ) (j : Fin w) : FlowerKind → Prop
  | .X => 1 ≤ LG.topOrder p j ∧ LG.topOrder p j ≤ Ntr
  | .Y => Ntr < LG.topOrder p j ∧ ∀ b : GBranch LG.garden.tree, b.1 = (j, []) →
      ∀ i : Fin 3, LG.topCountBelow p (b.child i) ≤ Ntr
  | .W => Ntr < LG.topOrder p j ∧ ∀ b : GBranch LG.garden.tree, b.1.1 = j → IsCapFlowerParent LG J b →
      (∀ i : Fin 3, ¬ IsCapFlowerNode LG J (b.child i) → LG.topCountBelow p (b.child i) ≤ Ntr) ∧
      LG.topOrder p j - LG.topCountBelow p b.toNode ≤ Ntr

/-- The pattern validity of the original tree `j` of a capped garden (`PatValid` with capped flowers). -/
def CapPatExist (LG : LayeredGarden w) (J : Finset (Fin w)) (p : ℕ) (j : Fin w) : FixPat → Prop
  | .plain => True
  | .dRoot => ∃ b : GBranch LG.garden.tree, b.1 = (j, []) ∧ ¬ IsCapFlowerParent LG J b
  | .dParent => ∃ b c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ c.1.1 = j ∧ c.IsChildOf b
  | .dChild i => ∃ b c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ c.1.1 = j ∧
      b.1.1 = j ∧ b.1.2 = c.1.2 ++ [i] ∧ LG.layer b.toNode = p

/-- The stem of the original tree `j` lies in layer `p`. -/
def CapStem (LG : LayeredGarden w) (J : Finset (Fin w)) (p : ℕ) (j : Fin w) : Prop :=
  ∀ a : GNode LG.garden.tree, a.1.1 = j → OnCapStem LG J a → LG.layer a = p

end Defs

/-! ## Transport through capping -/

section Cap

variable {w : ℕ}

theorem topCountBelow_capLayered (LG : LayeredGarden w) (p q : ℕ) (a : GNode LG.garden.tree) :
    (capLayered LG p).topCountBelow q (embN LG.garden a) = LG.topCountBelow q a := by
  unfold LayeredGarden.topCountBelow
  have : (univ.filter fun b : GBranch (capLayered LG p).garden.tree =>
      (embN LG.garden a).IsDesc b.toNode ∧ (capLayered LG p).layer b.toNode = q) =
      (univ.filter fun b : GBranch LG.garden.tree => a.IsDesc b.toNode ∧ LG.layer b.toNode = q).map
        (cBranch LG.garden).toEmbedding := by
    ext b
    obtain ⟨b, rfl⟩ := (cBranch LG.garden).surjective b
    rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
    simp only [mem_filter, mem_univ, true_and, cBranch_toNode, capLayer_embN, isDesc_embN]
  rw [this, card_map]

theorem isChildOf_cBranch (G : Garden w) (b' b : GBranch G.tree) :
    (cBranch G b').IsChildOf (cBranch G b) ↔ b'.IsChildOf b := by
  simp only [GBranch.IsChildOf, cBranch_val, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq]

theorem isCapFlowerNode_embN (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) (a : GNode LG.garden.tree) :
    IsCapFlowerNode (capLayered LG p) (capJ w) (embN LG.garden a) ↔ LG.IsFlowerNode a :=
  capFlowerNode_iff LG p hF a

theorem forall_branch_cap (G : Garden w) (Q : GBranch (capGarden G).tree → Prop) :
    (∀ b, Q b) ↔ ∀ b, Q (cBranch G b) :=
  ⟨fun h b => h _, fun h b => by obtain ⟨b, rfl⟩ := (cBranch G).surjective b; exact h b⟩

theorem exists_branch_cap (G : Garden w) (Q : GBranch (capGarden G).tree → Prop) :
    (∃ b, Q b) ↔ ∃ b, Q (cBranch G b) :=
  ⟨fun ⟨b, hb⟩ => by obtain ⟨b, rfl⟩ := (cBranch G).surjective b; exact ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨_, hb⟩⟩

theorem cBranch_root_iff (G : Garden w) (b : GBranch G.tree) (j : Fin w) :
    (cBranch G b).1 = (capσ w (.inl j), []) ↔ b.1 = (j, []) := by
  rw [cBranch_val]
  simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq]
  exact ⟨fun ⟨h1, h2⟩ => Prod.ext h1 h2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

theorem cBranch_tree_iff (G : Garden w) (b : GBranch G.tree) (j : Fin w) :
    (cBranch G b).1.1 = capσ w (.inl j) ↔ b.1.1 = j := by
  rw [cBranch_val]
  simp only [EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq]

/-- The kind restriction is the capped kind restriction of every original tree. -/
theorem flowerKindOK_iff_cap (LG : LayeredGarden w) (p Ntr : ℕ) (hF : OneFlower LG.garden) (kind : FlowerKind) :
    LG.FlowerKindOK p Ntr kind ↔ ∀ j, CapKindOK (capLayered LG p) (capJ w) p Ntr (capσ w (.inl j)) kind := by
  cases kind with
  | X =>
    simp only [LayeredGarden.FlowerKindOK, CapKindOK, topOrder_capLayered]
  | Y =>
    simp only [LayeredGarden.FlowerKindOK, CapKindOK, topOrder_capLayered]
    refine forall_congr' fun j => and_congr Iff.rfl ?_
    rw [forall_branch_cap]
    refine forall_congr' fun b => ?_
    rw [cBranch_root_iff]
    simp only [cBranch_child, topCountBelow_capLayered]
  | W =>
    simp only [LayeredGarden.FlowerKindOK, CapKindOK, topOrder_capLayered]
    refine forall_congr' fun j => and_congr Iff.rfl ?_
    rw [forall_branch_cap]
    refine forall_congr' fun b => ?_
    rw [cBranch_tree_iff, isCapFlowerParent_cBranch LG p hF]
    simp only [cBranch_child, cBranch_toNode, topCountBelow_capLayered, isCapFlowerNode_embN LG p hF]

/-- The pattern validity is the capped pattern validity of the original tree. -/
theorem patValid_iff_cap (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) (j : Fin w) (pat : FixPat) :
    LG.PatValid p j pat ↔ CapPatExist (capLayered LG p) (capJ w) p (capσ w (.inl j)) pat := by
  cases pat with
  | plain => exact Iff.rfl
  | dRoot =>
    simp only [LayeredGarden.PatValid, CapPatExist]
    rw [exists_branch_cap]
    refine exists_congr fun b => ?_
    rw [cBranch_root_iff, isCapFlowerParent_cBranch LG p hF]
  | dParent =>
    simp only [LayeredGarden.PatValid, CapPatExist]
    rw [exists_branch_cap]
    refine exists_congr fun b => ?_
    rw [exists_branch_cap]
    refine exists_congr fun c => ?_
    rw [isCapFlowerParent_cBranch LG p hF, cBranch_tree_iff, isChildOf_cBranch]
  | dChild i =>
    simp only [LayeredGarden.PatValid, CapPatExist]
    rw [exists_branch_cap]
    refine exists_congr fun b => ?_
    rw [exists_branch_cap]
    refine exists_congr fun c => ?_
    rw [isCapFlowerParent_cBranch LG p hF, cBranch_tree_iff, cBranch_tree_iff, cBranch_toNode]
    show _ ↔ _ ∧ _ ∧ _ ∧ _ ∧ capLayer LG p (embN LG.garden b.toNode) = p
    rw [capLayer_embN]
    exact Iff.rfl

/-- The stem condition is the capped stem condition of every original tree. -/
theorem stem_iff_cap (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) :
    (∀ a, LG.OnStem a → LG.layer a = p) ↔ ∀ j, CapStem (capLayered LG p) (capJ w) p (capσ w (.inl j)) := by
  constructor
  · intro h j x hx hst
    rcases node_cases LG.garden x with ⟨a, rfl⟩ | ⟨j', rfl⟩
    · rw [capLayered_layer_embN]
      exact h a ((onCapStem_embN LG p hF a).1 hst)
    · exfalso
      have : capσ w (.inr j') = capσ w (.inl j) := hx
      exact Sum.inr_ne_inl ((capσ w).injective this)
  · intro h a ha
    have := h a.1.1 (embN LG.garden a) rfl ((onCapStem_embN LG p hF a).2 ha)
    rwa [capLayered_layer_embN] at this

end Cap

/-! ## Transport through the n-ary glue -/

section Glue

variable {m w : ℕ} {a : Fin m → ℕ}

theorem glueBranchN_tree_eq (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree)
    {c c' : Fin m} (i : Fin (a c)) (y : GBranch (TA c')) :
    (glueBranchN σ TA ⟨c', y⟩).1.1 = σ ⟨c, i⟩ ↔ ∃ h : c' = c, h ▸ y.1.1 = i := by
  rw [glueBranchN_val]
  exact sigma_val_eq_iff σ i y.1.1

theorem topCountBelow_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c)) (p : ℕ)
    (c : Fin m) (x : GNode (LA c).garden.tree) :
    (glueL σ LA).topCountBelow p (glueNodeN σ (fun c => (LA c).garden.tree) ⟨c, x⟩) = (LA c).topCountBelow p x := by
  unfold LayeredGarden.topCountBelow
  symm
  apply Finset.card_bij (fun y _ => glueBranchN σ (fun c => (LA c).garden.tree) ⟨c, y⟩)
  · intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    rw [glueBranchN_toNode, glueN_isDesc_same, gLayerN_apply]
    exact hy
  · intro y _ y' _ e
    have := (glueBranchN σ fun c => (LA c).garden.tree).injective e
    simpa using this
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    obtain ⟨⟨c', y⟩, rfl⟩ := (glueBranchN σ fun c => (LA c).garden.tree).surjective b
    rw [glueBranchN_toNode] at hb
    by_cases hc : c' = c
    · subst hc
      refine ⟨y, ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and]
      rw [glueN_isDesc_same, gLayerN_apply] at hb
      exact hb
    · exact absurd hb.1 (glueN_not_isDesc σ (fun c => (LA c).garden.tree) (Ne.symm hc) x y.toNode)

theorem topOrder_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c)) (p : ℕ)
    (c : Fin m) (i : Fin (a c)) :
    (glueL σ LA).topOrder p (σ ⟨c, i⟩) = (LA c).topOrder p i := by
  unfold LayeredGarden.topOrder
  symm
  apply Finset.card_bij (fun y _ => glueBranchN σ (fun c => (LA c).garden.tree) ⟨c, y⟩)
  · intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    refine ⟨by rw [glueBranchN_val, hy.1], (glueL_layer_branch σ LA c y).trans hy.2⟩
  · intro y _ y' _ e
    have := (glueBranchN σ fun c => (LA c).garden.tree).injective e
    simpa using this
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    obtain ⟨⟨c', y⟩, rfl⟩ := (glueBranchN σ fun c => (LA c).garden.tree).surjective b
    obtain ⟨rfl, hy⟩ := (glueBranchN_tree_eq σ (fun c => (LA c).garden.tree) i y).1 hb.1
    refine ⟨y, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨hy, (glueL_layer_branch σ LA c' y).symm.trans hb.2⟩

theorem isCapFlowerNode_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (c : Fin m) (x : GNode (LA c).garden.tree) :
    IsCapFlowerNode (glueL σ LA) J (glueNodeN σ (fun c => (LA c).garden.tree) ⟨c, x⟩) ↔
      IsCapFlowerNode (LA c) (resJ σ J c) x := by
  unfold IsCapFlowerNode
  rw [exists_leaf_glueN]
  constructor
  · rintro ⟨c', y, h1, h2⟩
    rw [glueLeafN_toNode] at h2
    have := (glueNodeN σ fun c => (LA c).garden.tree).injective h2
    simp only [Sigma.mk.injEq] at this
    obtain ⟨rfl, h3⟩ := this
    exact ⟨y, (isCapFlower_glueN σ LA J c' y).1 h1, eq_of_heq h3⟩
  · rintro ⟨y, h1, h2⟩
    exact ⟨c, y, (isCapFlower_glueN σ LA J c y).2 h1, by rw [glueLeafN_toNode, h2]⟩

theorem forall_branch_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree)
    (Q : GBranch (CapsGlue.gT σ TA) → Prop) :
    (∀ b, Q b) ↔ ∀ (c : Fin m) (y : GBranch (TA c)), Q (glueBranchN σ TA ⟨c, y⟩) :=
  ⟨fun h c y => h _, fun h b => by obtain ⟨⟨c, y⟩, rfl⟩ := (glueBranchN σ TA).surjective b; exact h c y⟩

/-- Restricted to a fixed component: statements over the branches of the tree `σ ⟨c, i⟩` of the glue. -/
theorem forall_branch_tree_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree)
    (c : Fin m) (i : Fin (a c)) (Q : GBranch (CapsGlue.gT σ TA) → Prop) :
    (∀ b : GBranch (CapsGlue.gT σ TA), b.1.1 = σ ⟨c, i⟩ → Q b) ↔
      ∀ y : GBranch (TA c), y.1.1 = i → Q (glueBranchN σ TA ⟨c, y⟩) := by
  rw [forall_branch_glueN]
  constructor
  · intro h y hy
    exact h c y (by rw [glueBranchN_val, hy])
  · intro h c' y hy
    obtain ⟨rfl, hy'⟩ := (glueBranchN_tree_eq σ TA i y).1 hy
    exact h y hy'

theorem exists_branch_tree_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree)
    (c : Fin m) (i : Fin (a c)) (Q : GBranch (CapsGlue.gT σ TA) → Prop) :
    (∃ b : GBranch (CapsGlue.gT σ TA), b.1.1 = σ ⟨c, i⟩ ∧ Q b) ↔
      ∃ y : GBranch (TA c), y.1.1 = i ∧ Q (glueBranchN σ TA ⟨c, y⟩) := by
  constructor
  · rintro ⟨b, hb, hq⟩
    obtain ⟨⟨c', y⟩, rfl⟩ := (glueBranchN σ TA).surjective b
    obtain ⟨rfl, hy'⟩ := (glueBranchN_tree_eq σ TA i y).1 hb
    exact ⟨y, hy', hq⟩
  · rintro ⟨y, hy, hq⟩
    exact ⟨_, by rw [glueBranchN_val, hy], hq⟩

theorem capKindOK_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (p Ntr : ℕ) (c : Fin m) (i : Fin (a c)) (kind : FlowerKind) :
    CapKindOK (glueL σ LA) J p Ntr (σ ⟨c, i⟩) kind ↔ CapKindOK (LA c) (resJ σ J c) p Ntr i kind := by
  cases kind with
  | X => simp only [CapKindOK, topOrder_glueN]
  | Y =>
    simp only [CapKindOK, topOrder_glueN]
    refine and_congr Iff.rfl ?_
    have e : ∀ b : GBranch (glueL σ LA).garden.tree, b.1 = (σ ⟨c, i⟩, []) ↔
        b.1.1 = σ ⟨c, i⟩ ∧ b.1.2 = [] := fun b => Prod.ext_iff
    simp only [e, and_imp]
    rw [forall_branch_tree_glueN σ (fun c => (LA c).garden.tree) c i
      (fun b => b.1.2 = [] → ∀ k : Fin 3, (glueL σ LA).topCountBelow p (b.child k) ≤ Ntr)]
    refine forall_congr' fun y => ?_
    simp only [glueBranchN_val, glueBranchN_child, topCountBelow_glueN, Prod.ext_iff]
    exact ⟨fun h h1 => h h1.1 h1.2, fun h h1 h2 => h ⟨h1, h2⟩⟩
  | W =>
    simp only [CapKindOK, topOrder_glueN]
    refine and_congr Iff.rfl ?_
    rw [forall_branch_tree_glueN σ (fun c => (LA c).garden.tree) c i]
    refine forall_congr' fun y => forall_congr' fun _ => ?_
    rw [isCapFlowerParent_glueN]
    simp only [glueBranchN_child, glueBranchN_toNode, topCountBelow_glueN, isCapFlowerNode_glueN]

theorem capPatExist_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (p : ℕ) (c : Fin m) (i : Fin (a c)) (pat : FixPat) :
    CapPatExist (glueL σ LA) J p (σ ⟨c, i⟩) pat ↔ CapPatExist (LA c) (resJ σ J c) p i pat := by
  cases pat with
  | plain => exact Iff.rfl
  | dRoot =>
    simp only [CapPatExist]
    have e : ∀ b : GBranch (glueL σ LA).garden.tree, (b.1 = (σ ⟨c, i⟩, []) ∧ ¬ IsCapFlowerParent (glueL σ LA) J b) ↔
        b.1.1 = σ ⟨c, i⟩ ∧ (b.1.2 = [] ∧ ¬ IsCapFlowerParent (glueL σ LA) J b) := fun b => by
      rw [Prod.ext_iff, and_assoc]
    simp only [e]
    rw [exists_branch_tree_glueN σ (fun c => (LA c).garden.tree) c i]
    refine exists_congr fun y => ?_
    rw [isCapFlowerParent_glueN, glueBranchN_val, Prod.ext_iff]
    simp only [and_assoc]
  | dParent =>
    simp only [CapPatExist]
    constructor
    · rintro ⟨b, cc, h1, h2, h3⟩
      obtain ⟨⟨c', y⟩, rfl⟩ := (glueBranchN σ fun c => (LA c).garden.tree).surjective cc
      obtain ⟨rfl, hy⟩ := (glueBranchN_tree_eq σ (fun c => (LA c).garden.tree) i y).1 h2
      obtain ⟨⟨c'', z⟩, rfl⟩ := (glueBranchN σ fun c => (LA c).garden.tree).surjective b
      by_cases hc : c' = c''
      · subst hc
        exact ⟨z, y, (isCapFlowerParent_glueN σ LA J c' y).1 h1, hy, (glueN_isChildOf_same σ (fun c => (LA c).garden.tree) c' y z).1 h3⟩
      · exact absurd h3 (glueN_not_isChildOf σ (fun c => (LA c).garden.tree) hc y z)
    · rintro ⟨z, y, h1, h2, h3⟩
      exact ⟨_, _, (isCapFlowerParent_glueN σ LA J c y).2 h1, by rw [glueBranchN_val, h2],
        (glueN_isChildOf_same σ (fun c => (LA c).garden.tree) c y z).2 h3⟩
  | dChild k =>
    simp only [CapPatExist]
    constructor
    · rintro ⟨b, cc, h1, h2, h3, h4, h5⟩
      obtain ⟨⟨c', y⟩, rfl⟩ := (glueBranchN σ fun c => (LA c).garden.tree).surjective cc
      obtain ⟨rfl, hy⟩ := (glueBranchN_tree_eq σ (fun c => (LA c).garden.tree) i y).1 h2
      obtain ⟨⟨c'', z⟩, rfl⟩ := (glueBranchN σ fun c => (LA c).garden.tree).surjective b
      obtain ⟨rfl, hz⟩ := (glueBranchN_tree_eq σ (fun c => (LA c).garden.tree) i z).1 h3
      refine ⟨z, y, (isCapFlowerParent_glueN σ LA J _ y).1 h1, hy, hz, ?_, ?_⟩
      · simpa using h4
      · exact (glueL_layer_branch σ LA _ z).symm.trans h5
    · rintro ⟨z, y, h1, h2, h3, h4, h5⟩
      exact ⟨_, _, (isCapFlowerParent_glueN σ LA J c y).2 h1, by rw [glueBranchN_val, h2],
        by rw [glueBranchN_val, h3], by simpa using h4, (glueL_layer_branch σ LA c z).trans h5⟩

theorem capStem_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (p : ℕ) (c : Fin m) (i : Fin (a c)) :
    CapStem (glueL σ LA) J p (σ ⟨c, i⟩) ↔ CapStem (LA c) (resJ σ J c) p i := by
  unfold CapStem
  constructor
  · intro h x hx hst
    have := h (glueNodeN σ (fun c => (LA c).garden.tree) ⟨c, x⟩) (by rw [glueNodeN_val, hx])
      ((onCapStem_glueN σ LA J c x).2 hst)
    rwa [glueL_layer] at this
  · intro h x hx hst
    obtain ⟨⟨c', y⟩, rfl⟩ := (glueNodeN σ fun c => (LA c).garden.tree).surjective x
    rw [glueNodeN_val] at hx
    obtain ⟨rfl, hy⟩ := (sigma_val_eq_iff σ i y.1.1).1 hx
    rw [glueL_layer]
    exact h y hy ((onCapStem_glueN σ LA J c' y).1 hst)

end Glue

end WaveTurbulence.Flower.CapsComp
