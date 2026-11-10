/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsComp.Restrict
public import WaveTurbulence.Foundations.Flower.CapsGlue.Stem
public import WaveTurbulence.Foundations.Flower.CapsGlue.Weights2
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Closed
/-! # A3b CAPS-COMP: irreducible components of a plain garden, and of an n-ary glue

* `compOf G i`: the smallest pairing-closed set of trees containing tree `i` (the irreducible component of `i`);
  `rep G i` its least element. These partition the trees (`compOf_eq_of_mem`, `mem_compOf_iff_rep`).
* For the glue `glueL σ LA` of irreducible plain components, the component of the tree `σ ⟨c, i⟩` is the block
  `{σ ⟨c, ·⟩}` (`compOf_glueN`); conversely the restrictions to the components of a plain garden are irreducible.
* The canonicity criterion and plainness of a glue are those of its pieces (`canonCriterion_glueN`,
  `isPlain_glueN`; n-ary versions of FLOWER-P7's `glue_canonCriterion_iff`). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsComp
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue

/-! ## Components of a plain garden -/

section Comp

variable {W : ℕ}

/-- The irreducible component of tree `i`: the intersection of all pairing-closed sets of trees containing `i`. -/
def compOf (G : Garden W) (i : Fin W) : Finset (Fin W) :=
  univ.filter fun j => ∀ T : Finset (Fin W), ClosedTrees G T → i ∈ T → j ∈ T

theorem mem_compOf {G : Garden W} {i j : Fin W} :
    j ∈ compOf G i ↔ ∀ T, ClosedTrees G T → i ∈ T → j ∈ T := by simp [compOf]

theorem self_mem_compOf (G : Garden W) (i : Fin W) : i ∈ compOf G i :=
  mem_compOf.2 fun _ _ h => h

theorem compOf_subset {G : Garden W} {i : Fin W} {T : Finset (Fin W)} (hT : ClosedTrees G T) (hi : i ∈ T) :
    compOf G i ⊆ T := fun _ hj => mem_compOf.1 hj T hT hi

theorem closedTrees_compOf {G : Garden W} (hG : G.IsPlain) (i : Fin W) : ClosedTrees G (compOf G i) := by
  rw [closedTrees_iff G hG]
  intro ℓ hℓ
  rw [mem_compOf] at hℓ ⊢
  intro T hT hi
  exact (closedTrees_iff G hG T).1 hT ℓ (hℓ T hT hi)

theorem mem_compOf_symm {G : Garden W} (hG : G.IsPlain) {i j : Fin W} (h : j ∈ compOf G i) : i ∈ compOf G j := by
  by_contra hi
  have hcl := closedTrees_sdiff G hG (closedTrees_compOf hG i) (closedTrees_compOf hG j)
  have := compOf_subset hcl (mem_sdiff.2 ⟨self_mem_compOf G i, hi⟩)
  exact (mem_sdiff.1 (this h)).2 (self_mem_compOf G j)

theorem compOf_eq_of_mem {G : Garden W} (hG : G.IsPlain) {i j : Fin W} (h : j ∈ compOf G i) :
    compOf G j = compOf G i :=
  le_antisymm (compOf_subset (closedTrees_compOf hG i) h)
    (compOf_subset (closedTrees_compOf hG j) (mem_compOf_symm hG h))

/-- The least tree of the component of `i`. -/
def rep (G : Garden W) (i : Fin W) : Fin W := (compOf G i).min' ⟨i, self_mem_compOf G i⟩

theorem rep_mem (G : Garden W) (i : Fin W) : rep G i ∈ compOf G i := Finset.min'_mem _ _

theorem rep_le (G : Garden W) (i : Fin W) : rep G i ≤ i := Finset.min'_le _ _ (self_mem_compOf G i)

theorem rep_eq_of_compOf_eq {G : Garden W} {i j : Fin W} (h : compOf G j = compOf G i) : rep G j = rep G i := by
  unfold rep
  congr 1

theorem mem_compOf_iff_rep {G : Garden W} (hG : G.IsPlain) {i j : Fin W} :
    j ∈ compOf G i ↔ rep G j = rep G i := by
  constructor
  · intro h; exact rep_eq_of_compOf_eq (compOf_eq_of_mem hG h)
  · intro h
    have h1 := compOf_eq_of_mem hG (rep_mem G j)
    have h2 := compOf_eq_of_mem hG (rep_mem G i)
    rw [h] at h1
    rw [← h1.symm.trans h2]
    exact self_mem_compOf G j

theorem rep_rep {G : Garden W} (hG : G.IsPlain) (i : Fin W) : rep G (rep G i) = rep G i :=
  (mem_compOf_iff_rep hG).1 (rep_mem G i)

end Comp

/-! ## Gluing: leaves below, complete pairing, incomparability, the criterion -/

variable {m w : ℕ} {a : Fin m → ℕ}

theorem leavesBelow_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) (c : Fin m)
    (x : GNode (TA c)) :
    (glueNodeN σ TA ⟨c, x⟩).leavesBelow = x.leavesBelow.image fun ℓ => glueLeafN σ TA ⟨c, ℓ⟩ := by
  ext ℓ
  obtain ⟨⟨c', y⟩, rfl⟩ := (glueLeafN σ TA).surjective ℓ
  simp only [GNode.leavesBelow, mem_filter, mem_univ, true_and, mem_image]
  rw [glueLeafN_toNode]
  by_cases hc : c' = c
  · subst hc
    rw [glueN_isDesc_same]
    constructor
    · intro h; exact ⟨y, h, rfl⟩
    · rintro ⟨y', hy', e⟩
      have := (glueLeafN σ TA).injective e
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
      rw [← this]; exact hy'
  · constructor
    · intro h; exact absurd h (glueN_not_isDesc σ TA (Ne.symm hc) x y.toNode)
    · rintro ⟨y', -, e⟩
      have := (glueLeafN σ TA).injective e
      simp only [Sigma.mk.injEq] at this
      exact absurd this.1.symm hc

theorem completelyPaired_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (c : Fin m) (S : Finset (GLeaf (LA c).garden.tree)) :
    (glueL σ LA).garden.CompletelyPaired (S.image fun ℓ => glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, ℓ⟩) ↔
      (LA c).garden.CompletelyPaired S := by
  unfold Garden.CompletelyPaired
  constructor
  · intro h ℓ hℓ
    obtain ⟨h1, h2⟩ := h _ (mem_image_of_mem _ hℓ)
    rw [show (glueL σ LA).garden.pair = (glueGardenN σ fun c => (LA c).garden).pair from rfl,
      glueN_pair_leaf] at h1 h2
    refine ⟨fun e => h1 (by rw [e]), ?_⟩
    obtain ⟨ℓ', hℓ', e⟩ := mem_image.1 h2
    have := (glueLeafN σ _).injective e
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
    rwa [← this]
  · intro h x hx
    obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.1 hx
    obtain ⟨h1, h2⟩ := h ℓ hℓ
    rw [show (glueL σ LA).garden.pair = (glueGardenN σ fun c => (LA c).garden).pair from rfl, glueN_pair_leaf]
    refine ⟨fun e => h1 ?_, mem_image_of_mem _ h2⟩
    have := (glueLeafN σ _).injective e
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
    exact this

/-- A cross pair cannot be completely paired. -/
theorem not_cp_cross_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c)) {c c' : Fin m}
    (hc : c ≠ c') (x : GNode (LA c).garden.tree) (x' : GNode (LA c').garden.tree) :
    ¬ (glueL σ LA).garden.CompletelyPaired
      ((glueNodeN σ (fun c => (LA c).garden.tree) ⟨c, x⟩).leavesBelow ∪
        (glueNodeN σ (fun c => (LA c).garden.tree) ⟨c', x'⟩).leavesBelow) := by
  intro h
  rw [leavesBelow_glueN, leavesBelow_glueN] at h
  have hA : (LA c).garden.CompletelyPaired x.leavesBelow := by
    intro ℓ hℓ
    obtain ⟨h1, h2⟩ := h _ (mem_union_left _ (mem_image_of_mem _ hℓ))
    rw [show (glueL σ LA).garden.pair = (glueGardenN σ fun c => (LA c).garden).pair from rfl,
      glueN_pair_leaf] at h1 h2
    refine ⟨fun e => h1 (by rw [e]), ?_⟩
    rcases mem_union.1 h2 with h3 | h3
    · obtain ⟨ℓ'', hℓ'', e⟩ := mem_image.1 h3
      have := (glueLeafN σ _).injective e
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
      rwa [← this]
    · obtain ⟨ℓ'', _, e⟩ := mem_image.1 h3
      have := (glueLeafN σ _).injective e
      simp only [Sigma.mk.injEq] at this
      exact absurd this.1.symm hc
  have he := Canon.even_card_of_completelyPaired (LA c).garden x.leavesBelow.card x.leavesBelow rfl hA
  exact (Nat.not_even_iff_odd.2 (Canon.odd_card_leavesBelow x)) he

theorem incomparable_glueN_same (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) (c : Fin m)
    (x x' : GNode (TA c)) :
    (glueNodeN σ TA ⟨c, x⟩).Incomparable (glueNodeN σ TA ⟨c, x'⟩) ↔ x.Incomparable x' := by
  unfold GNode.Incomparable
  rw [glueN_isDesc_same, glueN_isDesc_same]

/-- **The canonicity criterion of an n-ary glue** is the criterion of every piece. -/
theorem canonCriterion_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c)) (p : ℕ) :
    (glueL σ LA).CanonCriterion p ↔ ∀ c, (LA c).CanonCriterion p := by
  unfold LayeredGarden.CanonCriterion
  constructor
  · rintro ⟨hl, h⟩ c
    refine ⟨fun x => ?_, fun x x' hinc hcp => ?_⟩
    · have := hl (glueNodeN σ (fun c => (LA c).garden.tree) ⟨c, x⟩)
      rwa [glueL_layer] at this
    · have h1 := h (glueNodeN σ (fun c => (LA c).garden.tree) ⟨c, x⟩)
        (glueNodeN σ (fun c => (LA c).garden.tree) ⟨c, x'⟩)
        ((incomparable_glueN_same σ (fun c => (LA c).garden.tree) c x x').2 hinc) (by
          rw [leavesBelow_glueN, leavesBelow_glueN, ← image_union]
          exact (completelyPaired_glueN σ LA c _).2 hcp)
      rwa [parentLayer_glueN, parentLayer_glueN, glueL_layer, glueL_layer] at h1
  · intro hA
    refine ⟨fun x => ?_, fun x x' hinc hcp => ?_⟩
    · obtain ⟨⟨c, y⟩, rfl⟩ := (glueNodeN σ fun c => (LA c).garden.tree).surjective x
      rw [glueL_layer]; exact (hA c).1 y
    · obtain ⟨⟨c, y⟩, rfl⟩ := (glueNodeN σ fun c => (LA c).garden.tree).surjective x
      obtain ⟨⟨c', y'⟩, rfl⟩ := (glueNodeN σ fun c => (LA c).garden.tree).surjective x'
      by_cases hc : c = c'
      · subst hc
        rw [parentLayer_glueN, parentLayer_glueN, glueL_layer, glueL_layer]
        refine (hA c).2 y y' ((incomparable_glueN_same σ (fun c => (LA c).garden.tree) c y y').1 hinc) ?_
        rw [leavesBelow_glueN, leavesBelow_glueN, ← image_union] at hcp
        exact (completelyPaired_glueN σ LA c _).1 hcp
      · exact absurd hcp (not_cp_cross_glueN σ LA hc y y')

theorem isPlain_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c)) :
    (glueL σ LA).garden.IsPlain ↔ ∀ c, (LA c).garden.IsPlain := by
  constructor
  · intro h c ℓ
    have := h (glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, ℓ⟩)
    rwa [show (glueL σ LA).garden.mark = (glueGardenN σ fun c => (LA c).garden).mark from rfl,
      glueN_mark_leaf] at this
  · intro h ℓ
    obtain ⟨⟨c, y⟩, rfl⟩ := (glueLeafN σ fun c => (LA c).garden.tree).surjective ℓ
    rw [show (glueL σ LA).garden.mark = (glueGardenN σ fun c => (LA c).garden).mark from rfl, glueN_mark_leaf]
    exact h c y

/-! ## Closed sets and components of a glue -/

/-- The block of component `c`. -/
def blockOf (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (c : Fin m) : Finset (Fin w) :=
  univ.image fun i => σ ⟨c, i⟩

theorem mem_blockOf (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (c : Fin m) (x : Fin w) :
    x ∈ blockOf σ c ↔ (σ.symm x).1 = c := by
  simp only [blockOf, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; simp
  · intro h
    refine ⟨h ▸ (σ.symm x).2, ?_⟩
    subst h
    exact σ.apply_symm_apply x

theorem pair_glueN_fst (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (ℓ : GLeaf (glueL σ LA).garden.tree) :
    (σ.symm ((glueL σ LA).garden.pair ℓ).1.1).1 = (σ.symm ℓ.1.1).1 := by
  obtain ⟨⟨c, y⟩, rfl⟩ := (glueLeafN σ fun c => (LA c).garden.tree).surjective ℓ
  rw [show (glueL σ LA).garden.pair = (glueGardenN σ fun c => (LA c).garden).pair from rfl, glueN_pair_leaf]
  simp

theorem closedTrees_blockOf (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (hpl : (glueL σ LA).garden.IsPlain) (c : Fin m) : ClosedTrees (glueL σ LA).garden (blockOf σ c) := by
  rw [closedTrees_iff _ hpl]
  intro ℓ hℓ
  rw [mem_blockOf] at hℓ ⊢
  rw [pair_glueN_fst, hℓ]

/-- The preimage in component `c` of a set of trees of the glue. -/
def preBlock (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (c : Fin m) (T : Finset (Fin w)) : Finset (Fin (a c)) :=
  univ.filter fun i => σ ⟨c, i⟩ ∈ T

theorem closedTrees_preBlock (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (hpl : (glueL σ LA).garden.IsPlain) (c : Fin m) {T : Finset (Fin w)}
    (hT : ClosedTrees (glueL σ LA).garden T) : ClosedTrees (LA c).garden (preBlock σ c T) := by
  rw [closedTrees_iff _ ((isPlain_glueN σ LA).1 hpl c)]
  rw [closedTrees_iff _ hpl] at hT
  intro ℓ hℓ
  simp only [preBlock, mem_filter, mem_univ, true_and] at hℓ ⊢
  have := hT (glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, ℓ⟩) hℓ
  rwa [show (glueL σ LA).garden.pair = (glueGardenN σ fun c => (LA c).garden).pair from rfl,
    glueN_pair_leaf] at this

theorem closedTrees_image_blockOf (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (hpl : (glueL σ LA).garden.IsPlain) (c : Fin m) {T : Finset (Fin (a c))}
    (hT : ClosedTrees (LA c).garden T) : ClosedTrees (glueL σ LA).garden (T.image fun i => σ ⟨c, i⟩) := by
  rw [closedTrees_iff _ hpl]
  rw [closedTrees_iff _ ((isPlain_glueN σ LA).1 hpl c)] at hT
  intro ℓ hℓ
  obtain ⟨⟨c', y⟩, rfl⟩ := (glueLeafN σ fun c => (LA c).garden.tree).surjective ℓ
  obtain ⟨i, hi, e⟩ := mem_image.1 hℓ
  have e' := σ.injective e
  simp only [Sigma.mk.injEq] at e'
  obtain ⟨rfl, e2⟩ := e'
  rw [show (glueL σ LA).garden.pair = (glueGardenN σ fun c => (LA c).garden).pair from rfl, glueN_pair_leaf]
  have hy : y.1.1 ∈ T := by rw [← eq_of_heq e2]; exact hi
  exact mem_image_of_mem _ (hT y hy)

/-- The component of a tree of a glue of irreducible plain pieces is its block. -/
theorem compOf_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (hpl : (glueL σ LA).garden.IsPlain) (hirr : ∀ c, (LA c).garden.Irreducible) (c : Fin m) (i : Fin (a c)) :
    compOf (glueL σ LA).garden (σ ⟨c, i⟩) = blockOf σ c := by
  apply le_antisymm (compOf_subset (closedTrees_blockOf σ LA hpl c) (by simp [mem_blockOf]))
  intro x hx
  obtain ⟨⟨c', j⟩, rfl⟩ := σ.surjective x
  rw [mem_blockOf, Equiv.symm_apply_apply] at hx
  dsimp only at hx
  subst hx
  have hpre := closedTrees_preBlock σ LA hpl c' (closedTrees_compOf hpl (σ ⟨c', i⟩))
  have hall : preBlock σ c' (compOf (glueL σ LA).garden (σ ⟨c', i⟩)) = univ := by
    by_contra hne
    refine hirr c' _ ⟨i, ?_⟩ hne hpre
    simp [preBlock, self_mem_compOf]
  have hmem : j ∈ preBlock σ c' (compOf (glueL σ LA).garden (σ ⟨c', i⟩)) := by
    rw [hall]; exact mem_univ _
  simpa [preBlock] using hmem

/-- Conversely, if each block is a component of the glue, the pieces are irreducible. -/
theorem irreducible_of_compOf (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (hpl : (glueL σ LA).garden.IsPlain)
    (hcomp : ∀ c i, compOf (glueL σ LA).garden (σ ⟨c, i⟩) = blockOf σ c) (c : Fin m) :
    (LA c).garden.Irreducible := by
  intro T hT hne hcl
  obtain ⟨i, hi⟩ := hT
  have h1 := compOf_subset (closedTrees_image_blockOf σ LA hpl c hcl) (mem_image_of_mem (fun i => σ ⟨c, i⟩) hi)
  rw [hcomp c i] at h1
  apply hne
  apply eq_univ_of_forall
  intro j
  have := h1 (by simp [blockOf] : σ ⟨c, j⟩ ∈ blockOf σ c)
  obtain ⟨j', hj', e⟩ := mem_image.1 this
  have e' := σ.injective e
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at e'
  rwa [← e']

end WaveTurbulence.Flower.CapsComp
