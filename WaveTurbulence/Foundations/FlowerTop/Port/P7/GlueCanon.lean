/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueCond
public import WaveTurbulence.Foundations.Canon.Basic
/-! FLOWER-P7: the canonicity criterion of a glued layered garden is the conjunction of the criteria of the
two parts (a cross pair of nodes cannot have completely paired leaves: a subtree has an odd number of
leaves). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {a b w : ℕ}

theorem mem_leavesBelow_glue_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GNode TA) (ℓ : GLeaf (gT σ TA TB)) :
    ℓ ∈ (glueNode σ TA TB (.inl x)).leavesBelow ↔ ∃ ℓ' ∈ x.leavesBelow, glueLeaf σ TA TB (.inl ℓ') = ℓ := by
  unfold GNode.leavesBelow
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨z, rfl⟩ := (glueLeaf σ TA TB).surjective ℓ
    rcases z with y | y
    · exact ⟨y, by rwa [glueLeaf_toNode_inl, glue_isDesc_inl] at h, rfl⟩
    · exfalso
      rw [glueLeaf_toNode_inr] at h
      exact not_glue_isDesc_inl_inr σ TA TB x y.toNode h
  · rintro ⟨ℓ', h, rfl⟩
    rwa [glueLeaf_toNode_inl, glue_isDesc_inl]

theorem mem_leavesBelow_glue_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GNode TB) (ℓ : GLeaf (gT σ TA TB)) :
    ℓ ∈ (glueNode σ TA TB (.inr x)).leavesBelow ↔ ∃ ℓ' ∈ x.leavesBelow, glueLeaf σ TA TB (.inr ℓ') = ℓ := by
  unfold GNode.leavesBelow
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨z, rfl⟩ := (glueLeaf σ TA TB).surjective ℓ
    rcases z with y | y
    · exfalso
      rw [glueLeaf_toNode_inl] at h
      exact not_glue_isDesc_inr_inl σ TA TB x y.toNode h
    · exact ⟨y, by rwa [glueLeaf_toNode_inr, glue_isDesc_inr] at h, rfl⟩
  · rintro ⟨ℓ', h, rfl⟩
    rwa [glueLeaf_toNode_inr, glue_isDesc_inr]

theorem leavesBelow_glue_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GNode TA) :
    (glueNode σ TA TB (.inl x)).leavesBelow = x.leavesBelow.image (fun ℓ => glueLeaf σ TA TB (.inl ℓ)) := by
  ext ℓ
  rw [mem_leavesBelow_glue_inl, Finset.mem_image]

theorem leavesBelow_glue_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GNode TB) :
    (glueNode σ TA TB (.inr x)).leavesBelow = x.leavesBelow.image (fun ℓ => glueLeaf σ TA TB (.inr ℓ)) := by
  ext ℓ
  rw [mem_leavesBelow_glue_inr, Finset.mem_image]

/-- Complete pairing of a set of leaves of the first part. -/
theorem completelyPaired_glue_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b)
    (S : Finset (GLeaf GA.tree)) :
    (glueGarden σ GA GB).CompletelyPaired (S.image fun ℓ => glueLeaf σ GA.tree GB.tree (.inl ℓ)) ↔
      GA.CompletelyPaired S := by
  unfold Garden.CompletelyPaired
  constructor
  · intro h ℓ hℓ
    obtain ⟨h1, h2⟩ := h (glueLeaf σ GA.tree GB.tree (.inl ℓ)) (Finset.mem_image_of_mem _ hℓ)
    rw [glue_pair_leaf_inl] at h1 h2
    refine ⟨fun e => h1 (by rw [e]), ?_⟩
    obtain ⟨ℓ'', hℓ'', e⟩ := Finset.mem_image.1 h2
    rwa [Sum.inl_injective ((glueLeaf σ GA.tree GB.tree).injective e)] at hℓ''
  · intro h x hx
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨h1, h2⟩ := h ℓ hℓ
    rw [glue_pair_leaf_inl]
    exact ⟨fun e => h1 (Sum.inl_injective ((glueLeaf σ GA.tree GB.tree).injective e)),
      Finset.mem_image_of_mem _ h2⟩

theorem completelyPaired_glue_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b)
    (S : Finset (GLeaf GB.tree)) :
    (glueGarden σ GA GB).CompletelyPaired (S.image fun ℓ => glueLeaf σ GA.tree GB.tree (.inr ℓ)) ↔
      GB.CompletelyPaired S := by
  unfold Garden.CompletelyPaired
  constructor
  · intro h ℓ hℓ
    obtain ⟨h1, h2⟩ := h (glueLeaf σ GA.tree GB.tree (.inr ℓ)) (Finset.mem_image_of_mem _ hℓ)
    rw [glue_pair_leaf_inr] at h1 h2
    refine ⟨fun e => h1 (by rw [e]), ?_⟩
    obtain ⟨ℓ'', hℓ'', e⟩ := Finset.mem_image.1 h2
    rwa [Sum.inr_injective ((glueLeaf σ GA.tree GB.tree).injective e)] at hℓ''
  · intro h x hx
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨h1, h2⟩ := h ℓ hℓ
    rw [glue_pair_leaf_inr]
    exact ⟨fun e => h1 (Sum.inr_injective ((glueLeaf σ GA.tree GB.tree).injective e)),
      Finset.mem_image_of_mem _ h2⟩

/-- A cross pair cannot be completely paired: the leaves below the first node are paired among themselves,
but there is an odd number of them. -/
theorem not_cp_cross (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (x : GNode GA.tree)
    (x' : GNode GB.tree) :
    ¬ (glueGarden σ GA GB).CompletelyPaired
      ((glueNode σ GA.tree GB.tree (.inl x)).leavesBelow ∪ (glueNode σ GA.tree GB.tree (.inr x')).leavesBelow) := by
  intro h
  rw [leavesBelow_glue_inl, leavesBelow_glue_inr] at h
  have hA : GA.CompletelyPaired x.leavesBelow := by
    intro ℓ hℓ
    have := h (glueLeaf σ GA.tree GB.tree (.inl ℓ)) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hℓ))
    obtain ⟨h1, h2⟩ := this
    rw [glue_pair_leaf_inl] at h1 h2
    refine ⟨fun e => h1 (by rw [e]), ?_⟩
    rcases Finset.mem_union.1 h2 with h3 | h3
    · obtain ⟨ℓ'', hℓ'', e⟩ := Finset.mem_image.1 h3
      rwa [Sum.inl_injective ((glueLeaf σ GA.tree GB.tree).injective e)] at hℓ''
    · obtain ⟨ℓ'', _, e⟩ := Finset.mem_image.1 h3
      exact absurd ((glueLeaf σ GA.tree GB.tree).injective e) (by simp)
  have he := Canon.even_card_of_completelyPaired GA x.leavesBelow.card x.leavesBelow rfl hA
  exact (Nat.not_even_iff_odd.2 (Canon.odd_card_leavesBelow x)) he

theorem glue_incomparable_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x x' : GNode TA) :
    (glueNode σ TA TB (.inl x)).Incomparable (glueNode σ TA TB (.inl x')) ↔ x.Incomparable x' := by
  unfold GNode.Incomparable
  rw [glue_isDesc_inl, glue_isDesc_inl]

theorem glue_incomparable_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x x' : GNode TB) :
    (glueNode σ TA TB (.inr x)).Incomparable (glueNode σ TA TB (.inr x')) ↔ x.Incomparable x' := by
  unfold GNode.Incomparable
  rw [glue_isDesc_inr, glue_isDesc_inr]

theorem gLayer_dropLast_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b)
    (lA : GNode GA.tree → ℕ) (lB : GNode GB.tree → ℕ) (c : Fin a) (q : Path)
    (hmem : (σ (.inl c), q.dropLast).2 ∈ ((glueGarden σ GA GB).tree (σ (.inl c))).nodes)
    (hmem' : (c, q.dropLast).2 ∈ (GA.tree c).nodes) :
    gLayer σ GA GB lA lB ⟨(σ (.inl c), q.dropLast), hmem⟩ = lA ⟨(c, q.dropLast), hmem'⟩ := by
  have : (⟨(σ (.inl c), q.dropLast), hmem⟩ : GNode (glueGarden σ GA GB).tree) =
      glueNode σ GA.tree GB.tree (.inl ⟨(c, q.dropLast), hmem'⟩) := rfl
  rw [this]
  exact gLayer_inl σ GA GB lA lB _

theorem gLayer_dropLast_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b)
    (lA : GNode GA.tree → ℕ) (lB : GNode GB.tree → ℕ) (c : Fin b) (q : Path)
    (hmem : (σ (.inr c), q.dropLast).2 ∈ ((glueGarden σ GA GB).tree (σ (.inr c))).nodes)
    (hmem' : (c, q.dropLast).2 ∈ (GB.tree c).nodes) :
    gLayer σ GA GB lA lB ⟨(σ (.inr c), q.dropLast), hmem⟩ = lB ⟨(c, q.dropLast), hmem'⟩ := by
  have : (⟨(σ (.inr c), q.dropLast), hmem⟩ : GNode (glueGarden σ GA GB).tree) =
      glueNode σ GA.tree GB.tree (.inr ⟨(c, q.dropLast), hmem'⟩) := rfl
  rw [this]
  exact gLayer_inr σ GA GB lA lB _

theorem parentLayer_glue_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (p : ℕ) (x : GNode LA.garden.tree) :
    (glueLayered σ LA LB).parentLayer p (glueNode σ LA.garden.tree LB.garden.tree (.inl x)) =
      LA.parentLayer p x := by
  unfold LayeredGarden.parentLayer
  by_cases h : x.1.2 = []
  · simp [glueNode_inl, h]
  · simp only [glueNode_inl, h, ite_false]
    obtain ⟨⟨c, q⟩, hc⟩ := x
    exact gLayer_dropLast_inl σ LA.garden LB.garden LA.layer LB.layer c q _ _

theorem parentLayer_glue_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (p : ℕ) (x : GNode LB.garden.tree) :
    (glueLayered σ LA LB).parentLayer p (glueNode σ LA.garden.tree LB.garden.tree (.inr x)) =
      LB.parentLayer p x := by
  unfold LayeredGarden.parentLayer
  by_cases h : x.1.2 = []
  · simp [glueNode_inr, h]
  · simp only [glueNode_inr, h, ite_false]
    obtain ⟨⟨c, q⟩, hc⟩ := x
    exact gLayer_dropLast_inr σ LA.garden LB.garden LA.layer LB.layer c q _ _

/-- **The canonicity criterion of a glued garden.** -/
theorem glue_canonCriterion_iff (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (p : ℕ) :
    (glueLayered σ LA LB).CanonCriterion p ↔ LA.CanonCriterion p ∧ LB.CanonCriterion p := by
  unfold LayeredGarden.CanonCriterion
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨⟨fun x => ?_, fun x x' hinc hcp => ?_⟩, ⟨fun x => ?_, fun x x' hinc hcp => ?_⟩⟩
    · have := hl (glueNode σ LA.garden.tree LB.garden.tree (.inl x))
      rwa [glueLayered_layer_inl] at this
    · have h1 := h (glueNode σ LA.garden.tree LB.garden.tree (.inl x))
        (glueNode σ LA.garden.tree LB.garden.tree (.inl x')) ((glue_incomparable_inl σ _ _ x x').2 hinc) (by
          rw [leavesBelow_glue_inl, leavesBelow_glue_inl, ← Finset.image_union]
          exact (completelyPaired_glue_inl σ LA.garden LB.garden _).2 hcp)
      rwa [parentLayer_glue_inl, parentLayer_glue_inl, glueLayered_layer_inl, glueLayered_layer_inl] at h1
    · have := hl (glueNode σ LA.garden.tree LB.garden.tree (.inr x))
      rwa [glueLayered_layer_inr] at this
    · have h1 := h (glueNode σ LA.garden.tree LB.garden.tree (.inr x))
        (glueNode σ LA.garden.tree LB.garden.tree (.inr x')) ((glue_incomparable_inr σ _ _ x x').2 hinc) (by
          rw [leavesBelow_glue_inr, leavesBelow_glue_inr, ← Finset.image_union]
          exact (completelyPaired_glue_inr σ LA.garden LB.garden _).2 hcp)
      rwa [parentLayer_glue_inr, parentLayer_glue_inr, glueLayered_layer_inr, glueLayered_layer_inr] at h1
  · rintro ⟨⟨hA, hA2⟩, ⟨hB, hB2⟩⟩
    refine ⟨fun x => ?_, fun x x' hinc hcp => ?_⟩
    · obtain ⟨y, rfl⟩ := (glueNode σ LA.garden.tree LB.garden.tree).surjective x
      rcases y with y | y
      · rw [glueLayered_layer_inl]; exact hA y
      · rw [glueLayered_layer_inr]; exact hB y
    · obtain ⟨y, rfl⟩ := (glueNode σ LA.garden.tree LB.garden.tree).surjective x
      obtain ⟨y', rfl⟩ := (glueNode σ LA.garden.tree LB.garden.tree).surjective x'
      rcases y with y | y <;> rcases y' with y' | y'
      · rw [parentLayer_glue_inl, parentLayer_glue_inl, glueLayered_layer_inl, glueLayered_layer_inl]
        refine hA2 y y' ((glue_incomparable_inl σ _ _ y y').1 hinc) ?_
        rw [leavesBelow_glue_inl, leavesBelow_glue_inl, ← Finset.image_union] at hcp
        exact (completelyPaired_glue_inl σ LA.garden LB.garden _).1 hcp
      · exact absurd hcp (not_cp_cross σ LA.garden LB.garden y y')
      · rw [Finset.union_comm] at hcp
        exact absurd hcp (not_cp_cross σ LA.garden LB.garden y' y)
      · rw [parentLayer_glue_inr, parentLayer_glue_inr, glueLayered_layer_inr, glueLayered_layer_inr]
        refine hB2 y y' ((glue_incomparable_inr σ _ _ y y').1 hinc) ?_
        rw [leavesBelow_glue_inr, leavesBelow_glue_inr, ← Finset.image_union] at hcp
        exact (completelyPaired_glue_inr σ LA.garden LB.garden _).1 hcp

end WaveTurbulence.FlowerP7
