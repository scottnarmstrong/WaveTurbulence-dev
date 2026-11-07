/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueLayered
/-! FLOWER-P7: decorations of a glued garden are pairs of decorations. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {a b w d : ℕ}

theorem glueNode_root_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree) (i : Fin a) :
    glueNode σ TA TB (.inl (GNode.root TA i)) = GNode.root (gT σ TA TB) (σ (.inl i)) := rfl

theorem glueNode_root_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree) (i : Fin b) :
    glueNode σ TA TB (.inr (GNode.root TB i)) = GNode.root (gT σ TA TB) (σ (.inr i)) := rfl

/-- The glued root labels. -/
def gRoot (σ : Fin a ⊕ Fin b ≃ Fin w) (nA : Fin a → (Fin d → ℤ)) (nB : Fin b → (Fin d → ℤ)) :
    Fin w → (Fin d → ℤ) := fun c => Sum.elim nA nB (σ.symm c)

/-- Glued labelling. -/
noncomputable def gLabel (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b)
    (κA : GNode GA.tree → (Fin d → ℤ)) (κB : GNode GB.tree → (Fin d → ℤ)) :
    GNode (glueGarden σ GA GB).tree → (Fin d → ℤ) :=
  fun x => Sum.elim κA κB ((glueNode σ GA.tree GB.tree).symm x)

@[simp] theorem gLabel_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b)
    (κA : GNode GA.tree → (Fin d → ℤ)) (κB : GNode GB.tree → (Fin d → ℤ)) (x : GNode GA.tree) :
    gLabel σ GA GB κA κB (glueNode σ GA.tree GB.tree (.inl x)) = κA x := by simp [gLabel]

@[simp] theorem gLabel_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b)
    (κA : GNode GA.tree → (Fin d → ℤ)) (κB : GNode GB.tree → (Fin d → ℤ)) (x : GNode GB.tree) :
    gLabel σ GA GB κA κB (glueNode σ GA.tree GB.tree (.inr x)) = κB x := by simp [gLabel]

theorem glue_isDecoration_iff (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b)
    (κ : GNode (glueGarden σ GA GB).tree → (Fin d → ℤ)) :
    IsDecoration (glueGarden σ GA GB) κ ↔
      IsDecoration GA (fun x => κ (glueNode σ GA.tree GB.tree (.inl x))) ∧
      IsDecoration GB (fun x => κ (glueNode σ GA.tree GB.tree (.inr x))) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun br => ?_, fun ℓ => ?_⟩, ⟨fun br => ?_, fun ℓ => ?_⟩⟩
    · have := h1 (glueBranch σ GA.tree GB.tree (.inl br))
      rw [glueBranch_toNode_inl, glueBranch_child_inl, glueBranch_child_inl, glueBranch_child_inl] at this
      exact this
    · have := h2 (glueLeaf σ GA.tree GB.tree (.inl ℓ))
      rw [glueLeaf_toNode_inl, glue_pair_leaf_inl, glueLeaf_toNode_inl] at this
      exact this
    · have := h1 (glueBranch σ GA.tree GB.tree (.inr br))
      rw [glueBranch_toNode_inr, glueBranch_child_inr, glueBranch_child_inr, glueBranch_child_inr] at this
      exact this
    · have := h2 (glueLeaf σ GA.tree GB.tree (.inr ℓ))
      rw [glueLeaf_toNode_inr, glue_pair_leaf_inr, glueLeaf_toNode_inr] at this
      exact this
  · rintro ⟨⟨hA1, hA2⟩, ⟨hB1, hB2⟩⟩
    refine ⟨fun br => ?_, fun ℓ => ?_⟩
    · obtain ⟨y, rfl⟩ := (glueBranch σ GA.tree GB.tree).surjective br
      rcases y with y | y
      · rw [glueBranch_toNode_inl, glueBranch_child_inl, glueBranch_child_inl, glueBranch_child_inl]
        exact hA1 y
      · rw [glueBranch_toNode_inr, glueBranch_child_inr, glueBranch_child_inr, glueBranch_child_inr]
        exact hB1 y
    · obtain ⟨y, rfl⟩ := (glueLeaf σ GA.tree GB.tree).surjective ℓ
      rcases y with y | y
      · rw [glueLeaf_toNode_inl, glue_pair_leaf_inl, glueLeaf_toNode_inl]
        exact hA2 y
      · rw [glueLeaf_toNode_inr, glue_pair_leaf_inr, glueLeaf_toNode_inr]
        exact hB2 y

/-- Decorations of the glued garden are pairs of decorations. -/
noncomputable def glueDecEquiv (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b)
    (nA : Fin a → (Fin d → ℤ)) (nB : Fin b → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    GenDecoration (glueGarden σ GA GB) d (gRoot σ nA nB) nfl ≃
      GenDecoration GA d nA nfl × GenDecoration GB d nB nfl where
  toFun κ := (⟨fun x => κ.1 (glueNode σ GA.tree GB.tree (.inl x)),
      ((glue_isDecoration_iff σ GA GB κ.1).1 κ.2.1).1,
      fun j => by
        have := κ.2.2.1 (σ (.inl j))
        rw [← glueNode_root_inl] at this
        simpa [gRoot] using this,
      fun ℓ hℓ => by
        have := κ.2.2.2 (glueLeaf σ GA.tree GB.tree (.inl ℓ)) (by
          unfold Garden.IsFlower at hℓ ⊢
          rw [glue_mark_leaf_inl]; exact hℓ)
        rwa [glueLeaf_toNode_inl] at this⟩,
    ⟨fun x => κ.1 (glueNode σ GA.tree GB.tree (.inr x)),
      ((glue_isDecoration_iff σ GA GB κ.1).1 κ.2.1).2,
      fun j => by
        have := κ.2.2.1 (σ (.inr j))
        rw [← glueNode_root_inr] at this
        simpa [gRoot] using this,
      fun ℓ hℓ => by
        have := κ.2.2.2 (glueLeaf σ GA.tree GB.tree (.inr ℓ)) (by
          unfold Garden.IsFlower at hℓ ⊢
          rw [glue_mark_leaf_inr]; exact hℓ)
        rwa [glueLeaf_toNode_inr] at this⟩)
  invFun κ := ⟨gLabel σ GA GB κ.1.1 κ.2.1, by
      rw [glue_isDecoration_iff]
      refine ⟨?_, ?_⟩
      · simpa using κ.1.2.1
      · simpa using κ.2.2.1, by
      intro c
      obtain ⟨s, rfl⟩ := σ.surjective c
      rcases s with j | j
      · rw [← glueNode_root_inl, gLabel_inl]
        simpa [gRoot] using κ.1.2.2.1 j
      · rw [← glueNode_root_inr, gLabel_inr]
        simpa [gRoot] using κ.2.2.2.1 j, by
      intro ℓ hℓ
      obtain ⟨y, rfl⟩ := (glueLeaf σ GA.tree GB.tree).surjective ℓ
      rcases y with y | y
      · rw [glueLeaf_toNode_inl, gLabel_inl]
        apply κ.1.2.2.2 y
        unfold Garden.IsFlower at hℓ ⊢
        rwa [glue_mark_leaf_inl] at hℓ
      · rw [glueLeaf_toNode_inr, gLabel_inr]
        apply κ.2.2.2.2 y
        unfold Garden.IsFlower at hℓ ⊢
        rwa [glue_mark_leaf_inr] at hℓ⟩
  left_inv κ := by
    apply Subtype.ext
    funext x
    obtain ⟨y, rfl⟩ := (glueNode σ GA.tree GB.tree).surjective x
    rcases y with y | y <;> simp
  right_inv κ := by
    apply Prod.ext
    · apply Subtype.ext; funext x; simp
    · apply Subtype.ext; funext x; simp

end WaveTurbulence.FlowerP7
