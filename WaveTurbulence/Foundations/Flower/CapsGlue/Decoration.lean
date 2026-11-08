/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsGlue.Garden
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueDecoration
/-! # A3a CAPS-GLUE: decorations of an n-ary glued garden are families of decorations -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.CapsGlue
open TTree Finset WaveTurbulence.FlowerP7

variable {m w d : ℕ} {a : Fin m → ℕ}

theorem glueNodeN_root (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) (c : Fin m)
    (i : Fin (a c)) : glueNodeN σ TA ⟨c, GNode.root (TA c) i⟩ = GNode.root (gT σ TA) (σ ⟨c, i⟩) := rfl

/-- The glued root labels. -/
def gRootN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (nA : ∀ c, Fin (a c) → (Fin d → ℤ)) :
    Fin w → (Fin d → ℤ) := fun x => nA (σ.symm x).1 (σ.symm x).2

@[simp] theorem gRootN_apply (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (nA : ∀ c, Fin (a c) → (Fin d → ℤ))
    (c : Fin m) (i : Fin (a c)) : gRootN σ nA (σ ⟨c, i⟩) = nA c i := by
  unfold gRootN
  rw [Equiv.symm_apply_apply]

/-- Glued labelling. -/
noncomputable def gLabelN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c))
    (κ : ∀ c, GNode (GA c).tree → (Fin d → ℤ)) : GNode (glueGardenN σ GA).tree → (Fin d → ℤ) :=
  fun x => κ ((glueNodeN σ fun c => (GA c).tree).symm x).1 ((glueNodeN σ fun c => (GA c).tree).symm x).2

@[simp] theorem gLabelN_apply (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c))
    (κ : ∀ c, GNode (GA c).tree → (Fin d → ℤ)) (c : Fin m) (x : GNode (GA c).tree) :
    gLabelN σ GA κ (glueNodeN σ (fun c => (GA c).tree) ⟨c, x⟩) = κ c x := by
  unfold gLabelN
  rw [Equiv.symm_apply_apply]

theorem glueN_isDecoration_iff (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c))
    (κ : GNode (glueGardenN σ GA).tree → (Fin d → ℤ)) :
    IsDecoration (glueGardenN σ GA) κ ↔
      ∀ c, IsDecoration (GA c) (fun x => κ (glueNodeN σ (fun c => (GA c).tree) ⟨c, x⟩)) := by
  constructor
  · rintro ⟨h1, h2⟩ c
    refine ⟨fun br => ?_, fun ℓ => ?_⟩
    · have := h1 (glueBranchN σ (fun c => (GA c).tree) ⟨c, br⟩)
      rw [glueBranchN_toNode, glueBranchN_child, glueBranchN_child, glueBranchN_child] at this
      exact this
    · have := h2 (glueLeafN σ (fun c => (GA c).tree) ⟨c, ℓ⟩)
      rw [glueLeafN_toNode, glueN_pair_leaf, glueLeafN_toNode] at this
      exact this
  · intro h
    refine ⟨fun br => ?_, fun ℓ => ?_⟩
    · obtain ⟨⟨c, y⟩, rfl⟩ := (glueBranchN σ fun c => (GA c).tree).surjective br
      rw [glueBranchN_toNode, glueBranchN_child, glueBranchN_child, glueBranchN_child]
      exact (h c).1 y
    · obtain ⟨⟨c, y⟩, rfl⟩ := (glueLeafN σ fun c => (GA c).tree).surjective ℓ
      rw [glueLeafN_toNode, glueN_pair_leaf, glueLeafN_toNode]
      exact (h c).2 y

/-- Decorations of the glued garden are families of decorations. -/
noncomputable def glueDecEquivN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c))
    (nA : ∀ c, Fin (a c) → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    GenDecoration (glueGardenN σ GA) d (gRootN σ nA) nfl ≃ ∀ c, GenDecoration (GA c) d (nA c) nfl where
  toFun κ c := ⟨fun x => κ.1 (glueNodeN σ (fun c => (GA c).tree) ⟨c, x⟩),
      ((glueN_isDecoration_iff σ GA κ.1).1 κ.2.1) c,
      fun j => by
        have := κ.2.2.1 (σ ⟨c, j⟩)
        rw [← glueNodeN_root] at this
        simpa using this,
      fun ℓ hℓ => by
        have := κ.2.2.2 (glueLeafN σ (fun c => (GA c).tree) ⟨c, ℓ⟩) (by
          unfold Garden.IsFlower at hℓ ⊢
          rw [glueN_mark_leaf]; exact hℓ)
        rwa [glueLeafN_toNode] at this⟩
  invFun κ := ⟨gLabelN σ GA fun c => (κ c).1, by
      rw [glueN_isDecoration_iff]
      intro c
      simpa using (κ c).2.1, by
      intro x
      obtain ⟨⟨c, j⟩, rfl⟩ := σ.surjective x
      rw [← glueNodeN_root, gLabelN_apply]
      simpa using (κ c).2.2.1 j, by
      intro ℓ hℓ
      obtain ⟨⟨c, y⟩, rfl⟩ := (glueLeafN σ fun c => (GA c).tree).surjective ℓ
      rw [glueLeafN_toNode, gLabelN_apply]
      apply (κ c).2.2.2 y
      unfold Garden.IsFlower at hℓ ⊢
      rwa [glueN_mark_leaf] at hℓ⟩
  left_inv κ := by
    apply Subtype.ext
    funext x
    obtain ⟨⟨c, y⟩, rfl⟩ := (glueNodeN σ fun c => (GA c).tree).surjective x
    simp
  right_inv κ := by
    funext c
    apply Subtype.ext
    funext x
    simp

end WaveTurbulence.Flower.CapsGlue
