/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueCanon
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Closed
/-! FLOWER-P7: closed sets of trees and minimal components of a glued garden. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {a b w : ℕ}

theorem leavesOf_glue_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (T : Finset (Fin a)) :
    (glueGarden σ GA GB).leavesOf (T.image fun i => σ (.inl i)) =
      (GA.leavesOf T).image fun ℓ => glueLeaf σ GA.tree GB.tree (.inl ℓ) := by
  ext ℓ
  rw [mem_leavesOf, Finset.mem_image]
  simp only [Finset.mem_image, mem_leavesOf]
  constructor
  · rintro ⟨i, hi, h⟩
    obtain ⟨z, rfl⟩ := (glueLeaf σ GA.tree GB.tree).surjective ℓ
    rcases z with y | y
    · refine ⟨y, ?_, rfl⟩
      have : σ (.inl i) = σ (.inl y.1.1) := by simpa using h
      rw [← Sum.inl_injective (σ.injective this)]; exact hi
    · exfalso
      have : σ (.inl i) = σ (.inr y.1.1) := by simpa using h
      exact absurd (σ.injective this) (by simp)
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1.1, hy, by simp⟩

theorem leavesOf_glue_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (T : Finset (Fin b)) :
    (glueGarden σ GA GB).leavesOf (T.image fun i => σ (.inr i)) =
      (GB.leavesOf T).image fun ℓ => glueLeaf σ GA.tree GB.tree (.inr ℓ) := by
  ext ℓ
  rw [mem_leavesOf, Finset.mem_image]
  simp only [Finset.mem_image, mem_leavesOf]
  constructor
  · rintro ⟨i, hi, h⟩
    obtain ⟨z, rfl⟩ := (glueLeaf σ GA.tree GB.tree).surjective ℓ
    rcases z with y | y
    · exfalso
      have : σ (.inr i) = σ (.inl y.1.1) := by simpa using h
      exact absurd (σ.injective this) (by simp)
    · refine ⟨y, ?_, rfl⟩
      have : σ (.inr i) = σ (.inr y.1.1) := by simpa using h
      rw [← Sum.inr_injective (σ.injective this)]; exact hi
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1.1, hy, by simp⟩

theorem glue_closed_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (T : Finset (Fin a)) :
    ClosedTrees (glueGarden σ GA GB) (T.image fun i => σ (.inl i)) ↔ ClosedTrees GA T := by
  unfold ClosedTrees
  rw [leavesOf_glue_inl]
  exact completelyPaired_glue_inl σ GA GB _

theorem glue_closed_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (T : Finset (Fin b)) :
    ClosedTrees (glueGarden σ GA GB) (T.image fun i => σ (.inr i)) ↔ ClosedTrees GB T := by
  unfold ClosedTrees
  rw [leavesOf_glue_inr]
  exact completelyPaired_glue_inr σ GA GB _

/-- `G` has no closed proper set of trees containing `i₀`. -/
def IrrAt {w : ℕ} (G : Garden w) (i₀ : Fin w) : Prop :=
  ∀ T : Finset (Fin w), ClosedTrees G T → i₀ ∈ T → T = Finset.univ

theorem irreducible_iff_irrAt {w : ℕ} (G : Garden w) (hG : G.IsPlain) (i₀ : Fin w) :
    G.Irreducible ↔ IrrAt G i₀ := by
  constructor
  · intro h T hT hi
    by_contra hne
    exact h T ⟨i₀, hi⟩ hne hT
  · intro h T hne hTu hT
    by_cases hi : i₀ ∈ T
    · exact hTu (h T hT hi)
    · have hc : i₀ ∈ Tᶜ := by simpa using hi
      have := h Tᶜ (closedTrees_compl G hG hT) hc
      obtain ⟨j, hj⟩ := hne
      have : j ∈ Tᶜ := by rw [this]; exact Finset.mem_univ _
      exact absurd hj (by simpa using this)

theorem glue_minimalAt_inl_iff (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (hA : GA.IsPlain)
    (i₀ : Fin a) :
    MinimalAt (glueGarden σ GA GB) (σ (.inl i₀)) (Finset.univ.image fun i => σ (.inl i)) ↔ IrrAt GA i₀ := by
  classical
  constructor
  · rintro ⟨-, -, hmin⟩ T hT hi
    have h := hmin (T.image fun i => σ (.inl i)) ((glue_closed_inl σ GA GB T).2 hT)
      (Finset.mem_image.2 ⟨i₀, hi, rfl⟩) (Finset.image_subset_image (Finset.subset_univ _))
    ext i
    simp only [Finset.mem_univ, iff_true]
    have : σ (.inl i) ∈ (Finset.univ.image fun i => σ (.inl i)) := Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
    rw [← h] at this
    obtain ⟨j, hj, e⟩ := Finset.mem_image.1 this
    rwa [← Sum.inl_injective (σ.injective e)]
  · intro h
    refine ⟨Finset.mem_image.2 ⟨i₀, Finset.mem_univ _, rfl⟩, ?_, ?_⟩
    · exact (glue_closed_inl σ GA GB Finset.univ).2 (closedTrees_univ GA hA)
    · intro T hT hs hsub
      let T0 : Finset (Fin a) := Finset.univ.filter fun i => σ (.inl i) ∈ T
      have hT0 : T = T0.image fun i => σ (.inl i) := by
        ext x
        constructor
        · intro hx
          obtain ⟨y, hy, e⟩ := Finset.mem_image.1 (hsub hx)
          exact Finset.mem_image.2 ⟨y, by simp [T0, e, hx], e⟩
        · intro hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
          simpa [T0] using hy
      rw [hT0] at hT
      have hc := (glue_closed_inl σ GA GB T0).1 hT
      have hi : i₀ ∈ T0 := by simpa [T0] using hs
      have := h T0 hc hi
      rw [hT0, this]

end WaveTurbulence.FlowerP7
