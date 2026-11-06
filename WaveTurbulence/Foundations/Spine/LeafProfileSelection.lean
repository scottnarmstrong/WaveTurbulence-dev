/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseKernel
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
/-! Actual leaf subsets select individual source profiles in the remainder expansion. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset
open scoped Classical

noncomputable def selectLeafProfiles {w d : ℕ} (G : Garden w) (S : Finset (GLeaf G.tree))
    (H₀ H₁ : LeafProfiles w d) : LeafProfiles w d := fun a x =>
  if a ∈ S.image (fun l => l.1) then H₁ a x else H₀ a x

 theorem selectLeafProfiles_apply {w d : ℕ} (G : Garden w) (S : Finset (GLeaf G.tree))
    (H₀ H₁ : LeafProfiles w d) (l : GLeaf G.tree) (x : Mom d) :
    selectLeafProfiles G S H₀ H₁ l.1 x = if l ∈ S then H₁ l.1 x else H₀ l.1 x := by
  have hm : l.1 ∈ S.image (fun l => l.1) ↔ l ∈ S := by
    constructor
    · intro h
      obtain ⟨a, ha, he⟩ := mem_image.mp h
      exact (Subtype.ext he : a = l) ▸ ha
    · intro h
      exact mem_image.mpr ⟨l, h, rfl⟩
  simp only [selectLeafProfiles, hm]

/-- Expand the original input product, retaining the actual identity of every leaf. -/
theorem leaf_product_add_eq_sum_subsets {w d : ℕ} (G : Garden w)
    (H₀ H₁ : LeafProfiles w d) (k : GLeaf G.tree → Mom d) :
    (∏ l ∈ inputLeaves G, ((H₀ l.1 (k l) + H₁ l.1 (k l) : ℝ) : ℂ)) =
      ∑ S ∈ (inputLeaves G).powerset,
        ∏ l ∈ inputLeaves G, (selectLeafProfiles G S H₀ H₁ l.1 (k l) : ℂ) := by
  simp_rw [Complex.ofReal_add]
  rw [Finset.prod_add (fun l => (H₀ l.1 (k l) : ℂ)) (fun l => (H₁ l.1 (k l) : ℂ))]
  -- Reindex by the complementary selected remainder leaves.
  have hsum : (∑ S ∈ (inputLeaves G).powerset,
      (∏ l ∈ S, (H₀ l.1 (k l) : ℂ)) * ∏ l ∈ inputLeaves G \ S, (H₁ l.1 (k l) : ℂ)) =
      ∑ S ∈ (inputLeaves G).powerset,
      (∏ l ∈ S, (H₁ l.1 (k l) : ℂ)) * ∏ l ∈ inputLeaves G \ S, (H₀ l.1 (k l) : ℂ) := by
    rw [← Finset.prod_add, ← Finset.prod_add]
    apply prod_congr rfl
    intro l _
    exact add_comm _ _
  rw [hsum]
  apply sum_congr rfl
  intro S hS
  have hSI := mem_powerset.mp hS
  simp_rw [selectLeafProfiles_apply]
  simp_rw [apply_ite Complex.ofReal]
  rw [Finset.prod_ite]
  have hs : (inputLeaves G).filter (fun l => l ∈ S) = S := by
    ext l
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hSI h, h⟩⟩
  have hc : (inputLeaves G).filter (fun l => l ∉ S) = inputLeaves G \ S := by
    ext l
    simp only [mem_filter, mem_sdiff]
  rw [hs, hc]

end WaveTurbulence.LGSpine
