/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafSelectionBounds
/-! Leaf selection preserves the original finite regularity and relative spatial bounds. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

 theorem selectLeafProfiles_at_leaf {w d : ℕ} (G : Garden w) (S : Finset (GLeaf G.tree))
    (H₀ H₁ : LeafProfiles w d) (l : GLeaf G.tree) :
    selectLeafProfiles G S H₀ H₁ l.1 = if l ∈ S then H₁ l.1 else H₀ l.1 := by
  classical
  by_cases hs : l ∈ S <;> funext x <;> simp [selectLeafProfiles_apply, hs]

 theorem contDiff_selected_profile {w d N : ℕ} (G : Garden w) (S : Finset (GLeaf G.tree))
    (H₀ H₁ : LeafProfiles w d) (l : GLeaf G.tree)
    (h₀ : ContDiff ℝ N (H₀ l.1)) (h₁ : ContDiff ℝ N (H₁ l.1)) :
    ContDiff ℝ N (selectLeafProfiles G S H₀ H₁ l.1) := by
  classical
  rw [selectLeafProfiles_at_leaf]
  split_ifs
  · exact h₁
  · exact h₀

 theorem SNormR_selected_relative_le {w d N W : ℕ} (G : Garden w) (S : Finset (GLeaf G.tree))
    (H₀ H₁ : LeafProfiles w d) (B₀ B₁ : (Fin w × TTree.Path) → NNReal)
    (C : ℝ) (l : GLeaf G.tree)
    (h₀ : SNormR N W (H₀ l.1) ≤ ENNReal.ofReal (C * B₀ l.1))
    (h₁ : SNormR N W (H₁ l.1) ≤ ENNReal.ofReal (C * B₁ l.1)) :
    SNormR N W (selectLeafProfiles G S H₀ H₁ l.1) ≤
      ENNReal.ofReal (C * selectLeafBounds G S B₀ B₁ l.1) := by
  classical
  rw [selectLeafProfiles_at_leaf, selectLeafBounds_apply]
  split_ifs
  · exact h₁
  · exact h₀

end WaveTurbulence.LGSpine
