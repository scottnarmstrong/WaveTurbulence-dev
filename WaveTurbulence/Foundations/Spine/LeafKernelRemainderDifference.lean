/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafKernelRemainderExpansion
/-! The difference from the zero-remainder kernel contains a genuine remainder leaf in every term. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

 theorem selectLeafProfiles_empty {w d : ℕ} (G : Garden w) (H₀ H₁ : LeafProfiles w d) :
    selectLeafProfiles G ∅ H₀ H₁ = H₀ := by
  classical
  funext a x
  simp [selectLeafProfiles]

/-- Removing the empty subset identifies exactly the terms with at least one R input. -/
theorem kernelLeaves_sub_eq_sum_nonempty_subsets {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H₀ H₁ : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (hF₀ : ∀ l ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |H₀ l.1 (k₀ + latticePoint L n)|)
    (hF₁ : ∀ l ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |H₁ l.1 (k₀ + latticePoint L n)|) :
    kernelLeaves L γ δ LG (fun a x => H₀ a x + H₁ a x) up s k₀ nroot nfl -
      kernelLeaves L γ δ LG H₀ up s k₀ nroot nfl =
      ∑ S ∈ (inputLeaves LG.garden).powerset.erase ∅,
        kernelLeaves L γ δ LG (selectLeafProfiles LG.garden S H₀ H₁) up s k₀ nroot nfl := by
  classical
  rw [kernelLeaves_add_eq_sum_subsets L γ δ LG H₀ H₁ up s k₀ nroot nfl hlone hF₀ hF₁]
  have he := Finset.sum_erase_add ((inputLeaves LG.garden).powerset)
    (fun S => kernelLeaves L γ δ LG (selectLeafProfiles LG.garden S H₀ H₁) up s k₀ nroot nfl)
    (by simp : ∅ ∈ (inputLeaves LG.garden).powerset)
  rw [selectLeafProfiles_empty] at he
  rw [← he, add_sub_cancel_right]

end WaveTurbulence.LGSpine
