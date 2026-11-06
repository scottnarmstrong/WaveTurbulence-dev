/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafProfileSelection
public import WaveTurbulence.Foundations.Spine.WeightedLeafKernel
/-! Expand phi+R in the literal kernel without changing its decoration sum or oscillatory phase. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem kernelLeaves_add_eq_sum_subsets {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H₀ H₁ : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (hF₀ : ∀ l ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |H₀ l.1 (k₀ + latticePoint L n)|)
    (hF₁ : ∀ l ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |H₁ l.1 (k₀ + latticePoint L n)|) :
    kernelLeaves L γ δ LG (fun a x => H₀ a x + H₁ a x) up s k₀ nroot nfl =
      ∑ S ∈ (inputLeaves LG.garden).powerset,
        kernelLeaves L γ δ LG (selectLeafProfiles LG.garden S H₀ H₁) up s k₀ nroot nfl := by
  classical
  let g (S : Finset (GLeaf LG.garden.tree)) (κ : GenDecoration LG.garden d nroot nfl) : ℂ :=
    (epsDec LG.garden κ.1 : ℂ) *
      phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
      ∏ l ∈ inputLeaves LG.garden,
        (selectLeafProfiles LG.garden S H₀ H₁ l.1 (cosetDecoration LG.garden L k₀ κ.1 l.toNode) : ℂ)
  have hs (S : Finset (GLeaf LG.garden.tree)) (_ : S ∈ (inputLeaves LG.garden).powerset) :
      Summable (g S) := by
    apply summable_leafKernel_summand L γ δ LG (selectLeafProfiles LG.garden S H₀ H₁)
      up s k₀ nroot nfl hlone
    intro l hl
    by_cases hsel : l ∈ S
    · simpa only [selectLeafProfiles_apply, ite_eq_left hsel] using hF₁ l hl
    · simpa only [selectLeafProfiles_apply, ite_eq_right hsel] using hF₀ l hl
  have ht : (∑' κ : GenDecoration LG.garden d nroot nfl,
      (epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
        ∏ l ∈ inputLeaves LG.garden,
          ((H₀ l.1 (cosetDecoration LG.garden L k₀ κ.1 l.toNode) +
            H₁ l.1 (cosetDecoration LG.garden L k₀ κ.1 l.toNode) : ℝ) : ℂ)) =
        ∑ S ∈ (inputLeaves LG.garden).powerset, ∑' κ, g S κ := by
    calc
      _ = ∑' κ : GenDecoration LG.garden d nroot nfl,
          ∑ S ∈ (inputLeaves LG.garden).powerset, g S κ := by
        apply tsum_congr
        intro κ
        rw [leaf_product_add_eq_sum_subsets LG.garden H₀ H₁
          (fun l => cosetDecoration LG.garden L k₀ κ.1 l.toNode), mul_sum]
      _ = _ := Summable.tsum_finsetSum hs
  unfold kernelLeaves
  rw [ht, mul_sum]

end WaveTurbulence.LGSpine
