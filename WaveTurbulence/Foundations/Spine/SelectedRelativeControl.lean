/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SelectedProfileRegularity
public import WaveTurbulence.Foundations.Spine.RelativeLeafControl
public import WaveTurbulence.Foundations.XChain.SNormOperations
/-! All selected phi/R profiles satisfy relative modification bounds from the two original inputs. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

 theorem selected_combined_profiles_controlled {w d A m : ℕ} (hd : 1 ≤ d)
    (LG : LayeredGarden w) (hp : LG.garden.IsPlain) (H₀ H₁ : LeafProfiles w d)
    (B₀ B₁ : (Fin w × TTree.Path) → NNReal) (C : ℝ) (hC : 0 ≤ C) (C₂ : NNReal)
    (hc₀ : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (40 * d + 1 + A : ℕ) (H₀ l.1))
    (hc₁ : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (40 * d + 1 + A : ℕ) (H₁ l.1))
    (h₀ : LeafwiseControlled LG H₀ B₀) (h₁ : LeafwiseControlled LG H₁ B₁)
    (hb₀ : ∀ l ∈ inputLeaves LG.garden,
      SNormR (40 * d + 1 + A) (40 * d + 4 * m) (H₀ l.1) ≤ ENNReal.ofReal (C * B₀ l.1))
    (hb₁ : ∀ l ∈ inputLeaves LG.garden,
      SNormR (40 * d + 1 + A) (40 * d + 4 * m) (H₁ l.1) ≤ ENNReal.ofReal (C * B₁ l.1))
    (hC₂ : (((2 : ℝ) ^ (40 * d) * (d : ℝ) ^ (40 * d)) ^ (4 * m)) *
      ((d : ℝ) ^ (40 * d + A) * C) ≤ C₂)
    (S : Finset (GLeaf LG.garden.tree)) (word : List (Fin d)) (hw : word.length ≤ A)
    (a : LeafDerivativeChoices LG.garden word.length) (c : RootWeightChoices LG.garden d m) :
    LeafwiseControlled LG
      (rootModifiedProfiles LG.garden hp
        (leafDerivativeProfiles LG.garden (selectLeafProfiles LG.garden S H₀ H₁) word a) c)
      (relativeLeafModificationCosts LG.garden (combinedModifiedInputs LG.garden hp word a c)
        (selectLeafBounds LG.garden S B₀ B₁) C₂) := by
  have hc (l) (hl : l ∈ inputLeaves LG.garden) :
      ContDiff ℝ (40 * d + 1 + A : ℕ) (selectLeafProfiles LG.garden S H₀ H₁ l.1) :=
    contDiff_selected_profile LG.garden S H₀ H₁ l (hc₀ l hl) (hc₁ l hl)
  have hb (l) (hl : l ∈ inputLeaves LG.garden) :
      SNormR (40 * d + 1 + A) (40 * d + 4 * m) (selectLeafProfiles LG.garden S H₀ H₁ l.1) ≤
        ENNReal.ofReal (C * selectLeafBounds LG.garden S B₀ B₁ l.1) :=
    SNormR_selected_relative_le LG.garden S H₀ H₁ B₀ B₁ C l (hb₀ l hl) (hb₁ l hl)
  apply combined_leaf_profiles_controlled_relative hd LG hp _ word a c _ C₂ C hC
  · intro l hl
    exact (hc l hl).of_le (by exact_mod_cast (show 40 * d + word.length ≤ 40 * d + 1 + A by omega))
  · exact LeafwiseControlled.select LG S H₀ H₁ B₀ B₁ h₀ h₁
  · intro l hl
    exact SNorm_mono_bound (by omega) le_rfl _ (Complex.ofRealCLM.contDiff.comp (hc l hl))
      _ (mul_nonneg hC (NNReal.coe_nonneg _)) (hb l hl)
  · apply le_trans _ hC₂
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hC
    apply pow_le_pow_right₀ (by exact_mod_cast hd : (1 : ℝ) ≤ d)
    omega

end WaveTurbulence.LGSpine
