/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentAppSpatialNorm
public import WaveTurbulence.Foundations.Spine.RelativeLeafCostUniform
public import WaveTurbulence.Foundations.Spine.RelativeChoiceAbsorption
/-! A marked remainder factor survives the complete coherent-app spatial seminorm estimate. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset NormBridgeScratch
open scoped ENNReal

 theorem coherent_app_marked_SNorm_le (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (hC₁ : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hηmax : P.η ≤ 1 / 2)
    (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hqq' : q' ≤ q) (hqp : q ≤ p)
    (hn : n ≤ P.N (p + 1) ^ 4) (Q : RegCpl) (LG : LayeredGarden 2)
    (hsize : Q.size = 2 * n) (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (A m : ℕ) (H : LeafProfiles 2 P.d) (C : (Fin 2 × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (40 * P.d + 1 + A : ℕ) (H l.1))
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR (40 * P.d + 1 + A) (40 * P.d) (H l.1) ≤
      ENNReal.ofReal (C l.1 : ℝ))
    (hplain : LG.garden.IsPlain) (horder : LG.garden.order = 2 * n)
    (B : (Fin 2 × TTree.Path) → NNReal) (C₂ : NNReal) (hC₂ : (1 : ℝ) ≤ C₂)
    (hB : ∀ l ∈ inputLeaves LG.garden, 0 < (B l.1 : ℝ))
    (ε D : ℝ) (hε : 0 ≤ ε)
    (hprod : leafSizeProduct LG B ≤ ε * P.C₁ ^ (inputLeaves LG.garden).card)
    (hchoice : ((inputLeaves LG.garden).card + 1 : ℝ) ^ A *
      (Fintype.card (RootWeightChoices LG.garden P.d m) : ℝ) ≤ D * 8 ^ n)
    (hcost : ∀ word : List (Fin P.d), word.length ≤ A →
      ∀ (a : LeafDerivativeChoices LG.garden word.length) (c : RootWeightChoices LG.garden P.d m),
        LeafwiseControlled LG
          (rootModifiedProfiles LG.garden hplain (leafDerivativeProfiles LG.garden H word a) c)
          (relativeLeafModificationCosts LG.garden (combinedModifiedInputs LG.garden hplain word a c) B C₂))
    (t s : ℝ) (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1)) :
    SNorm A (4 * m) (fun k => LeafApp.coherentCouple P.δ LG H Q q q' t s k) ≤
      ENNReal.ofReal (((2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
        (ε * (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A))))) := by
  let cost : (word : List (Fin P.d)) → LeafDerivativeChoices LG.garden word.length →
      RootWeightChoices LG.garden P.d m → (Fin 2 × TTree.Path) → NNReal := fun word a c =>
    relativeLeafModificationCosts LG.garden (combinedModifiedInputs LG.garden hplain word a c) B C₂
  refine coherent_app_SNorm_le P hsource hC₁ hδ hηmax hd hη ha hp hqq' hqp hn Q LG hsize hcoh
    A m H C hc hb hplain cost hcost ?_ _ ?_ t s ht hs
  · intro word _ a c
    exact relative_leaf_cost_product_pos LG _ B C₂ hB (zero_lt_one.trans_le hC₂)
  · intro word hw
    have hsum := relative_combined_leaf_cost_sum_uniform (m := m) LG hplain word hw B C₂ hC₂
    have hmarked := coherent_choice_cost_marked_le (d := P.d) (m := m) (A := A) LG.garden hplain horder
      D P.C₁ C₂ (leafSizeProduct LG B) ε (zero_le_one.trans hC₁) (NNReal.coe_nonneg _) hε hprod hchoice
    have hsum' := hsum.trans hmarked
    have hA : 0 ≤ (2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2 := by positivity
    rw [ENNReal.ofReal_mul hA]
    exact mul_le_mul_of_nonneg_left hsum' (by positivity)

end WaveTurbulence.LGSpine
