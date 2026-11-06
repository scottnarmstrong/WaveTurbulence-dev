/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentErrorSpatialNorm
public import WaveTurbulence.Foundations.Spine.CombinedLeafCostUniform
/-! Explicit high-order coherent error bound, with the source high norm paid only at modified leaves. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Set Finset NormBridgeScratch
open scoped Topology ENNReal

theorem coherent_error_SNorm_uniform (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At { P with L := L })
    (hL : 1 ≤ P.L) (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hqq' : q' ≤ q) (hqp : q ≤ p)
    (hn : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (LG : LayeredGarden 2) (hsize : Q.size = 2 * n)
    (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (A m : ℕ) (H : LeafProfiles 2 P.d) (C₁ C₂ U : NNReal)
    (hC₁ : (1 : ℝ) ≤ C₁) (hC₂ : (1 : ℝ) ≤ C₂)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (40 * P.d + 1 + A : ℕ) (H l.1))
    (hlow : ∀ l ∈ inputLeaves LG.garden, SNormR (40 * P.d) (40 * P.d) (H l.1) ≤
      ENNReal.ofReal (C₁ : ℝ))
    (hhigh : ∀ l ∈ inputLeaves LG.garden, SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) (H l.1) ≤
      ENNReal.ofReal (U : ℝ))
    (hcostC₂ : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * U) ≤ C₂)
    (hplain : LG.garden.IsPlain)
    (t s : ℝ) (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1)) :
    SNorm A (4 * m) (fun k => coupleLeaves P.L P.γ P.δ LG H t s k -
      LeafApp.coherentCouple P.δ LG H Q q q' t s k) ≤
      regBound P n 1 *
        ((((inputLeaves LG.garden).card + 1 : ℕ) : ℝ≥0∞) ^ A *
          (Fintype.card (RootWeightChoices LG.garden P.d m) : ℝ≥0∞) *
          ENNReal.ofReal ((C₁ : ℝ) ^ (inputLeaves LG.garden).card * (C₂ : ℝ) ^ (4 * m + A))) := by
  classical
  let cost := fun (word : List (Fin P.d)) (a : LeafDerivativeChoices LG.garden word.length)
      (c : RootWeightChoices LG.garden P.d m) =>
    leafModificationCosts LG.garden (combinedModifiedInputs LG.garden hplain word a c) C₁ C₂
  have hb : ∀ l ∈ inputLeaves LG.garden, SNormR (40 * P.d + 1 + A) (40 * P.d) (H l.1) ≤
      ENNReal.ofReal (U : ℝ) :=
    fun l hl => SNorm_mono_bound le_rfl (by omega) _ (Complex.ofRealCLM.contDiff.comp (hc l hl))
      _ (NNReal.coe_nonneg _) (hhigh l hl)
  apply coherent_error_SNorm_le P hsource hL hd hη ha hp hqq' hqp hn Q LG hsize hcoh
    A m H (fun _ => U) hc hb hplain cost
  · intro word hw a c
    apply combined_leaf_profiles_controlled hd LG hplain H word a c C₁ C₂ U (NNReal.coe_nonneg _)
    · intro l hl
      exact (hc l hl).of_le (by exact_mod_cast (show 40 * P.d + word.length ≤ 40 * P.d + 1 + A by omega))
    · exact hlow
    · intro l hl
      exact SNorm_mono_bound (by omega) le_rfl _ (Complex.ofRealCLM.contDiff.comp (hc l hl))
        _ (NNReal.coe_nonneg _) (hhigh l hl)
    · apply le_trans _ hcostC₂
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by exact_mod_cast hd) (Nat.add_le_add_left hw _)) (NNReal.coe_nonneg _)
  · intro word hw
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [show 2 * 2 * m = 4 * m by omega] using
      combined_leaf_cost_sum_uniform LG hplain word hw C₁ C₂ hC₁ hC₂
  · exact ht
  · exact hs

end WaveTurbulence.LGSpine
