/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafKernelWordDerivative
public import WaveTurbulence.Foundations.Spine.WeightedCoupleKernel
/-! Exact reduction of every weighted coordinate derivative of a source couple to a finite
sum of source kernels with individually modified real leaf profiles. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset NormBridgeScratch

theorem weighted_wordD_coupleLeaves {d B m : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L)
    (hB : d + 1 ≤ B) (γ δ : ℝ) (LG : LayeredGarden 2) (hp : LG.garden.IsPlain)
    (H : LeafProfiles 2 d) (word : List (Fin d)) (C : (Fin 2 × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (1 + word.length : ℕ) (H l.1))
    (hb : ∀ l ∈ inputLeaves LG.garden,
      SNormR (1 + word.length) B (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ))
    (cost : LeafDerivativeChoices LG.garden word.length →
      RootWeightChoices LG.garden d m → (Fin 2 × TTree.Path) → NNReal)
    (hcost : ∀ a c, LeafwiseControlled LG
      (rootModifiedProfiles LG.garden hp (leafDerivativeProfiles LG.garden H word a) c) (cost a c))
    (t s : ℝ) (k : Mom d) :
    ((jbr k ^ (4 * m) : ℝ) : ℂ) * wordD word (fun x => coupleLeaves L γ δ LG H t s x) k =
      ∑ a : LeafDerivativeChoices LG.garden word.length,
        ∑ c : RootWeightChoices LG.garden d m, ((rootChoiceSign LG.garden c : ℝ) : ℂ) *
          coupleLeaves L γ δ LG
            (rootModifiedProfiles LG.garden hp (leafDerivativeProfiles LG.garden H word a) c) t s k := by
  have he := wordD_kernelLeaves_eq_sum hd hL hB γ δ LG H word C hc hb
    (fun b => if b.1.1 = 0 then t else s) 0 (fun _ => 0) 0
    (card_lone_le_one_of_plain LG.garden hp) k
  change wordD word (fun x => coupleLeaves L γ δ LG H t s x) k =
    ∑ a : LeafDerivativeChoices LG.garden word.length,
      coupleLeaves L γ δ LG (leafDerivativeProfiles LG.garden H word a) t s k at he
  rw [he, mul_sum]
  apply sum_congr rfl
  intro a _
  exact weighted_coupleLeaves hd hL γ δ LG hp (leafDerivativeProfiles LG.garden H word a)
    m (cost a) (hcost a) t s k

theorem weighted_wordD_coupleLeaves_norm_le {d B m : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L)
    (hB : d + 1 ≤ B) (γ δ : ℝ) (LG : LayeredGarden 2) (hp : LG.garden.IsPlain)
    (H : LeafProfiles 2 d) (word : List (Fin d)) (C : (Fin 2 × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (1 + word.length : ℕ) (H l.1))
    (hb : ∀ l ∈ inputLeaves LG.garden,
      SNormR (1 + word.length) B (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ))
    (cost : LeafDerivativeChoices LG.garden word.length →
      RootWeightChoices LG.garden d m → (Fin 2 × TTree.Path) → NNReal)
    (hcost : ∀ a c, LeafwiseControlled LG
      (rootModifiedProfiles LG.garden hp (leafDerivativeProfiles LG.garden H word a) c) (cost a c))
    (t s : ℝ) (k : Mom d) :
    jbr k ^ (4 * m) * ‖wordD word (fun x => coupleLeaves L γ δ LG H t s x) k‖ ≤
      ∑ a : LeafDerivativeChoices LG.garden word.length,
        ∑ c : RootWeightChoices LG.garden d m,
          ‖coupleLeaves L γ δ LG
            (rootModifiedProfiles LG.garden hp (leafDerivativeProfiles LG.garden H word a) c) t s k‖ := by
  have he := weighted_wordD_coupleLeaves hd hL hB γ δ LG hp H word C hc hb cost hcost t s k
  have hn := norm_sum_le (univ : Finset (LeafDerivativeChoices LG.garden word.length))
    (fun a => ∑ c : RootWeightChoices LG.garden d m, ((rootChoiceSign LG.garden c : ℝ) : ℂ) *
      coupleLeaves L γ δ LG
        (rootModifiedProfiles LG.garden hp (leafDerivativeProfiles LG.garden H word a) c) t s k)
  rw [← he, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (pow_nonneg (jbr_pos k).le _)] at hn
  apply hn.trans
  apply sum_le_sum
  intro a _
  have h := norm_sum_le (univ : Finset (RootWeightChoices LG.garden d m))
    (fun c => ((rootChoiceSign LG.garden c : ℝ) : ℂ) * coupleLeaves L γ δ LG
      (rootModifiedProfiles LG.garden hp (leafDerivativeProfiles LG.garden H word a) c) t s k)
  simpa only [norm_mul, norm_rootChoiceSign, one_mul] using h

end WaveTurbulence.LGSpine
