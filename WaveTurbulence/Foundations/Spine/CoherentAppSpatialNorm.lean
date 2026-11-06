/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.WeightedCoherentAppBound
public import WaveTurbulence.Foundations.Spine.CoherentAppSpatialRegularity
public import WaveTurbulence.Foundations.Spine.SpatialNormFromWords
/-! Assemble the actual coherent app spatial seminorm from the corrected order-zero source gate.
The remaining budget premise is a finite numerical sum of explicit leaf costs, not a kernel estimate. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Set Finset NormBridgeScratch
open scoped Topology ENNReal ContDiff

theorem coherent_app_SNorm_le (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At { P with L := L })
    (hC₁ : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hηmax : P.η ≤ 1 / 2) (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hqq' : q' ≤ q) (hqp : q ≤ p)
    (hn : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (LG : LayeredGarden 2) (hsize : Q.size = 2 * n)
    (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (A m : ℕ) (H : LeafProfiles 2 P.d) (C : (Fin 2 × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (40 * P.d + 1 + A : ℕ) (H l.1))
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR (40 * P.d + 1 + A) (40 * P.d) (H l.1) ≤
      ENNReal.ofReal (C l.1 : ℝ))
    (hplain : LG.garden.IsPlain)
    (cost : (word : List (Fin P.d)) → LeafDerivativeChoices LG.garden word.length →
      RootWeightChoices LG.garden P.d m → (Fin 2 × TTree.Path) → NNReal)
    (hcost : ∀ word, word.length ≤ A → ∀ a c, LeafwiseControlled LG
      (rootModifiedProfiles LG.garden hplain (leafDerivativeProfiles LG.garden H word a) c) (cost word a c))
    (hpositive : ∀ word, word.length ≤ A → ∀ a c, 0 < leafSizeProduct LG (cost word a c))
    (E : ℝ≥0∞)
    (hbudget : ∀ word : List (Fin P.d), word.length ≤ A →
      ENNReal.ofReal ((2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) * ∑ a : LeafDerivativeChoices LG.garden word.length,
        ∑ c : RootWeightChoices LG.garden P.d m, ENNReal.ofReal (leafSizeProduct LG (cost word a c)) ≤ E)
    (t s : ℝ) (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1)) :
    SNorm A (4 * m) (fun k => LeafApp.coherentCouple P.δ LG H Q q q' t s k) ≤ E := by
  classical
  have hlone := card_lone_le_one_of_plain LG.garden hplain
  have hlowC (a : ℕ) (ha' : a ≤ 40 * P.d + 1 + A) :
      ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ a (H l.1) :=
    fun l hl => (hc l hl).of_le (by exact_mod_cast ha')
  have hlowB (a : ℕ) (ha' : a ≤ 40 * P.d + 1 + A) :
      ∀ l ∈ inputLeaves LG.garden, SNormR a (40 * P.d) (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ) :=
    fun l hl => SNorm_mono_bound ha' le_rfl _ (Complex.ofRealCLM.contDiff.comp (hc l hl))
      _ (NNReal.coe_nonneg _) (hb l hl)
  have hApp := contDiff_coherentCouple_of_source P hsource hd hη ha hp hqq' hqp Q LG hsize hcoh
    hlone t s ht hs A H C (hlowC _ (by omega)) (hlowB _ (by omega))
  apply SNorm_le_of_word_enorm_bounds _ hApp E
  intro word hw k
  exact (weighted_wordD_coherentApp_enorm_le P hsource hd hη ha hC₁ hδ hηmax hp hqq' hqp hn
    Q LG hsize hcoh H word C (hlowC _ (by omega)) (hlowB _ (by omega)) hlone t s ht hs hplain m
    (cost word) (hcost word hw) (hpositive word hw) k).trans (hbudget word hw)

end WaveTurbulence.LGSpine
