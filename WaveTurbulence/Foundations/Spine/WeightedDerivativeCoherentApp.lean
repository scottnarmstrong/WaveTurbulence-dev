/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentAppWordDerivative
public import WaveTurbulence.Foundations.Spine.CoherentAppWeights
/-! Combined derivative and root-weight transfer for literal coherent source apps. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Set Finset NormBridgeScratch
open scoped Topology

theorem weighted_wordD_coherentCouple (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At { P with L := L })
    (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hqq' : q' ≤ q) (hqp : q ≤ p)
    (Q : RegCpl) (LG : LayeredGarden 2) (hsize : Q.size = 2 * n)
    (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (H : LeafProfiles 2 P.d) (word : List (Fin P.d))
    (C : (Fin 2 × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (40 * P.d + 1 + word.length : ℕ) (H l.1))
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR (40 * P.d + 1 + word.length) (40 * P.d) (H l.1) ≤
      ENNReal.ofReal (C l.1 : ℝ))
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (t s : ℝ) (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1))
    (hplain : LG.garden.IsPlain) (m : ℕ)
    (cost : LeafDerivativeChoices LG.garden word.length →
      RootWeightChoices LG.garden P.d m → (Fin 2 × TTree.Path) → NNReal)
    (hcost : ∀ a c, LeafwiseControlled LG
      (rootModifiedProfiles LG.garden hplain (leafDerivativeProfiles LG.garden H word a) c) (cost a c))
    (k : Mom P.d) :
    ((jbr k ^ (4 * m) : ℝ) : ℂ) * wordD word (fun x => LeafApp.coherentCouple P.δ LG H Q q q' t s x) k =
      ∑ a : LeafDerivativeChoices LG.garden word.length,
        ∑ c : RootWeightChoices LG.garden P.d m, ((rootChoiceSign LG.garden c : ℝ) : ℂ) *
          LeafApp.coherentCouple P.δ LG
            (rootModifiedProfiles LG.garden hplain (leafDerivativeProfiles LG.garden H word a) c) Q q q' t s k := by
  classical
  rw [wordD_coherentCouple_eq_sum P hsource hd hη ha hp hqq' hqp Q LG hsize hcoh H word C hc hb
    hlone t s ht hs k, mul_sum]
  apply sum_congr rfl
  intro a _
  have hlowC : ∀ l ∈ inputLeaves LG.garden,
      ContDiff ℝ (40 * P.d + word.length : ℕ) (H l.1) :=
    fun l hl => (hc l hl).of_le (by exact_mod_cast (show 40 * P.d + word.length ≤ 40 * P.d + 1 + word.length by omega))
  have hlowB : ∀ l ∈ inputLeaves LG.garden,
      SNormR (40 * P.d + word.length) (40 * P.d) (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ) :=
    fun l hl => SNorm_mono_bound (by omega) le_rfl _ (Complex.ofRealCLM.contDiff.comp (hc l hl))
      _ (NNReal.coe_nonneg _) (hb l hl)
  have hH : LeafwiseControlled LG (leafDerivativeProfiles LG.garden H word a) (leafDerivativeCosts C (40 * P.d) word) :=
    leafDerivativeProfiles_norm hd LG.garden H word a C hlowC hlowB
  exact weighted_coherentCouple_of_source P hsource hd hη ha hp hqq' hqp Q LG hsize hcoh hplain
    _ _ hH m (cost a) (hcost a) t s ht hs k

end WaveTurbulence.LGSpine
