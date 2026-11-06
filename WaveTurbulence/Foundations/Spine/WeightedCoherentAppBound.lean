/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.WeightedDerivativeCoherentApp
public import WaveTurbulence.Foundations.Spine.LeafwiseAppPointwise
/-! The source leafwise product cost controls every weighted coordinate word of the fixed app. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Set Finset NormBridgeScratch
open scoped ENNReal

theorem weighted_wordD_coherentApp_enorm_le (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At { P with L := L })
    (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    (hC₁ : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hηmax : P.η ≤ 1 / 2)
    {p n q q' : ℕ} (hp : p < P.D) (hqq' : q' ≤ q) (hqp : q ≤ p)
    (hn : n ≤ P.N (p + 1) ^ 4)
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
    (hpositive : ∀ a c, 0 < leafSizeProduct LG (cost a c)) (k : Mom P.d) :
    ‖((jbr k ^ (4 * m) : ℝ) : ℂ) *
      wordD word (fun x => LeafApp.coherentCouple P.δ LG H Q q q' t s x) k‖ₑ ≤
      ENNReal.ofReal ((2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
        ∑ a : LeafDerivativeChoices LG.garden word.length,
          ∑ c : RootWeightChoices LG.garden P.d m, ENNReal.ofReal (leafSizeProduct LG (cost a c)) := by
  classical
  rw [weighted_wordD_coherentCouple P hsource hd hη ha hp hqq' hqp Q LG hsize hcoh
    H word C hc hb hlone t s ht hs hplain m cost hcost k]
  apply (enorm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro a _
  apply (enorm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro c _
  rw [← ofReal_norm, norm_mul, norm_rootChoiceSign, one_mul, ofReal_norm]
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact enorm_leafwise_coherentApp_le P (hsource P.L le_rfl) hC₁ hδ hη hηmax hp hn
    hqq' hqp Q LG hsize hcoh _ (cost a c) (hcost a c) (hpositive a c) t s ht hs k

end WaveTurbulence.LGSpine
