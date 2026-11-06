/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.WeightedDerivativeCoherentApp
public import WaveTurbulence.Foundations.Spine.WeightedDerivativeCouple
/-! High weighted coordinate error bounds from the corrected order-zero leafwise source gate. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Set Finset NormBridgeScratch
open scoped Topology ENNReal

theorem weighted_wordD_coherent_error_enorm_le (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At { P with L := L })
    (hL : 1 ≤ P.L) (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
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
    (k : Mom P.d) :
    ‖((jbr k ^ (4 * m) : ℝ) : ℂ) *
      (wordD word (fun x => coupleLeaves P.L P.γ P.δ LG H t s x) k -
        wordD word (fun x => LeafApp.coherentCouple P.δ LG H Q q q' t s x) k)‖ₑ ≤
      regBound P n 1 * ∑ a : LeafDerivativeChoices LG.garden word.length,
        ∑ c : RootWeightChoices LG.garden P.d m,
          ENNReal.ofReal (leafSizeProduct LG (cost a c)) := by
  classical
  have hcK : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (1 + word.length : ℕ) (H l.1) :=
    fun l hl => (hc l hl).of_le (by exact_mod_cast (show 1 + word.length ≤ 40 * P.d + 1 + word.length by omega))
  have hbK : ∀ l ∈ inputLeaves LG.garden, SNormR (1 + word.length) (40 * P.d) (H l.1) ≤
      ENNReal.ofReal (C l.1 : ℝ) :=
    fun l hl => SNorm_mono_bound (by omega) le_rfl _ (Complex.ofRealCLM.contDiff.comp (hc l hl))
      _ (NNReal.coe_nonneg _) (hb l hl)
  have hK := weighted_wordD_coupleLeaves hd hL (by omega) P.γ P.δ LG hplain H word C hcK hbK cost hcost t s k
  have hA := weighted_wordD_coherentCouple P hsource hd hη ha hp hqq' hqp Q LG hsize hcoh H word C hc hb
    hlone t s ht hs hplain m cost hcost k
  rw [mul_sub, hK, hA, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib, ← mul_sub]
  apply (enorm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro a _
  apply (enorm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro c _
  rw [← ofReal_norm, norm_mul, norm_rootChoiceSign, one_mul, ofReal_norm]
  exact enorm_leafwise_coherent_error_le P (hsource P.L le_rfl) hd hL hη hp
    hn hqq' hqp Q LG hsize hcoh
    _ (cost a c) (hcost a c) t s ht hs k

end WaveTurbulence.LGSpine
