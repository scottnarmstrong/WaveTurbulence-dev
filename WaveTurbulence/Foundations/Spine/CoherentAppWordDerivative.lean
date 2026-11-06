/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentAppHighDerivative
public import WaveTurbulence.Foundations.Spine.LeafKernelWordDerivative
/-! Repeated derivatives of the literal coherent app preserve individual original leaf addresses. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Set Finset NormBridgeScratch
open scoped Topology

theorem wordD_coherentCouple_eq_sum (P : WTParams)
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
    (k : Mom P.d) :
    wordD word (fun x => LeafApp.coherentCouple P.δ LG H Q q q' t s x) k =
      ∑ c : LeafDerivativeChoices LG.garden word.length,
        LeafApp.coherentCouple P.δ LG (leafDerivativeProfiles LG.garden H word c) Q q q' t s k := by
  classical
  induction word generalizing k with
  | nil =>
    change LeafApp.coherentCouple P.δ LG H Q q q' t s k =
      ∑ _c : PUnit, LeafApp.coherentCouple P.δ LG H Q q q' t s k
    simp only [Fintype.sum_unique]
  | cons j word ih =>
    have hn : 40 * P.d + 1 + word.length ≤ 40 * P.d + 1 + (j :: word).length := by simp
    have hcTail : ∀ l ∈ inputLeaves LG.garden,
        ContDiff ℝ (40 * P.d + 1 + word.length : ℕ) (H l.1) :=
      fun l hl => (hc l hl).of_le (by exact_mod_cast hn)
    have hbTail : ∀ l ∈ inputLeaves LG.garden,
        SNormR (40 * P.d + 1 + word.length) (40 * P.d) (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ) :=
      fun l hl => SNorm_mono_bound hn le_rfl _ (Complex.ofRealCLM.contDiff.comp (hc l hl))
        _ (NNReal.coe_nonneg _) (hb l hl)
    have he : wordD word (fun x => LeafApp.coherentCouple P.δ LG H Q q q' t s x) =
        fun x => ∑ c : LeafDerivativeChoices LG.garden word.length,
          LeafApp.coherentCouple P.δ LG (leafDerivativeProfiles LG.garden H word c) Q q q' t s x :=
      funext (fun x => ih hcTail hbTail x)
    change partialMom j (wordD word (fun x => LeafApp.coherentCouple P.δ LG H Q q q' t s x)) k = _
    rw [he]
    have hFD (c : LeafDerivativeChoices LG.garden word.length) (x : Mom P.d) :=
      hasFDerivAt_coherentCouple_high P hsource hd hη ha hp hqq' hqp Q LG hsize hcoh
        (leafDerivativeProfiles LG.garden H word c) (leafDerivativeCosts C (40 * P.d + 1) word)
        (contDiff_leafDerivativeProfiles LG.garden H word c hcTail)
        (leafDerivativeProfiles_norm hd LG.garden H word c C hcTail hbTail)
        hlone t s ht hs x
    rw [partialMom_finsetSum univ _ j k (fun c _ => (hFD c k).differentiableAt)]
    have hfirst (c : LeafDerivativeChoices LG.garden word.length) :
        partialMom j (fun x => LeafApp.coherentCouple P.δ LG
          (leafDerivativeProfiles LG.garden H word c) Q q q' t s x) k =
        ∑ l : ActualInputLeaves LG.garden, LeafApp.coherentCouple P.δ LG
          (singleLeafDerivative LG.garden (leafDerivativeProfiles LG.garden H word c) l j) Q q q' t s k := by
      unfold partialMom
      rw [(hFD c k).fderiv, coordinateLinearMap_single]
    simp_rw [hfirst]
    change (∑ c : LeafDerivativeChoices LG.garden word.length,
        ∑ l : ActualInputLeaves LG.garden,
          LeafApp.coherentCouple P.δ LG (singleLeafDerivative LG.garden
            (leafDerivativeProfiles LG.garden H word c) l j) Q q q' t s k) =
      ∑ c : ActualInputLeaves LG.garden × LeafDerivativeChoices LG.garden word.length,
        LeafApp.coherentCouple P.δ LG (singleLeafDerivative LG.garden
          (leafDerivativeProfiles LG.garden H word c.2) c.1 j) Q q q' t s k
    rw [Fintype.sum_prod_type, sum_comm]

end WaveTurbulence.LGSpine
