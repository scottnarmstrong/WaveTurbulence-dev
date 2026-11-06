/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentAppDerivative
public import WaveTurbulence.Foundations.Spine.LeafProfileHighBounds
/-! Source app differentiation directly from original high-order leaf norms. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Set Finset
open scoped Topology

theorem hasFDerivAt_coherentCouple_high (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At { P with L := L })
    (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hqq' : q' ≤ q) (hqp : q ≤ p)
    (Q : RegCpl) (LG : LayeredGarden 2) (hsize : Q.size = 2 * n)
    (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (H : LeafProfiles 2 P.d) (C : (Fin 2 × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (40 * P.d + 1 : ℕ) (H l.1))
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR (40 * P.d + 1) (40 * P.d) (H l.1) ≤
      ENNReal.ofReal (C l.1 : ℝ))
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (t s : ℝ) (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1))
    (k : Mom P.d) :
    HasFDerivAt (fun x => LeafApp.coherentCouple P.δ LG H Q q q' t s x)
      (coordinateLinearMap (fun i => ∑ l : ActualInputLeaves LG.garden,
        LeafApp.coherentCouple P.δ LG (singleLeafDerivative LG.garden H l i) Q q q' t s k)) k := by
  have hH := leafwiseControlled_of_high LG H C (by omega) le_rfl hc hb
  let CD : (Fin 2 × TTree.Path) → NNReal := fun a => (P.d : NNReal) ^ (40 * P.d + 1) * C a
  have hDC (l : ActualInputLeaves LG.garden) (j : Fin P.d) :
      LeafwiseControlled LG (singleLeafDerivative LG.garden H l j) CD :=
    (singleLeafDerivative_high hd LG.garden H C hc hb l j).2
  have hc1 : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (1 : ℕ) (H l.1) :=
    fun l hl => (hc l hl).of_le (by simp)
  have hb1 : ∀ l ∈ inputLeaves LG.garden, SNormR 1 (40 * P.d) (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ) :=
    fun l hl => SNorm_mono_bound (by omega) le_rfl _ (Complex.ofRealCLM.contDiff.comp (hc l hl))
      _ (NNReal.coe_nonneg _) (hb l hl)
  exact hasFDerivAt_coherentCouple_of_source P hsource hd hη ha hp hqq' hqp Q LG hsize hcoh
    H C hH (fun _ _ => CD) hDC hc1 C hb1 hlone t s ht hs k

end WaveTurbulence.LGSpine
