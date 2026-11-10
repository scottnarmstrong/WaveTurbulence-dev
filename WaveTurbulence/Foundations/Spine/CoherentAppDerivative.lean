/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentKernelLimit
public import WaveTurbulence.Foundations.Spine.CoordinateUniformLimits
public import WaveTurbulence.Foundations.Spine.SingleLeafDerivativeNorm
public import WaveTurbulence.Foundations.Spine.LeafwiseKernelSpatial
public import WaveTurbulence.Foundations.Spine.UniformFiniteSum
/-! Derivatives of the fixed coherent approximation inherited from its literal kernel limit.
All auxiliary premises concern input regularity and seminorms; no app identity is assumed. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Set Finset
open scoped Topology

theorem hasFDerivAt_coherentCouple_of_source (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At { P with L := L })
    (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hqq' : q' ≤ q) (hqp : q ≤ p)
    (Q : RegCpl) (LG : LayeredGarden 2) (hsize : Q.size = 2 * n)
    (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal)
    (hH : LeafwiseControlled LG H B)
    (BD : ActualInputLeaves LG.garden → Fin P.d → (Fin 2 × TTree.Path) → NNReal)
    (hHD : ∀ l j, LeafwiseControlled LG (singleLeafDerivative LG.garden H l j) (BD l j))
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (1 : ℕ) (H l.1))
    (C : (Fin 2 × TTree.Path) → NNReal)
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR 1 (40 * P.d) (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ))
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (t s : ℝ) (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1))
    (k : Mom P.d) :
    HasFDerivAt (fun x => LeafApp.coherentCouple P.δ LG H Q q q' t s x)
      (coordinateLinearMap (fun i => ∑ l : ActualInputLeaves LG.garden,
        LeafApp.coherentCouple P.δ LG (singleLeafDerivative LG.garden H l i) Q q q' t s k)) k := by
  classical
  let K := fun L k => coupleLeaves L P.γ P.δ LG H t s k
  let A := fun k => LeafApp.coherentCouple P.δ LG H Q q q' t s k
  let D := fun j k => ∑ l : ActualInputLeaves LG.garden,
    LeafApp.coherentCouple P.δ LG (singleLeafDerivative LG.garden H l j) Q q q' t s k
  have hK : TendstoUniformly K A atTop :=
    tendstoUniformly_coherentCouple P hsource hd hη ha hp hqq' hqp Q LG hsize hcoh H B hH t s ht hs
  have hdiff : ∀ᶠ L : ℝ in atTop, Differentiable ℝ (K L) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hh := contDiff_kernelLeaves_spatial hd hL P.γ P.δ LG H C
      (fun l hl => Complex.ofRealCLM.contDiff.comp (hc l hl)) hb (by omega)
      (fun b => if b.1.1 = 0 then t else s) 0 (fun _ => 0) 0 hlone
    exact hh.differentiable (by norm_num)
  have hder (i : Fin P.d) : TendstoUniformly (fun L x => partialMom i (K L) x) (D i) atTop := by
    have hsum := tendstoUniformly_finset_sum (univ : Finset (ActualInputLeaves LG.garden))
      (fun l L k => coupleLeaves L P.γ P.δ LG (singleLeafDerivative LG.garden H l i) t s k)
      (fun l k => LeafApp.coherentCouple P.δ LG (singleLeafDerivative LG.garden H l i) Q q q' t s k)
      (fun l _ => tendstoUniformly_coherentCouple P hsource hd hη ha hp hqq' hqp Q LG hsize hcoh
        _ (BD l i) (hHD l i) t s ht hs)
    have he : ∀ᶠ L : ℝ in atTop, (fun x => partialMom i (K L) x) =
        (fun x => ∑ l : ActualInputLeaves LG.garden,
          coupleLeaves L P.γ P.δ LG (singleLeafDerivative LG.garden H l i) t s x) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
      funext x
      exact partialMom_kernelLeaves_eq_sum hd hL (by omega) P.γ P.δ LG H C hc hb
        (fun b => if b.1.1 = 0 then t else s) 0 (fun _ => 0) 0 hlone i x
    exact (tendstoUniformly_congr he).mpr hsum
  exact hasFDerivAt_of_uniform_coordinate_limits K A D hdiff (fun x => hK.tendsto_at x) hder k

end WaveTurbulence.LGSpine
