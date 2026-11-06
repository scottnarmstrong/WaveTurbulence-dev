/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.KernelApproximationLimits
public import WaveTurbulence.Foundations.Spine.StageOrderLimit
/-! Uniform spatial convergence of the actual coherent kernels to the fixed source formula. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Set Finset
open scoped Topology ENNReal

theorem tendstoUniformly_coherentCouple (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At { P with L := L })
    (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hqq' : q' ≤ q) (hqp : q ≤ p)
    (Q : RegCpl) (LG : LayeredGarden 2) (hsize : Q.size = 2 * n)
    (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal)
    (hH : LeafwiseControlled LG H B) (t s : ℝ)
    (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1)) :
    TendstoUniformly (fun L k => coupleLeaves L P.γ P.δ LG H t s k)
      (fun k => LeafApp.coherentCouple P.δ LG H Q q q' t s k) atTop := by
  apply tendstoUniformly_of_enorm_error _ _
    (fun L => P.C₁ * (P.C₁ * P.δ) ^ n * L ^ (-(P.gamma1 - Real.sqrt P.η)) * leafSizeProduct LG B)
  · exact tendsto_reg_error (fun L : ℝ => L) tendsto_id _ _ _ _ ha n
  · filter_upwards [eventually_ge_atTop P.L, eventually_ge_atTop (1 : ℝ),
      eventually_order_le_stage P hd (p + 1) n] with L hL hL1 hn
    intro k
    have hh := enorm_leafwise_coherent_error_le ({ P with L := L } : WTParams)
      (hsource L hL) hd hL1 hη hp hn hqq' hqp Q LG hsize hcoh H B hH t s ht hs k
    have hB : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg (fun _ _ => NNReal.coe_nonneg _)
    simpa only [regBound, WTParams.gamma1, Nat.cast_one, ENNReal.ofReal_mul' hB, mul_one] using hh

end WaveTurbulence.LGSpine
