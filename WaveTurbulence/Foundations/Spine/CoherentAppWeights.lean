/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentKernelLimit
public import WaveTurbulence.Foundations.Spine.WeightedCoupleKernel
/-! Exact root-weight transfer for the literal coherent app, obtained from actual kernel limits. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Set Finset
open scoped Topology

theorem weighted_coherentCouple_of_source (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At { P with L := L })
    (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hqq' : q' ≤ q) (hqp : q ≤ p)
    (Q : RegCpl) (LG : LayeredGarden 2) (hsize : Q.size = 2 * n)
    (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (hplain : LG.garden.IsPlain)
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal)
    (hH : LeafwiseControlled LG H B) (m : ℕ)
    (BW : RootWeightChoices LG.garden P.d m → (Fin 2 × TTree.Path) → NNReal)
    (hHW : ∀ c, LeafwiseControlled LG (rootModifiedProfiles LG.garden hplain H c) (BW c))
    (t s : ℝ) (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1))
    (k : Mom P.d) :
    ((jbr k ^ (4 * m) : ℝ) : ℂ) * LeafApp.coherentCouple P.δ LG H Q q q' t s k =
      ∑ c : RootWeightChoices LG.garden P.d m, ((rootChoiceSign LG.garden c : ℝ) : ℂ) *
        LeafApp.coherentCouple P.δ LG (rootModifiedProfiles LG.garden hplain H c) Q q q' t s k := by
  have hK := (tendstoUniformly_coherentCouple P hsource hd hη ha hp hqq' hqp Q LG hsize hcoh
    H B hH t s ht hs).tendsto_at k
  have hleft := hK.const_mul (((jbr k ^ (4 * m) : ℝ) : ℂ))
  have hright := tendsto_finset_sum (univ : Finset (RootWeightChoices LG.garden P.d m))
    (fun c _ => ((tendstoUniformly_coherentCouple P hsource hd hη ha hp hqq' hqp Q LG hsize hcoh
      _ (BW c) (hHW c) t s ht hs).tendsto_at k).const_mul
        (((rootChoiceSign LG.garden c : ℝ) : ℂ)))
  have he : (fun L => ((jbr k ^ (4 * m) : ℝ) : ℂ) * coupleLeaves L P.γ P.δ LG H t s k) =ᶠ[atTop]
      (fun L => ∑ c : RootWeightChoices LG.garden P.d m, ((rootChoiceSign LG.garden c : ℝ) : ℂ) *
        coupleLeaves L P.γ P.δ LG (rootModifiedProfiles LG.garden hplain H c) t s k) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    exact weighted_coupleLeaves hd hL P.γ P.δ LG hplain H m BW hHW t s k
  exact tendsto_nhds_unique (hleft.congr' he) hright

end WaveTurbulence.LGSpine
