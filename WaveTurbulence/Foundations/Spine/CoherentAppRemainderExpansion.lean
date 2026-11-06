/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentKernelLimit
public import WaveTurbulence.Foundations.Spine.LeafKernelRemainderDifference
public import WaveTurbulence.Foundations.Spine.LeafSelectionBounds
/-! The literal coherent app inherits the actual marked-leaf remainder expansion by uniform limits. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Set Finset
open scoped Topology

/-- No app multilinearity gate is needed: use the exact kernel expansion at large L
and the already proved convergence to the fixed explicit coherent formula. -/
theorem coherentCouple_sub_eq_sum_nonempty_subsets_of_source (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hqq' : q' ≤ q) (hqp : q ≤ p)
    (Q : RegCpl) (LG : LayeredGarden 2) (hsize : Q.size = 2 * n)
    (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (H₀ H₁ : LeafProfiles 2 P.d) (B₀ B₁ Bsum : (Fin 2 × TTree.Path) → NNReal)
    (h₀ : LeafwiseControlled LG H₀ B₀) (h₁ : LeafwiseControlled LG H₁ B₁)
    (hsum : LeafwiseControlled LG (fun a x => H₀ a x + H₁ a x) Bsum)
    (t s : ℝ) (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1))
    (k : Mom P.d) :
    LeafApp.coherentCouple P.δ LG (fun a x => H₀ a x + H₁ a x) Q q q' t s k -
      LeafApp.coherentCouple P.δ LG H₀ Q q q' t s k =
      ∑ S ∈ (inputLeaves LG.garden).powerset.erase ∅,
        LeafApp.coherentCouple P.δ LG (selectLeafProfiles LG.garden S H₀ H₁) Q q q' t s k := by
  have hleft := ((tendstoUniformly_coherentCouple P hsource hd hη ha hp hqq' hqp
    Q LG hsize hcoh _ Bsum hsum t s ht hs).tendsto_at k).sub
      ((tendstoUniformly_coherentCouple P hsource hd hη ha hp hqq' hqp
        Q LG hsize hcoh H₀ B₀ h₀ t s ht hs).tendsto_at k)
  have hright := tendsto_finset_sum ((inputLeaves LG.garden).powerset.erase ∅)
    (fun S _ => (tendstoUniformly_coherentCouple P hsource hd hη ha hp hqq' hqp
      Q LG hsize hcoh _ (selectLeafBounds LG.garden S B₀ B₁)
        (h₀.select LG S H₀ H₁ B₀ B₁ h₁) t s ht hs).tendsto_at k)
  have he : (fun L => coupleLeaves L P.γ P.δ LG (fun a x => H₀ a x + H₁ a x) t s k -
      coupleLeaves L P.γ P.δ LG H₀ t s k) =ᶠ[atTop]
      (fun L => ∑ S ∈ (inputLeaves LG.garden).powerset.erase ∅,
        coupleLeaves L P.γ P.δ LG (selectLeafProfiles LG.garden S H₀ H₁) t s k) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    exact kernelLeaves_sub_eq_sum_nonempty_subsets L P.γ P.δ LG H₀ H₁
      (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0
      (card_lone_le_one_of_plain LG.garden hcoh.2.1.1.1)
      (h₀.summable_coset hd hL k) (h₁.summable_coset hd hL k)
  exact tendsto_nhds_unique (hleft.congr' he) hright

end WaveTurbulence.LGSpine
