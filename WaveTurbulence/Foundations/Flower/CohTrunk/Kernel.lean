/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CohTrunk.Main

/-!
# COH-TRUNK: Lemma 5.1 at the kernel level

The frontier-weighted coherent couple kernel is the single crossing factor times the unweighted one (formula
(5.2) with the raw kernel).  `coupleLeavesTopR … (fun _ _ => 1)` is the unweighted kernel (`rowTopWeightR ≡ 1`).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CohTrunk
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine WaveTurbulence.PL234 TTree

theorem tsum_scale {ι : Type*} (f f' T : ι → ℂ) (c : ℂ) (h : ∀ i, f i = c * f' i) :
    ∑' i, f i * T i = c * ∑' i, f' i * T i := by
  rw [← tsum_mul_left]
  exact tsum_congr fun i => by rw [h i]; ring

theorem kernelLeavesW_scale {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (m m' : (GNode LG.garden.tree → Mom d) → ℂ) (c : ℂ)
    (hm : ∀ κ : GenDecoration LG.garden d nroot nfl,
      m (cosetDecoration LG.garden L k₀ κ.1) = c * m' (cosetDecoration LG.garden L k₀ κ.1)) :
    Stage1W.kernelLeavesW L γ δ LG H up s k₀ nroot nfl m =
      c * Stage1W.kernelLeavesW L γ δ LG H up s k₀ nroot nfl m' := by
  unfold Stage1W.kernelLeavesW
  have h := tsum_scale
    (fun κ : GenDecoration LG.garden d nroot nfl => m (cosetDecoration LG.garden L k₀ κ.1))
    (fun κ : GenDecoration LG.garden d nroot nfl => m' (cosetDecoration LG.garden L k₀ κ.1))
    (fun κ : GenDecoration LG.garden d nroot nfl =>
      ((epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)))
    c hm
  rw [h]
  ring

/-- **Lemma 5.1, kernel form (couples)**: the weighted couple kernel is the crossing factor times the unweighted
kernel. -/
theorem coupleLeavesTopR_factor {d p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2}
    (hcoh : IsCoherentCoupleAt p q q' Q LG) (hqp : q ≤ p) (hq'p : q' ≤ p)
    (g : Fin 2 → Mom d → ℂ) (L γ δ : ℝ) (H : LeafProfiles 2 d) (t s : ℝ) (k : Mom d) :
    Stage1W.coupleLeavesTopR L γ δ p g q q' LG H t s k =
      (if q' < p ∧ q = p then g 0 k else if q < p ∧ q' = p then g 1 k else 1) *
        Stage1W.coupleLeavesTopR L γ δ p (fun _ _ => 1) q q' LG H t s k := by
  refine kernelLeavesW_scale L γ δ LG H _ 0 k (fun _ => 0) 0 _ _ _ fun κ => ?_
  have hB := rowTopAgreementCoupleR p q q' Q LG hqp hq'p hcoh (fun _ _ => 1) L k κ
  rw [rowTopAgreementCoupleR p q q' Q LG hqp hq'p hcoh g L k κ, hB]
  split_ifs <;> simp

end WaveTurbulence.Flower.CohTrunk

end
