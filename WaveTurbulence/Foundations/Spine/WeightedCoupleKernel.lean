/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.WeightedLeafKernel
public import WaveTurbulence.Foundations.Spine.RootChoiceSign
public import WaveTurbulence.Foundations.Spine.LeafwisePointwise
/-! Actual weighted couple kernels are finite sums of individually modified source kernels. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem weighted_coupleLeaves {d : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L)
    (γ δ : ℝ) (LG : LayeredGarden 2) (hp : LG.garden.IsPlain) (H : LeafProfiles 2 d)
    (m : ℕ) (B : RootWeightChoices LG.garden d m → (Fin 2 × TTree.Path) → NNReal)
    (hH : ∀ c, LeafwiseControlled LG (rootModifiedProfiles LG.garden hp H c) (B c))
    (t s : ℝ) (k : Mom d) :
    ((jbr k ^ (4 * m) : ℝ) : ℂ) * coupleLeaves L γ δ LG H t s k =
      ∑ c : RootWeightChoices LG.garden d m, ((rootChoiceSign LG.garden c : ℝ) : ℂ) *
        coupleLeaves L γ δ LG (rootModifiedProfiles LG.garden hp H c) t s k := by
  have hh := weighted_kernelLeaves L γ δ LG hp H m
    (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0
    (fun c => (hH c).summable_coset hd hL k)
  have hw : (∏ _j : Fin 2, jbr (k + latticePoint L (0 : Fin d → ℤ)) ^ (2 * m)) =
      jbr k ^ (4 * m) := by
    have hz : latticePoint L (0 : Fin d → ℤ) = (0 : Mom d) := by
      ext j
      simp [latticePoint]
    simp only [hz, add_zero, prod_const, card_univ, Fintype.card_fin]
    rw [← pow_mul]
    congr 1
    omega
  rw [hw] at hh
  exact hh

end WaveTurbulence.LGSpine
