/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.WeightedDecorationSum
public import WaveTurbulence.Foundations.Spine.RootModifiedProfiles
public import WaveTurbulence.Foundations.Spine.KernelCosetDecoration
public import WaveTurbulence.Foundations.Spine.LeafwiseMajorant
public import WaveTurbulence.Foundations.RegularAsymptotics.KernelContinuity
/-! Exact root-weight redistribution for the literal source kernel, retaining all phases. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem summable_leafKernel_summand {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (hF : ∀ l ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |H l.1 (k₀ + latticePoint L n)|) :
    Summable (fun κ : GenDecoration LG.garden d nroot nfl =>
      (epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s
          (cosetDecoration LG.garden L k₀ κ.1) *
        ∏ l ∈ inputLeaves LG.garden,
          (H l.1 (cosetDecoration LG.garden L k₀ κ.1 l.toNode) : ℂ)) := by
  apply Summable.of_norm_bounded (summable_leafInputMajorant L H LG k₀ nroot nfl hlone hF)
  intro κ
  exact norm_leafKernel_summand_le_leafInputMajorant L γ δ H LG up s k₀ κ

/-- The weight transfer is an equality of actual kernels. Only convergence of the explicitly
modified leaf inputs is required; their quantitative seminorm bounds enter separately. -/
theorem weighted_kernelLeaves {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (hp : LG.garden.IsPlain) (H : LeafProfiles w d) (m : ℕ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hF : ∀ c : RootWeightChoices LG.garden d m, ∀ l ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ =>
        |rootModifiedProfiles LG.garden hp H c l.1 (k₀ + latticePoint L n)|) :
    ((∏ j, jbr (k₀ + latticePoint L (nroot j)) ^ (2 * m) : ℝ) : ℂ) *
        kernelLeaves L γ δ LG H up s k₀ nroot nfl =
      ∑ c : RootWeightChoices LG.garden d m, ((rootChoiceSign LG.garden c : ℝ) : ℂ) *
        kernelLeaves L γ δ LG (rootModifiedProfiles LG.garden hp H c) up s k₀ nroot nfl := by
  classical
  let G := LG.garden
  let a : GenDecoration G d nroot nfl → ℂ := fun κ =>
    (epsDec G κ.1 : ℂ) *
      phaseIntegral L γ δ G (kDomain LG up s) s (cosetDecoration G L k₀ κ.1)
  have hprod (J : LeafProfiles w d) (κ : GenDecoration G d nroot nfl) :
      (∏ l : ActualInputLeaves G, (J l.1.1 (cosetDecoration G L k₀ κ.1 l.1.toNode) : ℂ)) =
        ∏ l ∈ inputLeaves G, (J l.1 (cosetDecoration G L k₀ κ.1 l.toNode) : ℂ) :=
    prod_coe_sort (inputLeaves G)
      (fun l : GLeaf G.tree => (J l.1 (cosetDecoration G L k₀ κ.1 l.toNode) : ℂ))
  have hs (c : RootWeightChoices G d m) : Summable fun κ : GenDecoration G d nroot nfl =>
      a κ * ((rootChoiceSign G c : ℝ) : ℂ) *
        ∏ l : ActualInputLeaves G,
          (monomialLeafProfile (fun l : ActualInputLeaves G => H l.1.1)
            (rootCoordinateSlots G hp c) l (cosetDecoration G L k₀ κ.1 l.1.toNode) : ℂ) := by
    have hsum := summable_leafKernel_summand L γ δ LG
      (rootModifiedProfiles G hp H c) up s k₀ nroot nfl
      (card_lone_le_one_of_plain G hp) (hF c)
    have hc := hsum.mul_left ((rootChoiceSign G c : ℝ) : ℂ)
    apply hc.congr
    intro κ
    rw [← hprod]
    simp_rw [rootModifiedProfiles_input]
    dsimp only [a, G]
    ring
  have he := weighted_decoration_sum G hp (fun l : ActualInputLeaves G => H l.1.1)
    (fun κ : GenDecoration G d nroot nfl => cosetDecoration G L k₀ κ.1)
    (fun κ => isDecoration_cosetDecoration G L k₀ κ.1 κ.2.1)
    (fun j => k₀ + latticePoint L (nroot j))
    (fun κ j => by change k₀ + latticePoint L (κ.1 (GNode.root G.tree j)) = _; rw [κ.2.2.1 j])
    a m hs
  simp_rw [← rootModifiedProfiles_input] at he
  simp_rw [hprod] at he
  have he' := congrArg
    (fun z : ℂ => ((coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta) * z) he
  simpa only [kernelLeaves, a, G, mul_sum, mul_assoc, mul_left_comm, mul_comm] using he'

end WaveTurbulence.LGSpine
