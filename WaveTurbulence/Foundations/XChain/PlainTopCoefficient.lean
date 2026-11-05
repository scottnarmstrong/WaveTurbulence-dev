/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.PlainTopPhase
public import WaveTurbulence.Foundations.XChain.ForestRootPhaseIntegral
public import WaveTurbulence.Foundations.XChain.ForestRootEpsilon
public import WaveTurbulence.Foundations.XChain.GraftKernelSummand
public import WaveTurbulence.Foundations.XChain.CumulantTreeLeafGroups
/-! The analytic tree coefficient is exactly the top factor in the canonical graft kernel. -/
public section
namespace WaveTurbulence.Induct
open Finset
open SysAPI

theorem topDecorationFactor_eq_prod_treeCoefficients {d w : ℕ} (L γ δ : ℝ) (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hplain : ∀ B, (low B).IsPlain) (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n)
    (p : ℕ) (t s : ℝ) :
    topDecorationFactor L γ δ sig top P low hsig κ.1 0 p t s =
      ∏ j, topTreeCoefficient L γ δ p top sig n κ (fun _ => t) j := by
  have hp := (graftTopPhaseIntegral_of_plain L γ δ sig top P low hsig hplain
    (fun a => latticePoint L (κ.1 a)) p t s).trans
      (forestPhaseIntegral_eq_roots L γ δ top sig κ.1 p t)
  have he := forest_epsProd_eq_roots top κ.1
  have hc : (∏ j, topTreeCoefficient L γ δ p top sig n κ (fun _ => t) j) =
      (∏ j, epsProd (top j) (fun a => κ.1 (singleNodeToForest top j a))) *
      ∏ j, zpowSign (sig j) (timeInt L γ δ (top j) (fun a => κ.1 (singleNodeToForest top j a)) p t) := by
    simp only [topTreeCoefficient, zpowSign_mul, zpowSign_epsProd, prod_mul_distrib]
    rfl
  have hh := congrArg₂ (fun a b : ℂ => a * b) he hp
  have hzero : (fun a : GNode top => (0 : Mom d) + latticePoint L (κ.1 a)) =
      fun a => latticePoint L (κ.1 a) := funext (fun _ => zero_add _)
  unfold topDecorationFactor
  rw [hzero]
  exact hh.trans hc.symm

end WaveTurbulence.Induct
