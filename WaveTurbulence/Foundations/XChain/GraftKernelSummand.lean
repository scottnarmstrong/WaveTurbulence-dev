/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftKernelWeights
public import WaveTurbulence.Foundations.XChain.GraftMarkedPhaseIntegral
public import WaveTurbulence.Foundations.XChain.GraftEpsilon
public import WaveTurbulence.Foundations.XChain.GraftGenDecorationEquiv
/-! Literal factors of kernelK used by the generic graft sum identity. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def kernelDecorationFactor {d w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d n nfl) : ℂ :=
  (epsDec LG.garden κ.1 : ℂ) *
    phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
    ∏ ℓ ∈ inputLeaves LG.garden,
      (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

noncomputable def topDecorationFactor {d w : ℕ} (L γ δ : ℝ) (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (κ : GNode top → (Fin d → ℤ)) (k₀ : Mom d) (p t s : ℝ) : ℂ :=
  (((∏ b : GBranch top, epsCoef (κ (b.child 0)) (κ (b.child 1)) (κ (b.child 2))) : ℝ) : ℂ) *
    graftTopPhaseIntegral L γ δ sig top P low hsig (fun a => k₀ + latticePoint L (κ a)) p t s

theorem kernelK_eq_tsum_factors {d w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelK L γ δ F LG up s k₀ n nfl =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d n nfl, kernelDecorationFactor L γ δ F LG up s k₀ κ := rfl

theorem mul_three_prod {β : Type*} [Fintype β] (a b : ℂ) (e f g : β → ℂ) :
    (a * ∏ j, e j) * (b * ∏ j, f j) * (∏ j, g j) =
      (a * b) * ∏ j, e j * f j * g j := by
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end WaveTurbulence.Induct
