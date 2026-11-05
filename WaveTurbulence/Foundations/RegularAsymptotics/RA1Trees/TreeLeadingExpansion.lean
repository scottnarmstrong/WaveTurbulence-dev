/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeActualRegularizedLimit
public import WaveTurbulence.Foundations.RegAsymp.TreeCoefficientLimit

/-! # Original tree expansion with every integrated coefficient identified -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open ClassJR MainCoef

/-- MAINCOEF-T and the actual tree regularization identify the integrated original
components. The family is chosen once before every physical garden and scale. -/
theorem tree_time_expansion_with_regularized_leading {η A : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A)
    (X : RegChain) (hwf : X.wf = true) (ζ : ℤˣ) :
    ∃ G : Finset ClassJR.Addr → (ClassJR.Addr → ℝ) → ℝ → ℝ → ℂ,
      (∀ Z ⊆ ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)),
        MCRep (1-η/8) (η/4) (1-η/2) A (CTη η^(2*X.size+1))
          (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)) \ Z : Finset ClassJR.Addr) (G Z)) ∧
      (∀ α t s, 0 ≤ s → s < t → t ≤ 1 → chainAtilde X ζ α t s =
        ∑ Z ∈ (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset,
          (∏ z ∈ Z, PhiZ nodeSgn z (α z))*G Z α t s) ∧
      ∀ Z ⊆ ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)),
        ∀ t s : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∀ α₀ : ClassJR.Addr → ℝ,
          Cancel.mint (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)) \ Z)
            (fun α => G Z α t s) α₀ = treeRegularizedLeading Z X ζ t s := by
  obtain ⟨G,hG,hF⟩ := maincoefT_DH23_B2 hη hη2 hA X hwf ζ
  refine ⟨G,hG,hF,?_⟩
  intro Z hZ t s hs hst ht α₀
  exact tree_component_mint_eq_of_tendsto (by linarith) nodeSgn_eq hZ hG hF hs hst ht
    (actual_tree_regularized_limit Z X hwf ζ hs hst ht) α₀

end WaveTurbulence.RegAsymp
