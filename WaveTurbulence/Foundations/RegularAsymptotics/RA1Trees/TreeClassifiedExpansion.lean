/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeLeadingExpansion
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeLeadingClassification

/-! # Full source classification of the original MAINCOEF-T expansion components -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open ClassJR MainCoef

/-- Every actual tree component has the original signed JBtree leading coefficient,
with zero for non-dominant/non-special terms. The one family precedes all physical data. -/
theorem tree_time_expansion_classified {η A : ℝ}
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
            (fun α => G Z α t s) α₀ =
              if X.dominant = true ∧ IsSpecialSet (X.linksAt ζ (rootT ζ)) Z then
                (-1:ℂ)^Z.card*(X.JBtree 0 t s:ℂ) else 0 := by
  obtain ⟨G,hG,hF,hLeading⟩ := tree_time_expansion_with_regularized_leading hη hη2 hA X hwf ζ
  refine ⟨G,hG,hF,?_⟩
  intro Z hZ t s hs hst ht α₀
  rw [hLeading Z hZ t s hs hst ht α₀]
  exact treeRegularizedLeading_eq_if_special X ζ Z hZ hs hst ht

end WaveTurbulence.RegAsymp
