/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeClassifiedExpansion
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeCoefficientEnumeration
public import WaveTurbulence.Foundations.RegAsymp.FiniteVariableIntegral

/-! # The original reindexed NT profile has the exact signed tree time integral -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR MainCoef

/-- Reindexing the actual active tree variables preserves the leading coefficient.
The only representation data are the original MAINCOEF-T fields and the literal Fourier
representation of its selected component; no limit identity is assumed. -/
theorem tree_reindexed_component_leading {θ a b Agev N : ℝ} (hθ : 0 ≤ θ)
    (X : RegChain) (hwf : X.wf = true) (ζ : ℤˣ)
    (G : Finset ClassJR.Addr → (ClassJR.Addr → ℝ) → ℝ → ℝ → ℂ)
    (hG : ∀ Z ⊆ ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)),
      MCRep θ a b Agev N (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)) \ Z : Finset ClassJR.Addr) (G Z))
    (hF : ∀ α t s, 0 ≤ s → s < t → t ≤ 1 → chainAtilde X ζ α t s =
      ∑ Z ∈ (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset,
        (∏ z ∈ Z, PhiZ nodeSgn z (α z))*G Z α t s)
    (Z : Finset ClassJR.Addr) (hZ : Z ⊆ ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)))
    (C : ({j : Fin (X.treeLinks ζ).length // j ∉ treeMarkedIndices (treeChosenAddress X ζ) Z} → ℝ) →
      ℝ × ℝ → ℂ)
    (hRep : ∀ α t s, t ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 →
      G Z α t s = ∫ lam, C (fun j => α (treeChosenAddress X ζ j)) lam * e2 lam t s)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    (∫ β, ∫ lam, C β lam * e2 lam t s) =
      if X.dominant = true ∧ IsSpecialSet (X.linksAt ζ (rootT ζ)) Z then
        (-1:ℂ)^Z.card*(X.JBtree 0 t s:ℂ) else 0 := by
  have hm := tree_component_mint_eq_of_tendsto hθ nodeSgn_eq hZ hG hF hs hst ht
    (actual_tree_regularized_limit Z X hwf ζ hs hst ht) (0 : ClassJR.Addr → ℝ)
  let f := fun j : {j : Fin (X.treeLinks ζ).length // j ∉ treeMarkedIndices (treeChosenAddress X ζ) Z} =>
    treeChosenAddress X ζ j
  have hf : Function.Injective f := (treeChosenAddress_injective X ζ).comp Subtype.val_injective
  have hr : Set.range f = (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)) \ Z : Finset ClassJR.Addr) :=
    range_treeUnmarked _ _ _ (range_treeChosenAddress X ζ)
  have hfun : (fun α => G Z α t s) = fun α => ∫ lam, C (α ∘ f) lam * e2 lam t s := by
    funext α
    exact hRep α t s ⟨hs.trans hst.le,ht⟩ ⟨hs,hst.le.trans ht⟩
  rw [hfun] at hm
  rw [mint_comp_eq_integral _ f hf hr (fun β => ∫ lam, C β lam * e2 lam t s)] at hm
  exact hm.trans (treeRegularizedLeading_eq_if_special X ζ Z hZ hs hst ht)

end WaveTurbulence.RegAsymp
