/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeReindexedLeading
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeSourceProfile

/-! # One actual tree NT profile family, with its exact signed leading time factors -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR MainCoef WithLp

/-- The original source tree time coefficient expands in a single family of physical NT
profiles, with every integrated component classified. The family precedes physical scales,
gardens, momenta and order cutoffs; the original CTeta budget is unchanged. -/
theorem tree_profiles_with_classified_leading {η A : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A)
    (X : RegChain) (hwf : X.wf = true) (ζ : ℤˣ) :
    ∃ C : (Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset) →
        ({j : Fin (X.treeLinks ζ).length // j ∉ treeMarkedIndices (treeChosenAddress X ζ) Z.val} → ℝ) →
          ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) A (CTη η^(2*X.size+1)) (C Z)) ∧
      (∀ α t s, 0 ≤ s → s < t → t ≤ 1 → chainAtilde X ζ α t s =
        ∑ Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset,
          (∏ z ∈ Z.val, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹) *
            ∫ lam, ApproxNT.resProfile (treeMarkedIndices (treeChosenAddress X ζ) Z.val)
              (fun Ω => C Z (ofLp Ω) lam) (fun j => α (treeChosenAddress X ζ j))*e2 lam t s) ∧
      ∀ Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset,
        ∀ t s : ℝ, 0 ≤ s → s < t → t ≤ 1 →
          (∫ β, ∫ lam, C Z β lam*e2 lam t s) =
            if X.dominant = true ∧ IsSpecialSet (X.linksAt ζ (rootT ζ)) Z.val then
              (-1:ℂ)^Z.val.card*(X.JBtree 0 t s:ℂ) else 0 := by
  classical
  obtain ⟨G,hG,hF,-⟩ := tree_time_expansion_classified hη hη2 hA X hwf ζ
  have hRep (Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset) :=
    tree_sourceCoefficient_on_unmarkedLinks (hG Z.val (Finset.mem_powerset.mp Z.property))
  choose C hC hrep using hRep
  refine ⟨C,hC,?_,?_⟩
  · intro α t s hs hst ht
    rw [hF α t s hs hst ht]
    calc
      _ = ∑ Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset,
          (∏ z ∈ Z.val, PhiZ nodeSgn z (α z))*G Z.val α t s := (Finset.sum_coe_sort _ _).symm
      _ = _ := Finset.sum_congr rfl (fun Z _ =>
        treeComponent_resProfile_of_representation (Finset.mem_powerset.mp Z.property)
          (hrep Z) α t s ⟨hs.trans hst.le,ht⟩ ⟨hs,hst.le.trans ht⟩)
  · intro Z t s hs hst ht
    exact tree_reindexed_component_leading (by linarith) X hwf ζ G hG hF Z.val
      (Finset.mem_powerset.mp Z.property) (C Z) (hrep Z) hs hst ht

end WaveTurbulence.RegAsymp
