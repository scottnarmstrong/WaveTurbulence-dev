/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.CoefficientEnumeration
public import WaveTurbulence.Foundations.Spine.RA1LW.ActualTimeExpansion
public import WaveTurbulence.Foundations.RegAsymp.PhiProfile

/-! # The literal special-address expansion in the NT energy profile -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory TTree Links ClassJR WithLp

/-- The marked independent links enumerate exactly the source address set. -/
theorem prod_marked_chosenNode (Q : RegCpl) (Z : Finset (Fin 2 × TTree.Path))
    (hZ : Z ⊆ chosenSet Q.links) (f : (Fin 2 × TTree.Path) → ℂ) :
    (∏ j ∈ markedLinkIndices Q Z, f (chosenNode Q j)) = ∏ z ∈ Z, f z := by
  apply Finset.prod_bij (fun j _ => chosenNode Q j)
  · intro j hj
    exact (Finset.mem_filter.mp hj).2
  · intro i _ j _ hij
    exact chosenNode_injective Q hij
  · intro z hz
    obtain ⟨j,hj⟩ := (Set.ext_iff.mp (range_chosenNode Q) z).mpr (hZ hz)
    refine ⟨j,?_,hj⟩
    simp only [markedLinkIndices,Finset.mem_filter,Finset.mem_univ,true_and,hj,hz]
  · intro j _
    rfl

end WaveTurbulence.RA1Leafwise
