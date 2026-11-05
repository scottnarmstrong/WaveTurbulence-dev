/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Param
public import WaveTurbulence.Foundations.RegAsymp.CoefficientEnumeration

/-! # The actual selected-address enumeration for J3 coefficients

The NT variable type is exactly the unmarked subtype of the independent
link indices. No bound on derivatives is lost in identifying these variables.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links ClassJR MeasureTheory TTree

/-- Injectivity of the actual link-selected addresses. -/
theorem chosenNode_injective (Q : RegCpl) : Function.Injective (chosenNode Q) := by
  intro i j hij
  have hh := congrArg (paramFun Q (fun l => ((l.val:ℤ),(0:ℤ)))) hij
  rw [paramFun_chosen,paramFun_chosen] at hh
  exact Fin.ext (Int.ofNat_inj.mp (congrArg Prod.fst hh))

theorem range_chosenNode (Q : RegCpl) : Set.range (chosenNode Q) = ↑(chosenSet Q.links) := by
  ext v
  constructor
  · rintro ⟨j,rfl⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨Q.links.get j,List.get_mem _ _,rfl⟩)
  · intro hv
    obtain ⟨x,hx,hxv⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hx
    exact ⟨j,by simpa only [chosenNode,hj] using hxv⟩

/-- The marked independent indices of the actual special-address set. -/
def markedLinkIndices (Q : RegCpl) (Z : Finset (Fin 2 × Path)) : Finset (Fin Q.links.length) :=
  Finset.univ.filter (fun j => chosenNode Q j ∈ Z)

theorem range_unmarked_chosenNode (Q : RegCpl) (Z : Finset (Fin 2 × Path)) :
    Set.range (fun j : {j : Fin Q.links.length // j ∉ markedLinkIndices Q Z} => chosenNode Q j) =
      ↑(chosenSet Q.links \ Z) := by
  ext v
  constructor
  · rintro ⟨j,rfl⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨?_,?_⟩
    · exact (Set.ext_iff.mp (range_chosenNode Q) _).mp ⟨j.val,rfl⟩
    · simpa only [markedLinkIndices,Finset.mem_filter,Finset.mem_univ,true_and] using j.property
  · intro hv
    obtain ⟨hchosen,hnot⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨j,hj⟩ := (Set.ext_iff.mp (range_chosenNode Q) v).mpr hchosen
    refine ⟨⟨j,?_⟩,hj⟩
    simpa only [markedLinkIndices,Finset.mem_filter,Finset.mem_univ,true_and,hj] using hnot

/-- The source coefficient representation is available on the literal NT
unmarked-link variable type, with the original constants. -/
theorem sourceCoefficient_on_unmarkedLinks {Q : RegCpl} {Z : Finset (Fin 2 × Path)}
    {θ a b A N : ℝ} {F : ((Fin 2 × Path) → ℝ) → ℝ → ℝ → ℂ}
    (hF : MCRep θ a b A N ↑(chosenSet Q.links \ Z) F) :
    ∃ C : ({j : Fin Q.links.length // j ∉ markedLinkIndices Q Z} → ℝ) → ℝ × ℝ → ℂ,
      SRep θ a b A N C ∧
      ∀ α t s, t ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 →
        F α t s = ∫ lam, C (fun j => α (chosenNode Q j)) lam*e2 lam t s := by
  exact mcRep_on_enumeration hF _ (fun i j h => Subtype.ext (chosenNode_injective Q h))
    (range_unmarked_chosenNode Q Z)

end WaveTurbulence.RegAsymp
