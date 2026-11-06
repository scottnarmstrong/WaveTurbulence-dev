/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.CoefficientEnumeration
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceParameterCongruence

/-! # Updating original link parameters equals updating their chosen source addresses -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Function

variable {V : Type*} [AddCommGroup V]

/-- The source address parameter function is exactly zero away from the
original chosen-node set; its definition is not a surrogate extension. -/
theorem paramFun_eq_zero_of_not_chosen (Q : RegCpl) (θ : Fin Q.links.length → V × V)
    (z : Fin 2 × TTree.Path) (hz : z ∉ chosenSet Q.links) : paramFun Q θ z = 0 := by
  have hm : z ∉ Q.links.map Prod.fst := by
    intro hm
    apply hz
    exact List.mem_toFinset.mpr hm
  have he := List.idxOf_of_notMem hm
  simp only [paramFun,he,List.length_map,lt_self_iff_false,dite_false]

/-- An update in the original finite link coordinates becomes precisely
one update at its chosen node, with no effect on the other addresses. -/
theorem paramFun_update (Q : RegCpl) (θ : Fin Q.links.length → V × V)
    (j : Fin Q.links.length) (v : V × V) :
    paramFun Q (update θ j v) = update (paramFun Q θ) (chosenNode Q j) v := by
  classical
  funext z
  by_cases hz : z ∈ chosenSet Q.links
  · obtain ⟨l,hl⟩ := (show z ∈ Set.range (chosenNode Q) from by
      rw [range_chosenNode]; exact hz)
    subst z
    rw [paramFun_chosen]
    simp only [update_apply,paramFun_chosen,(chosenNode_injective Q).eq_iff]
  · have hne : z ≠ chosenNode Q j := by
      intro he
      apply hz
      rw [he]
      have hm : chosenNode Q j ∈ Set.range (chosenNode Q) := ⟨j,rfl⟩
      rw [range_chosenNode] at hm
      exact hm
    rw [update_of_ne hne,paramFun_eq_zero_of_not_chosen Q _ z hz,
      paramFun_eq_zero_of_not_chosen Q _ z hz]

/-- The literal zero extension of zero link coordinates is zero everywhere. -/
theorem paramFun_zero (Q : RegCpl) : paramFun Q (0 : Fin Q.links.length → V × V) = 0 := by
  funext z
  unfold paramFun
  split_ifs <;> rfl

end WaveTurbulence.RA1Leafwise
