/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreePairEnumeration
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceAddressSingular

/-! # Actual tree address parameters commute with their original coordinate updates -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Function TTree
variable {V : Type*} [AddCommGroup V]

theorem treeChosen_injective (X : RegChain) (ζ : ℤˣ) : Function.Injective (treeChosen X ζ) := by
  intro i j he
  apply Fin.ext
  exact (idxOf_treeChosen X ζ i).symm.trans ((congrArg
    (fun z => ((X.treeLinks ζ).map Prod.fst).idxOf z) he).trans (idxOf_treeChosen X ζ j))

theorem treeParamFun_eq_zero_of_not_chosen (X : RegChain) (ζ : ℤˣ)
    (θ : Fin (X.treeLinks ζ).length → V × V) (z : Fin 1 × Path)
    (hz : z ∉ (X.treeLinks ζ).map Prod.fst) : treeParamFun X ζ θ z = 0 := by
  simp only [treeParamFun,List.idxOf_of_notMem hz,List.length_map,lt_self_iff_false,dite_false]

theorem treeParamFun_update (X : RegChain) (ζ : ℤˣ)
    (θ : Fin (X.treeLinks ζ).length → V × V) (j : Fin (X.treeLinks ζ).length) (v : V × V) :
    treeParamFun X ζ (update θ j v) = update (treeParamFun X ζ θ) (treeChosen X ζ j) v := by
  classical
  funext z
  by_cases hz : z ∈ (X.treeLinks ζ).map Prod.fst
  · obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hz
    obtain ⟨i,rfl⟩ := List.get_of_mem hl
    change treeParamFun X ζ (update θ j v) (treeChosen X ζ i) =
      update (treeParamFun X ζ θ) (treeChosen X ζ j) v (treeChosen X ζ i)
    rw [treeParamFun_chosen]
    simp only [update_apply,treeParamFun_chosen,(treeChosen_injective X ζ).eq_iff]
  · have hne : z ≠ treeChosen X ζ j := by
      intro he
      apply hz
      rw [he]
      exact List.mem_map.mpr ⟨(X.treeLinks ζ).get j,List.get_mem _ _,rfl⟩
    rw [update_of_ne hne,treeParamFun_eq_zero_of_not_chosen X ζ _ z hz,
      treeParamFun_eq_zero_of_not_chosen X ζ _ z hz]

theorem treeParamFun_zero (X : RegChain) (ζ : ℤˣ) :
    treeParamFun X ζ (0 : Fin (X.treeLinks ζ).length → V × V) = 0 := by
  funext z
  unfold treeParamFun
  split_ifs <;> rfl

theorem tree_map_finRange_chosen (X : RegChain) (ζ : ℤˣ) :
    (List.finRange (X.treeLinks ζ).length).map (treeChosen X ζ) = (X.treeLinks ζ).map Prod.fst := by
  rw [← List.ofFn_eq_map]
  change List.ofFn (fun j : Fin (X.treeLinks ζ).length => ((X.treeLinks ζ).get j).1) = _
  rw [List.ofFn_comp' (X.treeLinks ζ).get Prod.fst,List.ofFn_get]

end WaveTurbulence.RegAsymp
