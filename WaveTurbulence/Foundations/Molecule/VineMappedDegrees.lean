/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineIncidenceMultiset
public import WaveTurbulence.Foundations.Molecule.VineIncidence
import Mathlib.Tactic

/-! # Undirected realization maps preserve internal degrees -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- An injective atom map preserves the incidence multiplicity of a bond. -/
theorem bondIncidence_map {S : Finset V} (f : V → ℕ) (hf : Set.InjOn f S)
    (e : Sym2 V) (he : ∀ x ∈ e,x ∈ S) {v : V} (hv : v ∈ S) :
    bondIncidence (Sym2.map f e) (f v)=bondIncidence e v := by
  revert he
  refine Sym2.inductionOn e ?_
  intro u w he
  have hu := he u (Sym2.mem_mk_left u w)
  have hw := he w (Sym2.mem_mk_right u w)
  have heu : f u=f v ↔ u=v := ⟨fun h => hf hu hv h,congrArg f⟩
  have hew : f w=f v ↔ w=v := ⟨fun h => hf hw hv h,congrArg f⟩
  rw [Sym2.map_mk,bondIncidence_pair,bondIncidence_pair]
  simp only [heu,hew]

/-- Internal degree is recovered from the mapped induced bond multiset,
provided the atom map is injective on the outer group. -/
theorem degreeIn_eq_mapped_bondIncidence (M : Molecule V D) {A S : Finset V} (hAS : A ⊆ S)
    (f : V → ℕ) (hf : Set.InjOn f S) {v : V} (hv : v ∈ S) :
    M.degIn A v=(((M.groupBonds A).map (Sym2.map f)).map (fun e => bondIncidence e (f v))).sum := by
  rw [degreeIn_eq_bondIncidence,Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro e he
  symm
  apply bondIncidence_map f hf e ?_ hv
  simp only [Molecule.groupBonds,Multiset.mem_map,Finset.mem_val,mem_filter,mem_univ,true_and] at he
  obtain ⟨x,⟨_hout,hg⟩,rfl⟩ := he
  intro w hw
  simp only [Molecule.ends,Sym2.mem_iff] at hw
  rcases hw with rfl | rfl
  · exact hAS hg.1
  · exact hAS hg.2

/-- The incidence sum of a literal edge list is its usual undirected degree. -/
theorem edgeList_incidence_degree (es : List (ℕ×ℕ)) (v : ℕ) :
    (((es.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ))).map
      (fun e => bondIncidence e v)).sum=edgeDegree es v := by
  simp only [Multiset.map_coe,Multiset.sum_coe,List.map_map]
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,List.sum_cons,Function.comp_apply,bondIncidence_pair,ih,edgeDegree,List.count_cons,beq_iff_eq]
    omega

end WaveTurbulence.Vine
