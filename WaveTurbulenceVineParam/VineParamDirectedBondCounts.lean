/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamDirectedBondModel
public import WaveTurbulenceVineParam.VineParamGraphMolecule
import Mathlib.Tactic

/-! # Exact actual bond multiplicities through a directed atom/bond realization -/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract
variable {V D A β : Type*} [DecidableEq V] [Fintype D] [DecidableEq A] [Fintype β]

omit [DecidableEq V] [Fintype D] in
/-- Every bond between two atoms of S is internal to S. -/
theorem inGroup_of_ends_in_group (M : Molecule V D) (S : Finset V) {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) (e : D) (he : M.ends e=s(u,v)) : M.InGroup S e := by
  change s(M.atom e,M.atom (M.mate e))=s(u,v) at he
  rcases Sym2.eq_iff.mp he with h | h
  · exact ⟨h.1.symm ▸ hu,h.2.symm ▸ hv⟩
  · exact ⟨h.1.symm ▸ hv,h.2.symm ▸ hu⟩

/-- Internal filtering removes no actual bond between two included atoms. -/
theorem bondsBetween_internal_filter (M : Molecule V D) (S : Finset V) {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) :
    M.bondsBetween u v=((internalBondSet M S).filter (fun e => M.ends e=s(u,v))).card := by
  classical
  unfold Molecule.bondsBetween
  congr 1
  ext e
  simp only [internalBondSet,mem_filter]
  constructor
  · rintro ⟨he,hh⟩
    exact ⟨⟨he,inGroup_of_ends_in_group M S hu hv e hh⟩,hh⟩
  · rintro ⟨⟨he,_⟩,hh⟩
    exact ⟨he,hh⟩

namespace DirectedBondModel
variable {M : Molecule V D} {S : Finset V} (Q : DirectedBondModel M S A β)

/-- Unordered actual endpoints agree exactly with the model's endpoint pair. -/
theorem ends_eq_iff (e : β) (u v : A) :
    M.ends (Q.edge e).1=s((Q.atom u).1,(Q.atom v).1) ↔ s((Q.ends e).1,(Q.ends e).2)=s(u,v) := by
  change s(M.atom (Q.edge e).1,M.atom (M.mate (Q.edge e).1))=s((Q.atom u).1,(Q.atom v).1) ↔ _
  simp only [Q.tail,Q.head,Sym2.eq_iff,Q.atom_val_eq_iff]

/-- Actual multiplicity is exactly the finite count of model occurrences.
Parallel edges remain distinct; a loop still contributes one actual bond. -/
theorem bondsBetween_eq_count (u v : A) :
    M.bondsBetween (Q.atom u).1 (Q.atom v).1=
      ((univ : Finset β).filter (fun e => s((Q.ends e).1,(Q.ends e).2)=s(u,v))).card := by
  classical
  rw [bondsBetween_internal_filter M S (Q.atom u).2 (Q.atom v).2]
  let f : D → ℕ := fun e => if M.ends e=s((Q.atom u).1,(Q.atom v).1) then 1 else 0
  have hs : (∑ e ∈ internalBondSet M S,f e)=∑ e : Bond M S,f e.1 :=
    (sum_coe_sort (internalBondSet M S) f).symm
  calc
    _=(∑ e ∈ internalBondSet M S,f e) := (sum_boole _ _).symm
    _=(∑ e : Bond M S,f e.1) := hs
    _=(∑ e : β,f (Q.edge e).1) := (Equiv.sum_comp Q.edge (fun e : Bond M S => f e.1)).symm
    _=(∑ e : β,if s((Q.ends e).1,(Q.ends e).2)=s(u,v) then (1 : ℕ) else 0) := by
      apply sum_congr rfl
      intro e _
      simp only [f,Q.ends_eq_iff]
    _=_ := sum_boole _ _

/-- The canonical directed model of its own actual half-edge graph. -/
@[expose] noncomputable def graphModel [Fintype A] (ends : β → A×A) :
    DirectedBondModel (graphMolecule ends) univ A β where
  ends := ends
  atom :=
    { toFun := fun v => ⟨v,mem_univ _⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  edge := graphBondEquiv ends
  tail := fun _ => rfl
  head := fun _ => rfl

/-- The exact molecule and its finite graph have identical bond multiplicities. -/
theorem bondsBetween_eq_graph [Fintype A] (u v : A) :
    M.bondsBetween (Q.atom u).1 (Q.atom v).1=(graphMolecule Q.ends).bondsBetween u v := by
  rw [Q.bondsBetween_eq_count]
  exact ((graphModel Q.ends).bondsBetween_eq_count u v).symm

end DirectedBondModel
end WaveTurbulence.Vine.Param
