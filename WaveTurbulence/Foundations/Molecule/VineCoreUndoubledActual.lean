/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineUndoubledCore
import Mathlib.Tactic

/-! # Exceptional undoubled core atoms remain intrinsically undoubled -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The doubled partner of a fresh atom is fresh in the same allocation. -/
theorem VineRealization.fresh_double_partner_fresh (M : Molecule V D)
    (hM : M.IsMolecule) {X : VineType} {S : Finset V} {a b u v : V}
    (R : VineRealization M X S a b) (hu : u ∈ S) (hf : X.template.n ≤ R.f u)
    (T : TwoIncidences M u v) : X.template.n ≤ R.f v := by
  obtain ⟨A,i,hi,hin,he⟩ := R.fresh_slot hu hf
  have hn : X.template.n ≤ (A.pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n := by
    rw [fold_insertRungs_atoms]; omega
  rcases he with rfl | rfl
  · have hv := A.Q.upper_double_neighbor M hM A.frame.upper_injective i hi hin T
    rw [hv,(A.labels i hi hin).2]; omega
  · have hv := A.Q.lower_double_neighbor M hM A.frame.lower_injective i hi hin T
    rw [hv,(A.labels i hi hin).1]; omega

/-- The finite-core undoubled condition is an actual intrinsic condition. -/
theorem VineRealization.core_undoubled_actual (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hB : M.IsBlock S a b) (i : Fin X.template.n) (hi : 2 ≤ i.1)
    (hcore : CoreUndoubled X i) : CoherenceUndoubled M S a b (R.coreAtom i).1 := by
  refine ⟨R.core_interior hB i hi,?_⟩
  intro v hd
  obtain ⟨hu,hv,hne,⟨T⟩⟩ := hd
  have hvo : R.f v<X.template.n := by
    by_contra h
    have hh := R.fresh_double_partner_fresh M hM hv.1 (by omega) T.mates
    rw [R.label_coreAtom] at hh
    exact Nat.not_le_of_gt i.2 hh
  have hv2 : 2 ≤ R.f v := by
    have hh := realization_index_lt_two_iff R hB hv.1
    exact Nat.le_of_not_gt (fun h => (hh.mp h).elim hv.2.1 hv.2.2)
  have hij : i ≠ ⟨R.f v,hvo⟩ := by
    intro he
    have hh := congrArg Fin.val he
    have hh' : (R.coreAtom i).1=v := R.injOn (R.coreAtom i).2 hv.1
      ((R.label_coreAtom i).trans hh)
    exact hne hh'
  have hlo := twoIncidences_pair_degree_ge_two M T
  have hhi := R.old_pair_degree_le (R.coreAtom i).2 hv.1 hne
    (by rw [R.label_coreAtom]; exact i.2) hvo
  rw [R.label_coreAtom] at hhi
  have hh := hcore ⟨R.f v,hvo⟩ hv2 hij
  change X.template.bonds.count (i.1,R.f v)+X.template.bonds.count (R.f v,i.1)<2 at hh
  omega

end WaveTurbulence.Vine
