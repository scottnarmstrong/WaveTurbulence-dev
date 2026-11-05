/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineActualCorePairCounts
public import WaveTurbulence.Foundations.Molecule.VineDoubleRemovalRails
public import WaveTurbulence.Foundations.Molecule.VineUntouchedCoreEdges
import Mathlib.Tactic

/-! # Single old-core edges retain their intrinsic degree after expansion -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- An actual bond supplies a positive degree in its two-endpoint group. -/
theorem pair_degree_pos_of_adj (M : Molecule V D) {u v : V} (h : M.Adj u v) :
    0<M.degIn {u,v} u := by
  obtain ⟨d,hdu,hdv⟩ := h
  apply card_pos.mpr
  refine ⟨d,mem_filter.mpr ⟨(Mole.mem_dartsAt M u d).mpr hdu,?_,?_⟩⟩
  · exact hdu.symm ▸ mem_insert_self _ _
  · exact hdv.symm ▸ mem_insert_of_mem (mem_singleton_self _)

omit [DecidableEq D] in
/-- If an old core pair is single and remains adjacent, it is still a
single edge in the actual graph; other inserted rungs cannot add a copy. -/
theorem VineRealization.single_core_of_adj {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (i j : Fin X.template.n) (hne : i ≠ j)
    (hc : X.template.bonds.count (i.1,j.1)+X.template.bonds.count (j.1,i.1)=1)
    (ha : M.Adj (R.coreAtom i).1 (R.coreAtom j).1) :
    SingleGroupAdj M S (R.coreAtom i).1 (R.coreAtom j).1 := by
  have huv : (R.coreAtom i).1 ≠ (R.coreAtom j).1 := by
    intro he
    have hh := congrArg R.f he
    rw [R.label_coreAtom,R.label_coreAtom] at hh
    exact hne (Fin.ext hh)
  have hd := R.old_pair_degree_le (R.coreAtom i).2 (R.coreAtom j).2 huv
    (by rw [R.label_coreAtom]; exact i.2) (by rw [R.label_coreAtom]; exact j.2)
  rw [R.label_coreAtom,R.label_coreAtom,hc] at hd
  have hp := pair_degree_pos_of_adj M ha
  exact ⟨(R.coreAtom i).2,(R.coreAtom j).2,huv,ha,by omega⟩

/-- A core single edge outside all marked slots survives as an actual
single edge at arbitrary rung counts. -/
theorem VineRealization.single_core_untouched {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (i j : Fin X.template.n) (hne : i ≠ j)
    (hc : X.template.bonds.count (i.1,j.1)+X.template.bonds.count (j.1,i.1)=1)
    (hm : (i.1,j.1) ∈ X.template.bonds)
    (he : ∀ s ∈ X.template.slots,(i.1,j.1) ≠ s.1 ∧ (i.1,j.1) ≠ s.2) :
    SingleGroupAdj M S (R.coreAtom i).1 (R.coreAtom j).1 :=
  R.single_core_of_adj i j hne hc (R.core_untouched_adj i j hm he)

end WaveTurbulence.Vine
