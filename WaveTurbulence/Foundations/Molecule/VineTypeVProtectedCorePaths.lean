/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineTypeVOtherBranchPaths
public import WaveTurbulence.Foundations.Molecule.VineProtectedCoreBackbones
public import WaveTurbulence.Foundations.Molecule.VineCoreSinglePaths
import Mathlib.Tactic

/-! # Retained type-V core edges lift outside another removed branch -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A protected type-V core edge expands to a path outside the other
branch. The shared joint bond is excluded; all source rail slots survive. -/
theorem VineRealization.typeV_other_branch_core_edge {M : Molecule V D}
    {B : Finset V} {a b : V} (R : VineRealization M .V B a b) (hB : M.IsBlock B a b)
    (hM : M.IsMolecule) (A : Finset V) (hAB : A ∩ B={a,b}) (k : ℕ) (hk : R.k=[k])
    (i j : Fin 9) (he : (i.1,j.1) ∈ protectedCoreBonds .V {0,1}) :
    Relation.EqvGen (ProtectedSingleAdj M B A a b) (R.coreAtom i).1 (R.coreAtom j).1 := by
  have hsingle := (List.mem_filter.mp he).1
  have hm := (List.mem_filter.mp hsingle).1
  have hc : VineType.V.template.bonds.count (i.1,j.1)+VineType.V.template.bonds.count (j.1,i.1)=1 :=
    of_decide_eq_true (List.mem_filter.mp hsingle).2
  have hguard : ¬(i.1 ∈ ({0,1} : Finset ℕ) ∧ j.1 ∈ ({0,1} : Finset ℕ)) :=
    of_decide_eq_true (List.mem_filter.mp he).2
  have hij : i ≠ j := by
    intro heq
    subst j
    have hz := template_no_loop_counts .V i
    omega
  by_cases hslot : (i.1,j.1)=(2,4) ∨ (i.1,j.1)=(3,5)
  · have hp := R.typeV_other_branch_slot_paths hB hM A hAB k hk
    rcases hslot with heq | heq
    · have hi : i=(2 : Fin 9) := Fin.ext (congrArg Prod.fst heq)
      have hj : j=(4 : Fin 9) := Fin.ext (congrArg Prod.snd heq)
      simpa only [hi,hj] using hp.1
    · have hi : i=(3 : Fin 9) := Fin.ext (congrArg Prod.fst heq)
      have hj : j=(5 : Fin 9) := Fin.ext (congrArg Prod.snd heq)
      simpa only [hi,hj] using hp.2
  · have hd := R.single_core_untouched i j hij hc hm (by
      intro s hs
      have hs' : s=((2,4),(3,5)) := by simpa only [VineType.template,List.mem_singleton] using hs
      subst s
      exact not_or.mp hslot)
    have hnot : ¬((R.coreAtom i).1 ∈ A ∧ (R.coreAtom j).1 ∈ A) := by
      intro hh
      have hi := (R.mem_other_branch_iff hB A hAB (R.coreAtom i).2).mp hh.1
      have hj := (R.mem_other_branch_iff hB A hAB (R.coreAtom j).2).mp hh.2
      rw [R.label_coreAtom i] at hi
      rw [R.label_coreAtom j] at hj
      simp only [mem_insert,mem_singleton] at hguard
      omega
    exact Relation.EqvGen.rel _ _ ⟨hd,other_branch_atoms_survive hAB (R.coreAtom i).2,
      other_branch_atoms_survive hAB (R.coreAtom j).2,hnot⟩

end WaveTurbulence.Vine
