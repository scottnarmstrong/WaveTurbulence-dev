/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineErasedGroupBonds
import Mathlib.Tactic

/-! # A designated bond deletion removes exactly one undirected occurrence -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An outgoing designated internal bond is one multiset occurrence,
independently of any other bond with the same endpoints. -/
theorem eraseBond_groupBonds_cons_of_out (M : Molecule V D) (e : D) (A : Finset V)
    (hout : M.out e=true) (he : M.InGroup A e) :
    M.ends e ::ₘ (Mole.eraseBond M e).groupBonds A=M.groupBonds A := by
  let T := univ.filter (fun d => M.out d=true ∧ M.InGroup A d)
  have heT : e ∈ T := mem_filter.mpr ⟨mem_univ _,hout,he⟩
  have hmnot : M.mate e ∉ T := by
    intro hh
    have ho := (mem_filter.mp hh).2.1
    rw [M.out_mate,hout] at ho
    cases ho
  have hf : T.filter (fun d => d ≠ e ∧ d ≠ M.mate e)=T.erase e := by
    ext d
    constructor
    · intro hd
      have hh := mem_filter.mp hd
      exact mem_erase.mpr ⟨hh.2.1,hh.1⟩
    · intro hd
      have hh := mem_erase.mp hd
      exact mem_filter.mpr ⟨hh.2,hh.1,fun hdm => hmnot (hdm ▸ hh.2)⟩
  rw [eraseBond_groupBonds_filter]
  change M.ends e ::ₘ (T.filter (fun d => d ≠ e ∧ d ≠ M.mate e)).val.map M.ends=T.val.map M.ends
  rw [hf,erase_val]
  have hh := congrArg (Multiset.map M.ends) (Multiset.cons_erase (mem_val.mpr heT))
  simpa only [Multiset.map_cons] using hh

/-- The erased induced multiset is independent of which mate represents
the designated deleted bond. -/
theorem eraseBond_mate_groupBonds (M : Molecule V D) (e : D) (A : Finset V) :
    (Mole.eraseBond M (M.mate e)).groupBonds A=(Mole.eraseBond M e).groupBonds A := by
  rw [eraseBond_groupBonds_filter,eraseBond_groupBonds_filter,M.mate_mate]
  congr 2
  ext d
  simp only [mem_filter]
  tauto

/-- Deleting an internal bond removes one occurrence of its undirected
endpoint pair, in either orientation and even in the presence of parallel bonds. -/
theorem eraseBond_groupBonds_cons (M : Molecule V D) (e : D) (A : Finset V)
    (he : M.InGroup A e) :
    M.ends e ::ₘ (Mole.eraseBond M e).groupBonds A=M.groupBonds A := by
  by_cases hout : M.out e=true
  · exact eraseBond_groupBonds_cons_of_out M e A hout he
  · have hmout : M.out (M.mate e)=true := by
      rw [M.out_mate]
      have ho : M.out e=false := Bool.eq_false_iff.mpr hout
      rw [ho]
      rfl
    have hmgroup : M.InGroup A (M.mate e) := by
      exact ⟨he.2,by rw [M.mate_mate]; exact he.1⟩
    have hh := eraseBond_groupBonds_cons_of_out M (M.mate e) A hmout hmgroup
    rw [eraseBond_mate_groupBonds] at hh
    have heq : M.ends (M.mate e)=M.ends e := by
      simp only [Molecule.ends,M.mate_mate,Sym2.eq_swap]
    rwa [heq] at hh

end WaveTurbulence.Vine
