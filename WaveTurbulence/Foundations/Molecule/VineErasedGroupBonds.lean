/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBondEdits
public import WaveTurbulence.Foundations.Molecule.VineFiniteMatching
import Mathlib.Tactic

/-! # Exact induced bond multisets after deleting one designated actual bond -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Deleting an actual bond filters out its two specified mates from the
outgoing induced representatives, retaining all other parallel occurrences. -/
theorem eraseBond_groupBonds_filter (M : Molecule V D) (e : D) (A : Finset V) :
    (Mole.eraseBond M e).groupBonds A=
      ((univ.filter (fun d => M.out d=true ∧ M.InGroup A d)).filter
        (fun d => d ≠ e ∧ d ≠ M.mate e)).val.map M.ends := by
  let f : {d : D // d ≠ e ∧ d ≠ M.mate e} ↪ D := ⟨Subtype.val,Subtype.val_injective⟩
  let U := univ.filter (fun d : {d : D // d ≠ e ∧ d ≠ M.mate e} =>
    (Mole.eraseBond M e).out d=true ∧ (Mole.eraseBond M e).InGroup A d)
  let T := (univ.filter (fun d => M.out d=true ∧ M.InGroup A d)).filter
    (fun d => d ≠ e ∧ d ≠ M.mate e)
  have hmap : U.map f=T := by
    ext d
    constructor
    · intro hd
      obtain ⟨x,hx,rfl⟩ := mem_map.mp hd
      have hh := (mem_filter.mp hx).2
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hh⟩,x.2⟩
    · intro hd
      have hh := mem_filter.mp hd
      refine mem_map.mpr ⟨⟨d,hh.2⟩,?_,rfl⟩
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hh.1).2⟩
  have hv := congrArg Finset.val hmap
  rw [map_val] at hv
  have heq := congrArg (Multiset.map M.ends) hv
  rw [Multiset.map_map] at heq
  have hends : (Mole.eraseBond M e).ends=M.ends ∘ f := by
    funext x
    simp only [Molecule.ends,Mole.eraseBond,Function.comp_apply]
    rfl
  change U.val.map (Mole.eraseBond M e).ends=T.val.map M.ends
  rw [hends]
  exact heq

end WaveTurbulence.Vine
