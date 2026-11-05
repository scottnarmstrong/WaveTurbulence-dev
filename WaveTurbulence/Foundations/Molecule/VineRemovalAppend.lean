/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRemoval
import Mathlib.Tactic

/-! # Concatenating removal families intersects their surviving data -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V]

/-- An atom survives a concatenated family precisely when it survives both. -/
theorem mem_remainingAtoms_append (S : Finset V) (ps qs : List (RemovalPiece V D)) (v : V) :
    v ∈ remainingAtoms S (ps++qs) ↔ v ∈ remainingAtoms S ps ∧ v ∈ remainingAtoms S qs := by
  constructor
  · intro hv
    have hh := mem_filter.mp hv
    exact ⟨mem_filter.mpr ⟨hh.1,fun P hP => hh.2 P (List.mem_append_left _ hP)⟩,
      mem_filter.mpr ⟨hh.1,fun Q hQ => hh.2 Q (List.mem_append_right _ hQ)⟩⟩
  · rintro ⟨hp,hq⟩
    have hpp := mem_filter.mp hp
    have hqq := mem_filter.mp hq
    refine mem_filter.mpr ⟨hpp.1,?_⟩
    intro P hP
    rcases List.mem_append.mp hP with hP | hP
    · exact hpp.2 P hP
    · exact hqq.2 P hP

/-- A dart survives both families exactly when it survives their concatenation. -/
theorem keepDart_append_iff (M : Molecule V D) (S : Finset V)
    (ps qs : List (RemovalPiece V D)) (d : D) :
    KeepDart M S (ps++qs) d ↔ KeepDart M S ps d ∧ KeepDart M S qs d := by
  constructor
  · rintro ⟨hu,hv,hd⟩
    have hu' := (mem_remainingAtoms_append S ps qs _).mp hu
    have hv' := (mem_remainingAtoms_append S ps qs _).mp hv
    exact ⟨⟨hu'.1,hv'.1,fun P hP => hd P (List.mem_append_left _ hP)⟩,
      ⟨hu'.2,hv'.2,fun Q hQ => hd Q (List.mem_append_right _ hQ)⟩⟩
  · rintro ⟨⟨hu,hv,hd⟩,⟨hu',hv',hd'⟩⟩
    refine ⟨(mem_remainingAtoms_append S ps qs _).mpr ⟨hu,hu'⟩,
      (mem_remainingAtoms_append S ps qs _).mpr ⟨hv,hv'⟩,?_⟩
    intro P hP
    rcases List.mem_append.mp hP with hP | hP
    · exact hd P hP
    · exact hd' P hP

end WaveTurbulence.Vine
