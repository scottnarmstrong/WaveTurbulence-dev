/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoherence
public import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-! # Coherence does not depend on the ordering of groups or their atoms -/

public section
namespace WaveTurbulence.Vine
variable {A L : Type*} [DecidableEq L]

omit [DecidableEq L] in
/-- A group's source coherence condition depends only on its atoms. -/
theorem groupCoherent_iff_of_mem_iff (layer : A → L) {g h : List A}
    (he : ∀ x,x ∈ g ↔ x ∈ h) : GroupCoherent layer g ↔ GroupCoherent layer h := by
  constructor
  · intro hg x hx y hy
    exact hg x ((he x).mpr hx) y ((he y).mpr hy)
  · intro hh x hx y hy
    exact hh x ((he x).mp hx) y ((he y).mp hy)

omit [DecidableEq L] in
/-- Reordering the atoms of a group preserves coherence. -/
theorem groupCoherent_iff_of_perm (layer : A → L) {g h : List A} (hp : g.Perm h) :
    GroupCoherent layer g ↔ GroupCoherent layer h :=
  groupCoherent_iff_of_mem_iff layer (fun _ => hp.mem_iff)

/-- Reordering groups leaves the incoherency index unchanged. -/
theorem incoherencyIndex_eq_of_perm (layer : A → L) {g h : List (List A)}
    (hp : g.Perm h) : incoherencyIndex layer g=incoherencyIndex layer h := by
  exact (hp.filter _).length_eq

/-- Replacing each group by a list with the same atoms preserves the index.
This is an ordering helper; realization independence additionally requires
identifying the actual source groups. -/
theorem incoherencyIndex_eq_of_group_mem_iff (layer : A → L)
    {g h : List (List A)} (hp : List.Forall₂ (fun s t => ∀ x,x ∈ s ↔ x ∈ t) g h) :
    incoherencyIndex layer g=incoherencyIndex layer h := by
  induction hp with
  | nil => rfl
  | @cons a b g h hab _hgh ih =>
    have he := groupCoherent_iff_of_mem_iff layer hab
    by_cases hc : GroupCoherent layer a
    · have hc' := he.mp hc
      simpa [incoherencyIndex,hc,hc'] using ih
    · have hc' : ¬GroupCoherent layer b := fun hb => hc (he.mpr hb)
      simpa [incoherencyIndex,hc,hc'] using congrArg Nat.succ ih

end WaveTurbulence.Vine
