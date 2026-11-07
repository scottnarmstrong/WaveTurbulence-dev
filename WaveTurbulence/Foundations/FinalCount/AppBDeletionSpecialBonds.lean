/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBDeletionDegrees
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderRestriction
import Mathlib.Tactic

/-! # Exact special-bond effects computed in the old graph

The predicate below uses only old degrees, old bond multiplicities, and
old incidences into the deleted set. It contains no post graph statistic.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Old-data test for becoming a special bond after deletion. -/
def AppbErasureSpecial (M : Molecule V D) (Y : Finset V) (x : D) : Prop :=
  M.out x = true ∧
  M.deg (M.atom x) = 3 + (Degen.removedDartsAt M Y (M.atom x)).card ∧
  M.deg (M.atom (M.mate x)) = 3 + (Degen.removedDartsAt M Y (M.atom (M.mate x))).card ∧
  ∃ a ∈ M.atoms \ Y, ∃ b ∈ M.atoms \ Y,
    a ≠ b ∧ a ≠ M.atom x ∧ a ≠ M.atom (M.mate x) ∧
    b ≠ M.atom x ∧ b ≠ M.atom (M.mate x) ∧
    M.bondsBetween (M.atom x) (M.atom (M.mate x)) = 1 ∧
    M.bondsBetween (M.atom x) a = 2 ∧ M.bondsBetween (M.atom (M.mate x)) b = 2

/-- Exact equivalence of the actual post predicate and its old-data test. -/
theorem appb_eraseAtoms_special_iff (M : Molecule V D) (Y : Finset V)
    (x : Degen.RetainedDart M Y) :
    AppbSpecial (Degen.eraseAtoms M Y) x ↔ AppbErasureSpecial M Y x.val := by
  have h1 := appb_eraseAtoms_degree M Y x.property.1
  have h2 := appb_eraseAtoms_degree M Y x.property.2
  constructor
  · rintro ⟨ho,hd1,hd2,a,ha,b,hb,hab,ha1,ha2,hb1,hb2,hs,hA,hB⟩
    have haY := (mem_sdiff.mp ha).2
    have hbY := (mem_sdiff.mp hb).2
    refine ⟨ho,?_,?_,a,ha,b,hb,hab,ha1,ha2,hb1,hb2,?_,?_,?_⟩
    · change (Degen.eraseAtoms M Y).deg (M.atom x.val) = 3 at hd1
      omega
    · change (Degen.eraseAtoms M Y).deg (M.atom (M.mate x.val)) = 3 at hd2
      omega
    · exact (Degen.bondsBetween_erase_eq M Y x.property.1 x.property.2).symm.trans hs
    · exact (Degen.bondsBetween_erase_eq M Y x.property.1 haY).symm.trans hA
    · exact (Degen.bondsBetween_erase_eq M Y x.property.2 hbY).symm.trans hB
  · rintro ⟨ho,hd1,hd2,a,ha,b,hb,hab,ha1,ha2,hb1,hb2,hs,hA,hB⟩
    have haY := (mem_sdiff.mp ha).2
    have hbY := (mem_sdiff.mp hb).2
    refine ⟨ho,?_,?_,a,ha,b,hb,hab,ha1,ha2,hb1,hb2,?_,?_,?_⟩
    · change (Degen.eraseAtoms M Y).deg (M.atom x.val) = 3
      omega
    · change (Degen.eraseAtoms M Y).deg (M.atom (M.mate x.val)) = 3
      omega
    · exact (Degen.bondsBetween_erase_eq M Y x.property.1 x.property.2).trans hs
    · exact (Degen.bondsBetween_erase_eq M Y x.property.1 haY).trans hA
    · exact (Degen.bondsBetween_erase_eq M Y x.property.2 hbY).trans hB

/-- Old outgoing representatives passing the complete post-special test. -/
noncomputable def appbErasureSpecialBonds (M : Molecule V D) (Y : Finset V) : Finset D := by
  classical
  exact M.bonds.filter fun x => M.atom x ∉ Y ∧ M.atom (M.mate x) ∉ Y ∧ AppbErasureSpecial M Y x

/-- Exact post special-bond count, evaluated solely from the old molecule.
Every operation-specific deletion set can be substituted here. -/
theorem appb_eraseAtoms_special_count (M : Molecule V D) (Y : Finset V) :
    (appbSpecialBonds (Degen.eraseAtoms M Y)).card =
      (appbErasureSpecialBonds M Y).card := by
  classical
  unfold appbErasureSpecialBonds
  apply card_bij (fun x _ => x.val)
  · intro x hx
    have hs : AppbSpecial (Degen.eraseAtoms M Y) x := (mem_filter.mp hx).2
    have ho : M.out x.val = true := hs.1
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,ho⟩,x.property.1,x.property.2,
      (appb_eraseAtoms_special_iff M Y x).mp hs⟩
  · intro x _ y _ h; exact Subtype.ext h
  · intro x hx
    obtain ⟨hx,h1,h2,hs⟩ := mem_filter.mp hx
    refine ⟨⟨x,h1,h2⟩,?_,rfl⟩
    exact mem_filter.mpr ⟨mem_univ _,(appb_eraseAtoms_special_iff M Y ⟨x,h1,h2⟩).mpr hs⟩

end WaveTurbulence.Mole
