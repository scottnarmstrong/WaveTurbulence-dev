/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionMolecule
import Mathlib.Tactic

/-! # Directional degree caps for source bond reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_reinsert_direction_card_le (M : Molecule V D) (Y : Finset V) (a b : V)
    (ref : Bool → D) (hat : ∀ t,M.atom (ref t) = if t then a else b)
    (hdir : ∀ t,M.out (ref t) = t) (hdel : ∀ t,M.atom (M.mate (ref t)) ∈ Y)
    (v : V) (dir : Bool) :
    ((((addBond (Degen.eraseAtoms M Y) a b).dartsAt v).filter
      (fun x => (addBond (Degen.eraseAtoms M Y) a b).out x = dir)).card) ≤
      (((M.dartsAt v).filter (fun x => M.out x = dir)).card) := by
  classical
  let f : Degen.RetainedDart M Y ⊕ Bool → D := Sum.elim Subtype.val ref
  apply card_le_card_of_injOn f
  · intro x hx
    obtain ⟨hx,hd⟩ := mem_filter.mp hx
    have hv := (mem_filter.mp hx).2
    rcases x with x | t
    · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hv⟩,hd⟩
    · have ha : M.atom (ref t) = v := by
        rw [hat]
        cases t <;> exact hv
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,ha⟩,(hdir t).trans hd⟩
  · intro x hx y hy he
    rcases x with x | t <;> rcases y with y | u
    · exact congrArg Sum.inl (Subtype.ext he)
    · have hn : x.val ≠ ref u := by
        intro hh
        exact x.property.2 (hh ▸ hdel u)
      exact (hn he).elim
    · have hn : y.val ≠ ref t := by
        intro hh
        exact y.property.2 (hh ▸ hdel t)
      exact (hn he.symm).elim
    · have hh := congrArg M.out he
      change M.out (ref t) = M.out (ref u) at hh
      rw [hdir,hdir] at hh
      exact congrArg Sum.inr hh

/-- Both incoming and outgoing degree caps are inherited by replacing
removed boundary darts of the same direction. Nonsaturation is a separate
component statement and is not assumed or claimed here. -/
theorem appb_reinsert_degree_caps (M : Molecule V D) (hM : M.IsMolecule)
    (Y : Finset V) (a b : V) (ha : a ∈ M.atoms) (hb : b ∈ M.atoms)
    (ref : Bool → D) (hat : ∀ t,M.atom (ref t) = if t then a else b)
    (hdir : ∀ t,M.out (ref t) = t) (hdel : ∀ t,M.atom (M.mate (ref t)) ∈ Y) :
    ∀ v ∈ (addBond (Degen.eraseAtoms M Y) a b).atoms,
      ((((addBond (Degen.eraseAtoms M Y) a b).dartsAt v).filter
        (fun x => (addBond (Degen.eraseAtoms M Y) a b).out x = true)).card ≤ 2) ∧
      ((((addBond (Degen.eraseAtoms M Y) a b).dartsAt v).filter
        (fun x => (addBond (Degen.eraseAtoms M Y) a b).out x = false)).card ≤ 2) := by
  intro v hv
  have hvM : v ∈ M.atoms := by
    change v ∈ insert a (insert b (M.atoms \ Y)) at hv
    rcases mem_insert.mp hv with rfl | hv
    · exact ha
    rcases mem_insert.mp hv with rfl | hv
    · exact hb
    · exact (mem_sdiff.mp hv).1
  exact ⟨(appb_reinsert_direction_card_le M Y a b ref hat hdir hdel v true).trans (hM.1 v hvM).1,
    (appb_reinsert_direction_card_le M Y a b ref hat hdir hdel v false).trans (hM.1 v hvM).2⟩

end WaveTurbulence.Mole
