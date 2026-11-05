/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineJointFlows
import Mathlib.Tactic

/-! # Two low-degree selected atoms determine both inner joints -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Two distinct selected atoms of outer restricted degree at most three
must be exactly the two specified inner joints when every other inner atom
has degree four. This applies to both blocks and hyper-blocks. -/
theorem joints_eq_of_two_low_degrees (M : Molecule V D) {A U : Finset V} {a b x y : V}
    (hAU : A ⊆ U) (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (hxy : x ≠ y)
    (hda : M.degIn U a ≤ 3) (hdb : M.degIn U b ≤ 3)
    (hint : ∀ v ∈ A,v ≠ x → v ≠ y → M.degIn A v=4) :
    ({x,y} : Finset V)={a,b} := by
  have hj (v : V) (hv : v ∈ A) (hd : M.degIn U v ≤ 3) : v=x ∨ v=y := by
    by_contra hne
    have hd4 := hint v hv (not_or.mp hne).1 (not_or.mp hne).2
    have hle := degIn_mono M hAU v
    omega
  have hsub : ({a,b} : Finset V) ⊆ {x,y} := by
    intro v hv
    rcases mem_insert.mp hv with he | hv
    · rw [he]
      simpa only [mem_insert,mem_singleton] using hj a ha hda
    · have he := mem_singleton.mp hv
      subst v
      simpa only [mem_insert,mem_singleton] using hj b hb hdb
  exact (eq_of_subset_of_card_le hsub (by rw [card_pair hxy,card_pair hab])).symm

end WaveTurbulence.Vine
