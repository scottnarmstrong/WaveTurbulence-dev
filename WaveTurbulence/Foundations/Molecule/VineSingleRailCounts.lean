/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineFourIncidences
public import WaveTurbulence.Foundations.Molecule.VineAssembleIncidences
import Mathlib.Tactic

/-! # Single rail edges have exactly one actual incidence in full rung rows -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- In a full row [w,w,p,q], distinct neighboring atoms make the rail
edge v-p a single bond. This intrinsic degree fact is used to protect
backbone rails from double-bond removals. -/
theorem four_row_single_pair_degree (M : Molecule V D) (hM : M.IsMolecule)
    {v w p q : V} (R : FourIncidences M v ![w,w,p,q])
    (hvp : v ≠ p) (hwv : w ≠ v) (hwp : w ≠ p) (hqv : q ≠ v) (hqp : q ≠ p) :
    M.degIn {v,p} v=1 := by
  have hd := fourIncidences_degree M hM R ({v,p} : Finset V) (mem_insert_self _ _)
  rw [Fin.sum_univ_four] at hd
  simpa [jointIndicator,hwv,hwp,hqv,hqp,hvp,Ne.symm hvp] using hd

/-- In a full row [w,w,p,q], distinct neighboring atoms make the rail
edge v-q a single bond. This intrinsic degree fact is used to protect
backbone rails from double-bond removals. -/
theorem four_row_single_next_pair_degree (M : Molecule V D) (hM : M.IsMolecule)
    {v w p q : V} (R : FourIncidences M v ![w,w,p,q])
    (hvq : v ≠ q) (hwv : w ≠ v) (hwq : w ≠ q) (hpv : p ≠ v) (hpq : p ≠ q) :
    M.degIn {v,q} v=1 := by
  have hd := fourIncidences_degree M hM R ({v,q} : Finset V) (mem_insert_self _ _)
  rw [Fin.sum_univ_four] at hd
  simpa [jointIndicator,hwv,hwq,hpv,hpq,hvq,Ne.symm hvq] using hd

end WaveTurbulence.Vine
