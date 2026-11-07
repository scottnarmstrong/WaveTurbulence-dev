/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBOutgoingSums
public import WaveTurbulence.Foundations.Molecule.Degen.Removal
import Mathlib.Tactic

/-! # Exact outgoing reindexing of removed incidences at surviving atoms -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_sum_removedDartsAt_outgoing (M : Molecule V D) (Y : Finset V) {v : V} (hv : v ∉ Y)
    {E : Type*} [AddCommGroup E] (g : D → E) (hg : ∀ x,g (M.mate x) = -g x) :
    (∑ x ∈ Degen.removedDartsAt M Y v,g x) = ∑ x ∈ appbRemovedBonds M Y,
      ((if M.atom x = v then g x else 0)-(if M.atom (M.mate x) = v then g x else 0)) := by
  classical
  let gY := fun x : D => if M.atom x ∈ Y ∨ M.atom (M.mate x) ∈ Y then g x else 0
  have hY : ∀ x,gY (M.mate x) = -gY x := by
    intro x
    simp only [gY,M.mate_mate,hg,or_comm]
    split_ifs <;> simp
  have hleft : (∑ x ∈ M.dartsAt v,gY x) = ∑ x ∈ Degen.removedDartsAt M Y v,g x := by
    rw [Degen.removedDartsAt,sum_filter]
    apply sum_congr rfl
    intro x hx
    have hxv := (mem_filter.mp hx).2
    simp only [gY,hxv,hv,false_or]
  have hright : (∑ x ∈ M.bonds,
      ((if M.atom x = v then gY x else 0)-(if M.atom (M.mate x) = v then gY x else 0))) =
      ∑ x ∈ appbRemovedBonds M Y,
      ((if M.atom x = v then g x else 0)-(if M.atom (M.mate x) = v then g x else 0)) := by
    change _ = ∑ x ∈ M.bonds.filter _,_
    rw [sum_filter]
    apply sum_congr rfl
    intro x hx
    by_cases hd : M.atom x ∈ Y ∨ M.atom (M.mate x) ∈ Y
    · simp only [gY,hd,ite_true]
    · simp only [gY,hd,ite_false]
      split_ifs <;> simp
  exact hleft.symm.trans ((appb_sum_dartsAt_outgoing M v gY hY).trans hright)

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem sum_removedDartsAt_local_edges {v : V} (hv : v ∉ r.removedAtoms)
    {E : Type*} [AddCommGroup E] (g : D → E) (hg : ∀ x,g (M.mate x) = -g x) :
    (∑ x ∈ Degen.removedDartsAt M r.removedAtoms v,g x) = ∑ i : Fin P.edges.length,
      ((if M.atom (r.edge i).val = v then g (r.edge i).val else 0)-
        (if M.atom (M.mate (r.edge i).val) = v then g (r.edge i).val else 0)) := by
  rw [appb_sum_removedDartsAt_outgoing M r.removedAtoms hv g hg,← r.removedBond_sum]

end AppbRealization
end WaveTurbulence.Mole
