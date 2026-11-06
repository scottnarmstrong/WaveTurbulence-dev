/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.MoleculeOverlapCrossings
import Mathlib.Tactic

/-! # Actual incidence identities at full-degree intersections -/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

omit [DecidableEq D] in
/-- Full degree in B forces every actual incidence at v to remain in B;
intersecting any other group A with B loses no incidence at that atom. -/
theorem internal_inter_eq_of_full_degree (hM : M.IsMolecule) {B : Finset V} {v : V}
    (hv : v ∈ M.atoms) (hd : M.degIn B v = 4) (A : Finset V) :
    (M.dartsAt v).filter (M.InGroup (A ∩ B)) = (M.dartsAt v).filter (M.InGroup A) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxv,hxA,hxmA⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxv,(Finset.mem_inter.mp hxA).1,(Finset.mem_inter.mp hxmA).1⟩
  · intro hx
    obtain ⟨hxv,hxA,hxmA⟩ := Finset.mem_filter.mp hx
    have hxa := (mem_dartsAt M v x).mp hxv
    have hxmB := full_degree_no_exit M hM hv hd hxa
    have hvB : v ∈ B := by
      have hdeg : 0 < M.degIn B v := by omega
      obtain ⟨y,hy⟩ := Finset.card_pos.mp hdeg
      have hyv := (mem_dartsAt M v y).mp (Finset.mem_filter.mp hy).1
      exact hyv ▸ (Finset.mem_filter.mp hy).2.1
    exact Finset.mem_filter.mpr ⟨hxv,Finset.mem_inter.mpr ⟨hxA,hxa.symm ▸ hvB⟩,
      Finset.mem_inter.mpr ⟨hxmA,hxmB⟩⟩

omit [DecidableEq D] in
/-- Orientation counts are also unchanged at a full-degree intersection. -/
theorem orientedIn_inter_eq_of_full_degree (hM : M.IsMolecule) {B : Finset V} {v : V}
    (hv : v ∈ M.atoms) (hd : M.degIn B v = 4) (A : Finset V) (b : Bool) :
    ((M.dartsAt v).filter (fun x => M.InGroup (A ∩ B) x ∧ M.out x = b)).card =
      ((M.dartsAt v).filter (fun x => M.InGroup A x ∧ M.out x = b)).card := by
  simp only [← Finset.filter_filter]
  rw [internal_inter_eq_of_full_degree M hM hv hd A]

/-- A realized hyper-block's joint-to-joint edge cannot cross a full
interior boundary of another group, so such a realization is a block. -/
theorem realization_block_of_crossed_joints (hM : M.IsMolecule) {A B : Finset V} {a1 a2 b1 b2 : V}
    (RA : BlockRealization M A a1 a2) (RB : BlockRealization M B b1 b2)
    (ha1B : a1 ∈ B) (ha11 : a1 ≠ b1) (ha12 : a1 ≠ b2) (ha2out : a2 ∉ B) : M.IsBlock A a1 a2 := by
  cases RA with
  | block hB hc => exact hB
  | hyper e he hB hc =>
    have hadj : M.Adj a1 a2 := by
      have hend : (M.atom e = a1 ∧ M.atom (M.mate e) = a2) ∨
          (M.atom e = a2 ∧ M.atom (M.mate e) = a1) := Sym2.eq_iff.mp he
      rcases hend with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact ⟨e,h1,h2⟩
      · exact ⟨M.mate e,h2,by rw [M.mate_mate]; exact h1⟩
    exact (ha2out (realized_interior_adj_mem M hM RB ha1B ha11 ha12 hadj)).elim

end WaveTurbulence.Mole
