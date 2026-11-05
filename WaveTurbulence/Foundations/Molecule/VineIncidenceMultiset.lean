/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
import Mathlib.Tactic

/-! # Vertex degrees from the undirected bond multiset -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Count one incidence at each endpoint; a self-loop contributes twice. -/
@[expose] def bondIncidence (e : Sym2 V) (v : V) : ℕ := e.toMultiset.count v

/-- The incidence count of one unordered bond. -/
theorem bondIncidence_pair (u w v : V) :
    bondIncidence s(u,w) v=(if u=v then 1 else 0)+(if w=v then 1 else 0) := by
  simp only [bondIncidence,Sym2.toMultiset,Sym2.lift_mk,Multiset.coe_count,List.count_cons,
    List.count_nil,beq_iff_eq]
  omega

/-- Sum a dart weight by outgoing representatives and their actual mates. -/
theorem sum_internal_darts (M : Molecule V D) {N : Type*} [AddCommMonoid N]
    (S : Finset V) (f : D → N) :
    ∑ x ∈ univ.filter (M.InGroup S),f x =
      ∑ x ∈ univ.filter (fun x => M.out x=true ∧ M.InGroup S x), (f x+f (M.mate x)) := by
  let I := univ.filter (M.InGroup S)
  let O := I.filter fun x => M.out x=true
  let B := I.filter fun x => M.out x=false
  have mate_mem {x : D} (hx : x ∈ I) : M.mate x ∈ I := by
    have hg := (mem_filter.mp hx).2
    exact mem_filter.mpr ⟨mem_univ _,hg.2,by rw [M.mate_mate]; exact hg.1⟩
  have he : ∑ x ∈ O,f (M.mate x)=∑ x ∈ B,f x := by
    apply Finset.sum_bij (fun x _hx => M.mate x)
    · intro x hx
      have hx' := mem_filter.mp hx
      refine mem_filter.mpr ⟨mate_mem hx'.1,?_⟩
      rw [M.out_mate,hx'.2]
      rfl
    · intro x _hx y _hy hxy
      exact Mole.mate_injective M hxy
    · intro y hy
      have hy' := mem_filter.mp hy
      refine ⟨M.mate y,mem_filter.mpr ⟨mate_mem hy'.1,?_⟩,M.mate_mate y⟩
      rw [M.out_mate,hy'.2]
      rfl
    · intro x _hx
      rfl
  have hp := sum_filter_add_sum_filter_not I (fun x => M.out x=true) f
  simp only [Bool.not_eq_true] at hp
  have hh : ∑ x ∈ I,f x=∑ x ∈ O, (f x+f (M.mate x)) := by
    rw [← hp,← he,← sum_add_distrib]
  simpa only [I,O,filter_filter,and_comm] using hh

/-- The actual internal degree equals the sum of incidences in the induced
undirected bond multiset. This retains all loops and multiplicities. -/
theorem degreeIn_eq_bondIncidence (M : Molecule V D) (S : Finset V) (v : V) :
    M.degIn S v=((M.groupBonds S).map (fun e => bondIncidence e v)).sum := by
  have hh := sum_internal_darts M S (fun x => if M.atom x=v then (1 : ℕ) else 0)
  have hl : (∑ x ∈ univ.filter (M.InGroup S),if M.atom x=v then (1 : ℕ) else 0)=M.degIn S v := by
    simp only [sum_boole,Nat.cast_id,Molecule.degIn,Molecule.dartsAt,filter_filter,and_comm]
  rw [hl] at hh
  rw [hh]
  simp only [Molecule.groupBonds,Multiset.map_map,Function.comp_apply]
  change _=∑ x ∈ univ.filter (fun x => M.out x=true ∧ M.InGroup S x),bondIncidence (M.ends x) v
  apply sum_congr rfl
  intro x _hx
  exact (bondIncidence_pair (M.atom x) (M.atom (M.mate x)) v).symm

end WaveTurbulence.Vine
