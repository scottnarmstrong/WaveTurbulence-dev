/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRealizedSlot
public import WaveTurbulence.Foundations.Molecule.VineIntrinsicCoreGroups
import Mathlib.Tactic

/-! # Old nonjoint atoms cannot complete a triangle across an inserted rung -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Actual adjacency at a complete four-row uses one recorded neighbor. -/
theorem fourIncidences_adj_neighbor (M : Molecule V D) (hM : M.IsMolecule)
    {v z : V} {ns : Fin 4 → V} (F : FourIncidences M v ns) (hz : M.Adj v z) :
    ∃ j,ns j=z := by
  obtain ⟨e,he,hz⟩ := hz
  have hm : e ∈ M.dartsAt v := (Mole.mem_dartsAt M v e).mpr he
  rw [← fourIncidences_image M hM F] at hm
  obtain ⟨j,_hj,rfl⟩ := mem_image.mp hm
  exact ⟨j,(F.neighbor_eq j).symm.trans hz⟩

/-- A coordinate whose label is below the allocation is an old port. -/
theorem railAtom_old_port (N a b k i : ℕ) (_hi : i<k+2)
    (hold : railAtom N a b k i<N) : railAtom N a b k i=a ∨ railAtom N a b k i=b := by
  by_cases h0 : i=0
  · simp only [railAtom,h0,ite_true,true_or]
  · by_cases hk : i ≤ k
    · simp only [railAtom,h0,ite_false,hk,ite_true] at hold
      omega
    · simp only [railAtom,h0,ite_false,hk,or_true]

namespace RailLabelFrame
variable {M : Molecule V D} {k : ℕ} {Q : FullRungSequence M k} (F : RailLabelFrame Q)
include F

/-- Any old neighbor of a fresh upper atom is an upper old port. -/
theorem upper_old_neighbor (hM : M.IsMolecule) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ k)
    {z : V} (hz : F.f z<F.N) (hadj : M.Adj (Q.u i) z) : F.f z=F.a ∨ F.f z=F.b := by
  obtain ⟨j,hj⟩ := fourIncidences_adj_neighbor M hM (Q.upper i hi hin) hadj
  have hv : F.f (Q.v i)=F.N+k+(i-1) := by
    rw [F.lower ⟨i,by omega⟩,railAtom_interior _ _ _ _ _ hi hin]
  have port (t : ℕ) (ht : t<k+2) (he : Q.u t=z) : F.f z=F.a ∨ F.f z=F.b := by
    have hh := F.upper ⟨t,ht⟩
    rw [he] at hh
    rw [hh] at hz ⊢
    exact railAtom_old_port _ _ _ _ _ ht hz
  fin_cases j
  · change Q.v i=z at hj; rw [hj] at hv; omega
  · change Q.v i=z at hj; rw [hj] at hv; omega
  · exact port (i-1) (by omega) hj
  · exact port (i+1) (by omega) hj

/-- Any old neighbor of a fresh lower atom is a lower old port. -/
theorem lower_old_neighbor (hM : M.IsMolecule) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ k)
    {z : V} (hz : F.f z<F.N) (hadj : M.Adj (Q.v i) z) : F.f z=F.c ∨ F.f z=F.d := by
  obtain ⟨j,hj⟩ := fourIncidences_adj_neighbor M hM (Q.lower i hi hin) hadj
  have hu : F.f (Q.u i)=F.N+(i-1) := by
    rw [F.upper ⟨i,by omega⟩,railAtom_interior _ _ _ _ _ hi hin]
  have port (t : ℕ) (ht : t<k+2) (he : Q.v t=z) : F.f z=F.c ∨ F.f z=F.d := by
    have hh := F.lower ⟨t,ht⟩
    rw [he] at hh
    have hz' : F.f z<F.N+k := by omega
    rw [hh] at hz' ⊢
    exact railAtom_old_port _ _ _ _ _ ht hz'
  fin_cases j
  · change Q.u i=z at hj; rw [hj] at hu; omega
  · change Q.u i=z at hj; rw [hj] at hu; omega
  · exact port (i-1) (by omega) hj
  · exact port (i+1) (by omega) hj

end RailLabelFrame

/-- An old nonjoint atom cannot be adjacent to both ends of one fresh rung. -/
theorem RealizedSlot.old_nonjoint_not_both (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b z : V} {R : VineRealization M X S a b}
    (A : RealizedSlot R) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ A.k)
    (hzold : R.f z<X.template.n) (hz2 : 2 ≤ R.f z)
    (hU : M.Adj (A.Q.u i) z) (hV : M.Adj (A.Q.v i) z) : False := by
  have hn : X.template.n ≤ A.frame.N := by
    change X.template.n ≤ (A.pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n
    rw [fold_insertRungs_atoms]; omega
  have hz : A.frame.f z<A.frame.N := lt_of_lt_of_le hzold hn
  have hu := A.frame.upper_old_neighbor hM i hi hin hz hU
  have hv := A.frame.lower_old_neighbor hM i hi hin hz hV
  have hs : A.s ∈ X.template.slots := by
    have hh : (A.s,A.k) ∈ X.template.slots.zip R.k := by
      rw [A.loc]; exact List.mem_append_right _ List.mem_cons_self
    exact (List.of_mem_zip hh).1
  exact template_slot_nonjoint_cross_disjoint X A.s hs ⟨R.f z,hzold⟩ hz2 hu hv

end WaveTurbulence.Vine
