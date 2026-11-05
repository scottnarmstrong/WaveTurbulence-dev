/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRemoval
import Mathlib.Tactic

/-! # Joints and the designated adjoint bond survive removal -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [DecidableEq D] [Fintype D]

omit [DecidableEq D] [Fintype D] in
/-- A removed piece's two joints remain in the atom set. -/
theorem removal_joint_mem (S : Finset V) (P : RemovalPiece V D) {v : V}
    (hv : v ∈ S) (hj : v=P.left ∨ v=P.right) : v ∈ remainingAtoms S [P] := by
  apply mem_filter.mpr
  refine ⟨hv,?_⟩
  intro Q hQ
  have he := List.mem_singleton.mp hQ
  subst Q
  intro hi
  have hh := (mem_sdiff.mp hi).2
  apply hh
  simpa only [mem_insert,mem_singleton] using hj

/-- The designated added bond is retained when its adjoint is removed. -/
theorem adjointRemoval_keep_added (M : Molecule V D) (S A : Finset V) (a b : V)
    (e : D) (ha : a ∈ S) (hb : b ∈ S) (he : M.ends e=s(a,b)) :
    KeepDart M S [adjointRemoval M A a b e] e := by
  have hend : (M.atom e=a ∧ M.atom (M.mate e)=b) ∨
      (M.atom e=b ∧ M.atom (M.mate e)=a) := Sym2.eq_iff.mp he
  have hx : M.atom e ∈ S := hend.elim (fun h => h.1.symm ▸ ha) (fun h => h.1.symm ▸ hb)
  have hy : M.atom (M.mate e) ∈ S := hend.elim (fun h => h.2.symm ▸ hb) (fun h => h.2.symm ▸ ha)
  refine ⟨removal_joint_mem S _ hx ?_,removal_joint_mem S _ hy ?_,?_⟩
  · exact hend.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  · exact hend.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
  · intro P hP
    have hh := List.mem_singleton.mp hP
    subst P
    constructor <;> simp [adjointRemoval]

/-- The actual adjoint-removal molecule has a surviving edge between the
joints. Thus its replacement path is available without any gap assumption. -/
theorem adjointRemoval_added_adj (M : Molecule V D) (S A : Finset V) (a b : V)
    (e : D) (ha : a ∈ S) (hb : b ∈ S) (he : M.ends e=s(a,b)) :
    (removeBlocks M S [adjointRemoval M A a b e]).Adj a b := by
  have hk := adjointRemoval_keep_added M S A a b e ha hb he
  have hend : (M.atom e=a ∧ M.atom (M.mate e)=b) ∨
      (M.atom e=b ∧ M.atom (M.mate e)=a) := Sym2.eq_iff.mp he
  rcases hend with h | h
  · exact ⟨⟨e,hk⟩,h.1,h.2⟩
  · exact ⟨⟨M.mate e,keepDart_mate M S _ hk⟩,h.2,by change M.atom (M.mate (M.mate e))=b; rw [M.mate_mate]; exact h.1⟩

end WaveTurbulence.Vine
