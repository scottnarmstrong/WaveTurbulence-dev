/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSlotFullDistinct
public import WaveTurbulence.Foundations.Molecule.VineSlotBoundaryEdges
public import WaveTurbulence.Foundations.Molecule.VinePrependSequence
public import WaveTurbulence.Foundations.Molecule.VineAssembleIncidences
public import WaveTurbulence.Foundations.Molecule.VineCoreJointEdges
import Mathlib.Tactic

/-! # Actual type-II sequences with all rung atoms in the source vine

This extends the accepted M4 construction by retaining the membership
proof already constructed for every sequence value. The original input
source is read-only; the same construction covers zero inserted rungs. -/

public section
namespace WaveTurbulence.Molecpl
open Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET defvine, F72: type II with k inserted rungs has m=k+1 full
rungs. Both external port pairs coincide with the respective outer joint.
The case k=0 is the four-atom Q-block. -/
theorem typeII_full_sequence_with_membership {M : Molecule V D} {S : Finset V} {a b : V}
    (R : VineRealization M .II S a b) (k : ℕ) (hk : R.k=[k]) :
    ∃ Q : FullRungSequence M (k+1),
      Q.u 0=(R.coreAtom (0 : Fin 4)).1 ∧ Q.v 0=(R.coreAtom (0 : Fin 4)).1 ∧
      Q.u (k+2)=(R.coreAtom (1 : Fin 4)).1 ∧ Q.v (k+2)=(R.coreAtom (1 : Fin 4)).1 ∧
      (∀ i, Q.u i ∈ S ∧ Q.v i ∈ S) ∧
      ∀ z ∈ S,2 ≤ R.f z → ∃ i,1 ≤ i ∧ i ≤ k+1 ∧ (z=Q.u i ∨ z=Q.v i) := by
  let s : (ℕ×ℕ)×(ℕ×ℕ) := ((2,1),(3,1))
  have hloc : VineType.II.template.slots.zip R.k=[]++(s,k)::[] := by rw [hk]; rfl
  obtain ⟨Q,hmem,hports,hlabels⟩ := R.has_rungSequence_ports [] [] s k hloc
  have hports' : R.f (Q.u 0)=2 ∧ R.f (Q.v 0)=3 ∧
      R.f (Q.u (k+1))=1 ∧ R.f (Q.v (k+1))=1 := hports
  have hlabels' : ∀ i,1 ≤ i → i ≤ k →
      R.f (Q.u i)=4+(i-1) ∧ R.f (Q.v i)=4+k+(i-1) := hlabels
  have hrail := R.slot_boundary_adj [] [] s k hloc Q hmem hports
  let p := (R.coreAtom (0 : Fin 4)).1
  let q := (R.coreAtom (1 : Fin 4)).1
  have hp : R.f p=0 := R.label_coreAtom (0 : Fin 4)
  have hq : R.f q=1 := R.label_coreAtom (1 : Fin 4)
  have he (v : V) (hv : v ∈ S) (i : Fin 4) (hvi : R.f v=i.1) : v=(R.coreAtom i).1 :=
    R.injOn hv (R.coreAtom i).2 (hvi.trans (R.label_coreAtom i).symm)
  have hu0 := he (Q.u 0) (hmem 0).1 (2 : Fin 4) hports'.1
  have hv0 := he (Q.v 0) (hmem 0).2 (3 : Fin 4) hports'.2.1
  have huN := he (Q.u (k+1)) (hmem (k+1)).1 (1 : Fin 4) hports'.2.2.1
  have hvN := he (Q.v (k+1)) (hmem (k+1)).2 (1 : Fin 4) hports'.2.2.2
  have hfu (i : ℕ) (hi : i ≤ k) : R.f (Q.u i)=if i=0 then 2 else 4+(i-1) := by
    by_cases hz : i=0
    · simpa only [hz,ite_true] using hports'.1
    · simpa only [hz,ite_false] using (hlabels' i (by omega) hi).1
  have hfv (i : ℕ) (hi : i ≤ k) : R.f (Q.v i)=if i=0 then 3 else 4+k+(i-1) := by
    by_cases hz : i=0
    · simpa only [hz,ite_true] using hports'.2.1
    · simpa only [hz,ite_false] using (hlabels' i (by omega) hi).2
  have hd : Function.Injective (Sum.elim (fun i : Fin (k+1) => Q.u i.1)
      (fun i : Fin (k+1) => Q.v i.1)) := by
    apply Sum.elim_injective.mpr
    refine ⟨?_,?_,?_⟩
    · intro i j hij
      apply Fin.ext
      have hh := congrArg R.f hij
      rw [hfu i (by omega),hfu j (by omega)] at hh
      split_ifs at hh <;> omega
    · intro i j hij
      apply Fin.ext
      have hh := congrArg R.f hij
      rw [hfv i (by omega),hfv j (by omega)] at hh
      split_ifs at hh <;> omega
    · intro i j hij
      have hh := congrArg R.f hij
      rw [hfu i (by omega),hfv j (by omega)] at hh
      split_ifs at hh <;> omega
  obtain ⟨R0⟩ := R.twoIncidences_of_edge_count (hmem 0).1 (hmem 0).2 (by
    rw [hports'.1,hports'.2.1]
    exact expand_core_double_count .II R.k (2,3) (by decide))
  have hap : M.Adj (Q.u 0) p := by
    rw [hu0]
    exact Mole.adj_symmetric M (R.core_joint_adj (0 : Fin 4) (2 : Fin 4) (by decide) (by decide))
  have hbp : M.Adj (Q.v 0) p := by
    rw [hv0]
    exact Mole.adj_symmetric M (R.core_joint_adj (0 : Fin 4) (3 : Fin 4) (by decide) (by decide))
  have nextlabels :
      R.f (Q.u 1)=(if k=0 then 1 else 4) ∧
      R.f (Q.v 1)=(if k=0 then 1 else 4+k) := by
    by_cases hz : k=0
    · subst k
      simpa only [ite_true] using hports'.2.2
    · simpa only [hz,ite_false,Nat.sub_self,Nat.add_zero] using hlabels' 1 le_rfl (by omega)
  have hne (x y : V) (hh : R.f x ≠ R.f y) : x ≠ y := fun h => hh (congrArg R.f h)
  obtain ⟨rowu⟩ := fourIncidences_of_double_and_edges R0 hap hrail.1
    (hne _ _ (by rw [hports'.2.1,hp]; decide))
    (hne _ _ (by rw [hports'.2.1,nextlabels.1]; split_ifs <;> omega))
    (hne _ _ (by rw [hp,nextlabels.1]; split_ifs <;> omega))
  obtain ⟨rowv⟩ := fourIncidences_of_double_and_edges R0.mates hbp hrail.2.1
    (hne _ _ (by rw [hports'.1,hp]; decide))
    (hne _ _ (by rw [hports'.1,nextlabels.2]; split_ifs <;> omega))
    (hne _ _ (by rw [hp,nextlabels.2]; split_ifs <;> omega))
  let E := Q.prependInitialDistinct p p hd rowu rowv
  refine ⟨E,rfl,rfl,?_,?_,?_,?_⟩
  · exact huN
  · exact hvN
  · intro i
    cases i with
    | zero => exact ⟨(R.coreAtom (0 : Fin 4)).2,(R.coreAtom (0 : Fin 4)).2⟩
    | succ i => exact hmem i
  intro z hz hz2
  have hzn := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hz)
  rw [hk,expand_atoms_exact .II [k] rfl] at hzn
  change R.f z<4+2*k at hzn
  have halt : R.f z=2 ∨ R.f z=3 ∨
      (4 ≤ R.f z ∧ R.f z<4+k) ∨ (4+k ≤ R.f z ∧ R.f z<4+2*k) := by omega
  have hzu (i : ℕ) (hl : R.f z=R.f (Q.u i)) : z=E.u (i+1) :=
    R.injOn hz (hmem i).1 hl
  have hzv (i : ℕ) (hl : R.f z=R.f (Q.v i)) : z=E.v (i+1) :=
    R.injOn hz (hmem i).2 hl
  rcases halt with h | h | ⟨hlo,hhi⟩ | ⟨hlo,hhi⟩
  · exact ⟨1,by omega,by omega,Or.inl (hzu 0 (h.trans hports'.1.symm))⟩
  · exact ⟨1,by omega,by omega,Or.inr (hzv 0 (h.trans hports'.2.1.symm))⟩
  · let i := R.f z-4+1
    have hi : 1 ≤ i ∧ i ≤ k := by dsimp [i]; omega
    exact ⟨i+1,by omega,by omega,Or.inl (hzu i (by
      rw [(hlabels' i hi.1 hi.2).1]; dsimp [i]; omega))⟩
  · let i := R.f z-(4+k)+1
    have hi : 1 ≤ i ∧ i ≤ k := by dsimp [i]; omega
    exact ⟨i+1,by omega,by omega,Or.inr (hzv i (by
      rw [(hlabels' i hi.1 hi.2).2]; dsimp [i]; omega))⟩

end WaveTurbulence.Molecpl
