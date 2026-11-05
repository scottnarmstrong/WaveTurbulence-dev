/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRungJointExclusion
import Mathlib.Tactic

/-! # The active-wire data derived from an actual nested block -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- When a non-double connected block selects a long full-rung sequence,
its four boundary rail endpoints must be selected as well. -/
theorem block_fullRungSequence_ports_mem (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b) (hC : GroupConnected M S)
    (hcard : 2<S.card) {n : ℕ} (hn : 3 ≤ n) (R : FullRungSequence M n)
    (hfirst : R.u 1 ∈ S) :
    R.u 0 ∈ S ∧ R.v 0 ∈ S ∧ R.u (n+1) ∈ S ∧ R.v (n+1) ∈ S := by
  have hn1 : 1 ≤ n := by omega
  have hlast := (block_fullRungSequence_constant M hM hB hC hcard hn R 1 le_rfl hn1 n hn1 le_rfl).mp hfirst
  have hvfirst := (block_fullRungSequence_membership M hM hB hn R 1 le_rfl hn1).mp hfirst
  have hvlast := (block_fullRungSequence_membership M hM hB hn R n hn1 le_rfl).mp hlast
  have hno1 := block_fullRungSequence_no_joints M hM hB hC hcard hn R 1 le_rfl hn1
  have hnon := block_fullRungSequence_no_joints M hM hB hC hcard hn R n hn1 le_rfl
  let U1 := R.upper 1 le_rfl hn1
  let V1 := R.lower 1 le_rfl hn1
  let Un := R.upper n hn1 le_rfl
  let Vn := R.lower n hn1 le_rfl
  have hau : M.Adj (R.u 1) (R.u 0) := ⟨U1.dart 2,U1.atom_eq 2,U1.neighbor_eq 2⟩
  have hav : M.Adj (R.v 1) (R.v 0) := ⟨V1.dart 2,V1.atom_eq 2,V1.neighbor_eq 2⟩
  have hbu : M.Adj (R.u n) (R.u (n+1)) := ⟨Un.dart 3,Un.atom_eq 3,Un.neighbor_eq 3⟩
  have hbv : M.Adj (R.v n) (R.v (n+1)) := ⟨Vn.dart 3,Vn.atom_eq 3,Vn.neighbor_eq 3⟩
  exact ⟨Mole.block_interior_adj_mem M hM hB hfirst hno1.1.1 hno1.1.2 hau,
    Mole.block_interior_adj_mem M hM hB hvfirst hno1.2.1 hno1.2.2 hav,
    Mole.block_interior_adj_mem M hM hB hlast hnon.1.1 hnon.1.2 hbu,
    Mole.block_interior_adj_mem M hM hB hvlast hnon.2.1 hnon.2.2 hbv⟩

/-- All rung-membership indicators are the same 0/1 active-wire value. -/
theorem block_fullRungSequence_mask (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b) (hC : GroupConnected M S)
    (hcard : 2<S.card) {n : ℕ} (hn : 3 ≤ n) (R : FullRungSequence M n) :
    jointIndicator S (R.u 1)≤1 ∧ ∀ i,1 ≤ i → i ≤ n →
      jointIndicator S (R.u i)=jointIndicator S (R.u 1) ∧
      jointIndicator S (R.v i)=jointIndicator S (R.u 1) := by
  refine ⟨jointIndicator_le_one S _,?_⟩
  intro i hi hin
  have he := (jointIndicator_eq_iff S (R.u 1) (R.u i)).mpr
    (block_fullRungSequence_constant M hM hB hC hcard hn R 1 le_rfl (by omega) i hi hin)
  have hp := (jointIndicator_eq_iff S (R.u i) (R.v i)).mpr
    (block_fullRungSequence_membership M hM hB hn R i hi hin)
  exact ⟨he.symm,hp.symm.trans he.symm⟩

end WaveTurbulence.Vine
