/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineTypeVOtherBranchData
import Mathlib.Tactic

/-! # The type-V rail paths survive deletion of a second branch -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Both complete source type-V rails avoid the removed other branch,
for every rung count including zero. -/
theorem VineRealization.typeV_other_branch_slot_paths {M : Molecule V D}
    {B : Finset V} {a b : V} (R : VineRealization M .V B a b) (hB : M.IsBlock B a b)
    (hM : M.IsMolecule) (A : Finset V) (hAB : A ∩ B={a,b}) (k : ℕ) (hk : R.k=[k]) :
    Relation.EqvGen (ProtectedSingleAdj M B A a b)
      (R.coreAtom (2 : Fin 9)).1 (R.coreAtom (4 : Fin 9)).1 ∧
    Relation.EqvGen (ProtectedSingleAdj M B A a b)
      (R.coreAtom (3 : Fin 9)).1 (R.coreAtom (5 : Fin 9)).1 := by
  obtain ⟨Q,hmem,hports,hlabels,H,hzero⟩ := R.typeV_other_branch_slot_data hB A hAB k hk
  have hloc : VineType.V.template.slots.zip R.k=[]++(((2,4),(3,5)),k)::[] := by rw [hk]; rfl
  have hp := R.slot_protected_paths hM [] [] ((2,4),(3,5)) k hloc Q hmem hports hlabels H hzero
  have eqCore (v : V) (hv : v ∈ B) (i : Fin 9) (hi : R.f v=i.1) : v=(R.coreAtom i).1 :=
    R.injOn hv (R.coreAtom i).2 (hi.trans (R.label_coreAtom i).symm)
  have hu0 := eqCore (Q.u 0) (hmem 0).1 (2 : Fin 9) hports.1
  have hv0 := eqCore (Q.v 0) (hmem 0).2 (3 : Fin 9) hports.2.1
  have huN := eqCore (Q.u (k+1)) (hmem (k+1)).1 (4 : Fin 9) hports.2.2.1
  have hvN := eqCore (Q.v (k+1)) (hmem (k+1)).2 (5 : Fin 9) hports.2.2.2
  simpa only [hu0,hv0,huN,hvN] using hp

end WaveTurbulence.Vine
