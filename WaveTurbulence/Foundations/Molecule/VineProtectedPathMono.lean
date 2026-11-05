/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineMixedSinglePaths
import Mathlib.Tactic

/-! # Protected single paths in a subgroup are paths in a larger atom group -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Enlarging the ambient atom group preserves a protected path. The
single-pair degree and the removed piece are unchanged. -/
theorem protected_single_path_mono (M : Molecule V D) {B U A : Finset V} (hBU : B ⊆ U)
    {a b u v : V} (hp : Relation.EqvGen (ProtectedSingleAdj M B A a b) u v) :
    Relation.EqvGen (ProtectedSingleAdj M U A a b) u v := by
  induction hp with
  | rel u v huv =>
    obtain ⟨⟨hu,hv,hne,ha,hd⟩,huA,hvA,hn⟩ := huv
    exact Relation.EqvGen.rel _ _ ⟨⟨hBU hu,hBU hv,hne,ha,hd⟩,huA,hvA,hn⟩
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end WaveTurbulence.Vine
