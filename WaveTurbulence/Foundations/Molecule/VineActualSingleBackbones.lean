/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreSinglePathLift
import Mathlib.Tactic

/-! # Actual expanded vines have the literal single-bond backbone -/

public section
namespace WaveTurbulence.Vine

/-- Atoms reached by the single-bond backbone of a base template.
Type I has no such backbone. In types II/III all atoms are reached; in
IV–VIII only the indicated normal-center atom is excluded. -/
@[expose] def OnSingleBackbone : VineType → ℕ → Prop
  | .I, _ => False
  | .II, _ | .III, _ => True
  | .IV, i => i ≠ 5
  | .V, i => i ≠ 8
  | .VI, i => i ≠ 12
  | .VII, i => i ≠ 4
  | .VIII, i => i ≠ 10

instance (X : VineType) (i : ℕ) : Decidable (OnSingleBackbone X i) := by
  cases X <;> unfold OnSingleBackbone <;> infer_instance

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every core atom except the normal center reaches the first joint by
single actual bonds, for arbitrary source rung counts. -/
theorem VineRealization.core_single_to_zero {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (hM : M.IsMolecule)
    (i : Fin X.template.n) (hi : OnSingleBackbone X i.1) :
    Relation.EqvGen (SingleGroupAdj M S)
      (R.coreAtom ⟨0,by cases X <;> decide⟩).1 (R.coreAtom i).1 := by
  apply R.lift_core_single_path hM
  cases X with
  | I => exact False.elim hi
  | II => exact coreII_single_backbone i.1 i.2
  | III => exact coreIII_single_backbone i.1 i.2
  | IV => exact coreIV_single_backbone i.1 i.2 hi
  | V => exact coreV_single_backbone i.1 i.2 hi
  | VI => exact coreVI_single_backbone i.1 i.2 hi
  | VII => exact coreVII_single_backbone i.1 i.2 hi
  | VIII => exact coreVIII_single_backbone i.1 i.2 hi

/-- The expanded core backbone survives any disjoint or nondisjoint
family of type-I removals. Disjointness is needed only to attach a
normal center, not for this backbone itself. -/
theorem VineRealization.typeI_removals_core_backbone {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (hM : M.IsMolecule)
    (ps : List (RemovalPiece V D))
    (hI : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right)
    (hD : ∀ P ∈ ps,P.darts=Finset.univ.filter (M.InGroup P.atoms))
    (i : Fin X.template.n) (hi : OnSingleBackbone X i.1) :
    (removeBlocks M S ps).SameComponent
      (R.coreAtom ⟨0,by cases X <;> decide⟩).1 (R.coreAtom i).1 :=
  typeI_removal_single_path M S ps hI hD (R.core_single_to_zero hM i hi)

end WaveTurbulence.Vine
