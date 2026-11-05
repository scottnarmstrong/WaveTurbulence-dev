/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineObjects
import Mathlib.Tactic

/-! # Removing blocks while retaining joints (TARGET L1368, Operation 1)

The operation deletes non-joint atoms and selected whole bonds. In an
adjoint removal the added joint-to-joint bond is retained, including when
it is parallel to a removed bond. Actual dart identities retain this choice.
-/

public section
namespace WaveTurbulence.Vine
open Finset

/-- Atom and bond data of a removal. Specifying darts retains multiplicity;
the removal operation automatically treats both mates of each selected dart. -/
structure RemovalPiece (V D : Type*) where
  atoms : Finset V
  left : V
  right : V
  darts : Finset D

variable {V D : Type*} [DecidableEq V] [DecidableEq D] [Fintype D]

/-- Only non-joint atoms are deleted. -/
@[expose] def RemovalPiece.interior (P : RemovalPiece V D) : Finset V :=
  P.atoms \ {P.left,P.right}

/-- Removal of a block deletes all its internal bonds. -/
@[expose] def blockRemoval (M : Molecule V D) (A : Finset V) (a b : V) : RemovalPiece V D :=
  ⟨A,a,b,univ.filter (M.InGroup A)⟩

/-- Removal of an adjoint deletes its block bonds and retains precisely
the designated added bond, even if that bond has a parallel mate bond. -/
@[expose] def adjointRemoval (M : Molecule V D) (A : Finset V) (a b : V) (e : D) :
    RemovalPiece V D := ⟨A,a,b,(univ.filter (M.InGroup A)) \ {e,M.mate e}⟩

/-- The atoms surviving any finite family of removals. -/
@[expose] def remainingAtoms (S : Finset V) (ps : List (RemovalPiece V D)) : Finset V :=
  S.filter (fun v => ∀ P ∈ ps,v ∉ P.interior)

/-- A surviving bond has two surviving endpoints and is not selected by
any removal; either dart selecting a bond removes both mates. -/
@[expose] def KeepDart (M : Molecule V D) (S : Finset V)
    (ps : List (RemovalPiece V D)) (x : D) : Prop :=
  M.atom x ∈ remainingAtoms S ps ∧ M.atom (M.mate x) ∈ remainingAtoms S ps ∧
    ∀ P ∈ ps,x ∉ P.darts ∧ M.mate x ∉ P.darts

instance (M : Molecule V D) (S : Finset V) (ps : List (RemovalPiece V D)) (x : D) :
    Decidable (KeepDart M S ps x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

omit [DecidableEq D] [Fintype D] in
/-- Surviving darts are closed under the bond involution. -/
theorem keepDart_mate (M : Molecule V D) (S : Finset V) (ps : List (RemovalPiece V D))
    {x : D} (hx : KeepDart M S ps x) : KeepDart M S ps (M.mate x) := by
  refine ⟨hx.2.1,?_,?_⟩
  · simpa only [M.mate_mate] using hx.1
  · intro P hP
    simpa only [M.mate_mate] using (hx.2.2 P hP).symm

/-- The actual half-edge molecule remaining after simultaneous removals.
The joints remain as atoms, even if all their incidences are removed. -/
@[expose] def removeBlocks (M : Molecule V D) (S : Finset V) (ps : List (RemovalPiece V D)) :
    Molecule V {x : D // KeepDart M S ps x} where
  atoms := remainingAtoms S ps
  atom := fun x => M.atom x.1
  mate := fun x => ⟨M.mate x.1,keepDart_mate M S ps x.2⟩
  out := fun x => M.out x.1
  atom_mem := fun x => x.2.1
  mate_mate := fun x => Subtype.ext (M.mate_mate x.1)
  mate_ne := fun x h => M.mate_ne x.1 (congrArg Subtype.val h)
  out_mate := fun x => M.out_mate x.1

end WaveTurbulence.Vine
