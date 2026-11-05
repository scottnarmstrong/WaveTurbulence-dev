/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceVineGapObjects
/-! Explicit source objects used by subpro and the finalcount1 admissibility requirements. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.SourceVine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An actual designated vine-like object, including its atom set and ordered joints. -/
structure Object (M : Molecule V D) where
  atoms : Finset V
  upper : V
  lower : V
  shape : VineLikeObject M atoms upper lower

namespace Object
variable {M : Molecule V D}

/-- TARGET defdiff: the gap is computed in the designated adjoint for a hyper-object. -/
def HasGapKind {d : ℕ} (C : Object M) (L γ η : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (kind : Molecule.GapKind) : Prop :=
  ∃ r, C.shape.IsGap L w κ r ∧ Molecule.gapKind L γ η r = kind

/-- SOURCE containment retains a hyper-object's deleted bond when atom sets coincide. -/
def IsContained (A B : Object M) : Prop := A.shape.IsContained B.shape

/-- Membership of a bond in the actual object. A hyper-object uses its designated
adjoint, so neither dart of its deleted bond is included. -/
def ContainsDart (C : Object M) (x : D) : Prop :=
  match C.shape with
  | .vc _ => M.InGroup C.atoms x
  | .hyper R => x ≠ R.added ∧ x ≠ M.mate R.added ∧ M.InGroup C.atoms x

end Object

/-- The literal internal-parent incidence of a block in an actual garden. -/
def InternalParent {w : ℕ} (G : Garden w) (S : Finset (GBranch G.tree))
    (v : GBranch G.tree) : Prop :=
  ∃ h : v.1.2 ≠ [], GNode.parent v.toNode h ∈ S

/-- TARGET subpro(2), L2043: an HV, a CN vine, or a root CL vine. The source root-block
condition is the sum of the joint degrees being at most six (TARGET L1368). -/
def AllowedCollectionObject {w : ℕ} (G : Garden w) (C : Object G.molecule) : Prop :=
  match C.shape with
  | .hyper R => IsSomeVine (Molecule.eraseBond G.molecule R.added) C.atoms C.upper C.lower
  | .vc _ => IsSomeVine G.molecule C.atoms C.upper C.lower ∧
      ((¬ InternalParent G C.atoms C.upper ∧ ¬ InternalParent G C.atoms C.lower) ∨
        ((¬ InternalParent G C.atoms C.upper ∧ InternalParent G C.atoms C.lower) ∨
          (¬ InternalParent G C.atoms C.lower ∧ InternalParent G C.atoms C.upper)) ∧
          G.molecule.deg C.upper + G.molecule.deg C.lower ≤ 6)

end WaveTurbulence.LGSpine.SourceVine
