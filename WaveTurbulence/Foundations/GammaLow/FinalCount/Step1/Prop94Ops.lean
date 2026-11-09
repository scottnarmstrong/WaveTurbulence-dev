/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.Prop94Ops`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 **The stage-2 operations of DH23 §9.3** (Revision_Submit.tex L1773--L1783; TARGET L2117--L2151, Operations 1--4),
as a literal datatype over molecules (FINALCOUNT-G2).

* Step 1 (L1775, `vine`): for an SG vine-like object `U` (the lg-spine `Object`, `.vc` or `.hyper`), cut at each of
  its two joints along the two bonds of `U` at that joint, then remove the VC (the atoms of `U`). The two joints
  become the fresh atoms `fa`, `fb` of degree `≤ 2`, defined to be `α`-atoms labelled by the dyadic gap `R`.
* Step 2 (L1777, `triangle`): `TriData`: cut `v₁, v₂, v₃` along the triangle bonds and remove the triangle.
* Steps 3 and 4 (L1779, L1781, `cut`): a single cut of an atom of degree `3` or `4` (`α` or `β`, `IsAlphaCut`).
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem objectAtoms_sub {M : Molecule V D} (C : Src.Object g M) : C.atoms ⊆ M.atoms := by
  have := C.shape
  rcases h : C.shape with hv | hh
  · exact hv.1.1
  · exact hh.adjoint.1.1

/-- **Step 1 data over `𝒱_g`** (DH23 L1775; main's `FinalCount.VineCut` with the object carrier `Src.Object g M`, so that
the removed object may be a T-vine, an HV of a T-vine, or a VC/HVC over `𝒱_g`): the SG vine-like object `C`, the fresh atoms `fa fb` created at its upper and lower
joints, and the two darts of `C` at each joint along which the cut is made (`a_mem, b_mem, ab_ne` are the joint
facts of a block, `IsBlock`: `j₁, j₂ ∈ S`, `j₁ ≠ j₂`). The removed set is `C.atoms`; `closed`
says that it is a union of components of the doubly cut molecule (`Prop subsetvc`: "This disconnects a VC from the
rest of the molecule"). -/
structure VineCut (g : ℝ) (M : Molecule V D) where
  C : Src.Object g M
  fa : V
  fb : V
  x₁ : D
  x₂ : D
  y₁ : D
  y₂ : D
  a_mem : C.upper ∈ C.atoms
  b_mem : C.lower ∈ C.atoms
  ab_ne : C.upper ≠ C.lower
  cut_a : M.IsCutData C.upper fa x₁ x₂
  cut_b : (M.cut C.upper fa x₁ x₂).IsCutData C.lower fb y₁ y₂
  in_a : C.ContainsDart x₁ ∧ C.ContainsDart x₂
  in_b : C.ContainsDart y₁ ∧ C.ContainsDart y₂
  closed : PClosed ((M.cut C.upper fa x₁ x₂).cut C.lower fb y₁ y₂) (fun a => a ∉ C.atoms)

namespace VineCut
variable {M : Molecule V D} (K : VineCut g M)

/-- The molecule after the two cuts. -/
def cutMol : Molecule V D := (M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂

/-- The molecule after removing the VC. -/
def post : Molecule V (PDart K.cutMol (fun a => a ∉ K.C.atoms)) :=
  restrictP K.cutMol (fun a => a ∉ K.C.atoms) K.closed

end VineCut

/-- **The stage-2 operations** (DH23 L1773--L1783), main's `FinalCount.Stage2Op` with Step 1 over `𝒱_g`. -/
inductive Stage2Op (g : ℝ) (M : Molecule V D)
  /-- Steps 3--4 (L1779, L1781): cut the atom `v` along the darts `x₁` (incoming) and `x₂` (outgoing). -/
  | cut (v v₂ : V) (x₁ x₂ : D) (h : M.IsCutData v v₂ x₁ x₂)
  /-- Step 2 (L1777): remove a triangle. -/
  | triangle (T : TriData M)
  /-- Step 1 (L1775): remove an SG vine-like object. -/
  | vine (K : VineCut g M)

namespace Stage2Op
variable {M : Molecule V D}

/-- The dart type of the molecule after an operation. -/
def PostD : Stage2Op g M → Type _
  | .cut .. => D
  | .triangle T => PDart T.m3 T.TP
  | .vine K => PDart K.cutMol (fun a => a ∉ K.C.atoms)

/-- The molecule after an operation (`𝕄_pos`). -/
def post : (op : Stage2Op g M) → Molecule V op.PostD
  | .cut v v₂ x₁ x₂ _ => M.cut v v₂ x₁ x₂
  | .triangle T => T.kept
  | .vine K => K.post

end Stage2Op
end WaveTurbulence.GammaLow.FinalCount.Step1
