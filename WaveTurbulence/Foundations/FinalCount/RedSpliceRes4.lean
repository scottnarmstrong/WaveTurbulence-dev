/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceRes3
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): the vine is induced-isomorphic to its residual image

`SDecomp.inducedIso`: for a splice `SpMol N N1 cls` of a decomposed block, the skipped vine `A` is
induced-isomorphic to its image `A.image pi` in the spliced molecule.  Hence blocks and vines transport.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole

variable {V D V1 D1 : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V1] [Fintype D1] [DecidableEq D1]
  {N : Molecule V D} {N1 : Molecule V1 D1} {cls : V → Option V} {S A L0 R0 : Finset V} {a b x y : V}

/-- The residual of the vine, as an induced isomorphism. -/
@[expose] noncomputable def SDecomp.inducedIso (H : SDecomp N cls S A L0 R0 a b x y) (M : SpMol N N1 cls) :
    InducedIso N N1 A (A.image M.pi) :=
  M.inducedIso A H.H1 H.H2 (by
    intro y hy
    obtain ⟨v, hv, hvy⟩ := Finset.mem_image.mp hy.1
    obtain ⟨v', hv', hvy'⟩ := Finset.mem_image.mp hy.2
    apply H.H3 (M.od y)
    · refine ⟨v, hv, ?_⟩
      rw [← M.ob_atom y, ← hvy, M.ob_pi]
    · refine ⟨v', hv', ?_⟩
      rw [← M.od_mate, ← M.ob_atom, ← hvy', M.ob_pi]
    · exact (M.od_range (M.od y)).mp ⟨y, rfl⟩)

end WaveTurbulence.RedSplice
