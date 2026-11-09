/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.MemberF23
public import WaveTurbulence.Foundations.TVine.Struct.Thm6
public import WaveTurbulence.Foundations.TVine.Struct.Attach
public import WaveTurbulence.Foundations.TVine.Core.Lemma19Del
public import WaveTurbulence.Foundations.TVine.Core.Pendant
public import WaveTurbulence.Foundations.TVine.Core.JointsInRungs
public import WaveTurbulence.Foundations.TVine.Core.ContainerJoints
public import WaveTurbulence.Foundations.TVine.Core.PhiSub
public import WaveTurbulence.Foundations.TVine.Core.PhiGap2
public import WaveTurbulence.Foundations.TVine.Core.PhiRemoval

/-!
# L3's named inputs discharged by L1's published theorems (packet L3)

L1 (TVINE-CORE) proved seven of the U-level statements that L3 took as named inputs; L3's copies are verbatim, so each
is discharged by `exact`:

| L3 named input | L1 theorem |
|---|---|
| `DeleteRungInput` (N2 Lemma 1.9(1)) | `Core.isTVineU_rungDel` |
| `PendantPolesInput` (N3 Lemma 6.2) | `Core.pendantPoles_holds` |
| `JointsInRungsInput` (N2 Lemma 1.11) | `Core.jointsInRungs_holds` |
| `ContainerJointsInput` (N2 Lemma 1.12) | `Core.containerJoints_holds` |
| `PhiSubObjInput` (N2 Lemma 1.14(b)) | `Core.phiSubObj_holds` |
| `PhiGapInput` (N2 Lemma 1.14(d)) | `Core.phiGap_holds` |
| `PhiRemovalInput` (N2 Lemma 1.14(e)) | `Core.phiRemoval_holds` |

With these, the remaining hypotheses of the structure theorems are L2's base statements (and L2's `SizeBound`) and
L1's still-open N2 Lemma 1.14(c′) (`PhiTypeInput`).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Struct

open TVine Core

universe u v

theorem deleteRungInput_holds : DeleteRungInput.{u} :=
  fun _ _ _ _ _ _ _ _ _ _ _ hT hD μ => isTVineU_rungDel hT hD μ

theorem pendantPolesInput_holds : PendantPolesInput.{u} := pendantPoles_holds

theorem jointsInRungsInput_holds : JointsInRungsInput.{u} := jointsInRungs_holds

theorem containerJointsInput_holds : ContainerJointsInput.{u} := containerJoints_holds

theorem phiSubObjInput_holds : PhiSubObjInput.{u} := phiSubObj_holds

theorem phiGapInput_holds : PhiGapInput.{u} := phiGap_holds

theorem phiRemovalInput_holds : PhiRemovalInput.{u} := phiRemoval_holds

/-- **N2 Proposition 1.17(b)** from L2's two statements alone. -/
theorem pieceShape_of_L2 (hsize : Checker.SizeBoundStatement.{u})
    (hbase : Checker.PieceShapeBaseStatement.{u}) : PieceShapeStatement.{u, v} :=
  pieceShape deleteRungInput_holds hsize hbase

/-- **N3 Theorem 6 (i)–(iii)** from L2's two statements alone. -/
theorem layervine_of_L2 (hsize : Checker.SizeBoundStatement.{u})
    (hbase : Checker.PieceShapeBaseStatement.{u}) : LayervineStatement.{u, v} :=
  layervine_of_pieceShape pendantPolesInput_holds (pieceShape_of_L2 hsize hbase)

/-- **M4 Lemma A** from L2's two statements alone. -/
theorem attach_of_L2 (hsize : Checker.SizeBoundStatement.{u})
    (hbase : Checker.PieceShapeBaseStatement.{u}) : AttachStatement.{u, v} :=
  attach_of_pieceShape (pieceShape_of_L2 hsize hbase)

/-- The inputs of Thm 1.15 still open (L1's N2 Lemma 1.14(c′); L2's size bound and base statements). -/
structure Thm115Open : Prop where
  phiType : PhiTypeInput.{u}
  size : Checker.SizeBoundStatement.{u}
  basePS : Checker.PieceShapeBaseStatement.{u}
  baseSO : Checker.SubObjBaseStatement.{u}
  baseFam : Checker.FamiliesBaseStatement.{u}

/-- The full input bundle from the open part, L1's proved lemmas filling the rest. -/
theorem Thm115Open.toInputs (O : Thm115Open.{u}) : Thm115Inputs.{u} :=
  ⟨deleteRungInput_holds, pendantPolesInput_holds, jointsInRungsInput_holds, phiSubObjInput_holds, O.phiType,
    phiGapInput_holds, phiRemovalInput_holds, O.size, O.basePS, O.baseSO, O.baseFam⟩

end WaveTurbulence.TVine.Struct
