/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.SubObjects
public import WaveTurbulence.Foundations.TVine.Core.Final
public import WaveTurbulence.Foundations.TVine.Checker.BaseSub
public import WaveTurbulence.Foundations.TVine.Checker.BasePieces
public import WaveTurbulence.Foundations.TVine.Checker.SizeBound2

/-!
# The T-vine structure theorems, unconditional (packet L3)

Every named input of L3 is discharged: L1's N2 Lemma 1.14(c′) (`Core.phiType_holds`, `Core.Final`) together with the
other L1 statements (`Struct/Discharge.lean`), and L2's size bound and base statements (`Checker.sizeBound`,
`Checker.pieceShapeBase`, `Checker.subObjBase`, `Checker.familiesBase`).

* **`pieceShape_holds`** : `PieceShapeStatement` (N2 Prop 1.17(b));
* **`layervine_holds`** : `LayervineStatement` (N3 Thm 6 (i)–(iii));
* **`attach_holds`** : `AttachStatement` (M4 Lemma A);
* **`subObjects_holds`** : `SubObjectsStatement` (N2 Thm 1.15 (F1)–(F6));
* **`cor116Single_holds`** : `Cor116SingleStatement` (N3 Cor 1.16′).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Struct

universe u v

theorem phiTypeInput_holds : PhiTypeInput.{u} := Core.phiType_holds

theorem thm115Open_holds : Thm115Open.{u} :=
  ⟨phiTypeInput_holds, Checker.sizeBound, Checker.pieceShapeBase, Checker.subObjBase, Checker.familiesBase⟩

theorem thm115Inputs_holds : Thm115Inputs.{u} := thm115Open_holds.toInputs

/-- **N2 Proposition 1.17(b)** (= L6 `TVinePiecesInput`, L4 `PieceShapeInput`). -/
theorem pieceShape_holds : PieceShapeStatement.{u, v} :=
  pieceShape_of_L2 Checker.sizeBound Checker.pieceShapeBase

/-- **N3 Theorem 6 (i)–(iii)** (= L4 `LayervineInput`). -/
theorem layervine_holds : LayervineStatement.{u, v} :=
  layervine_of_L2 Checker.sizeBound Checker.pieceShapeBase

/-- **N2 Theorem 1.15 (F1)–(F6)** (= L5c / L07 `SubObjectsInput`). -/
theorem subObjects_holds : SubObjectsStatement.{u, v} := subObjects thm115Inputs_holds

/-- **N3 Corollary 1.16′ (1)–(3)** (= L6 `Cor116PrimeInput`). -/
theorem cor116Single_holds : Cor116SingleStatement.{u, v} := cor116Single thm115Inputs_holds

end WaveTurbulence.TVine.Struct
