/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.InsertMiniTree
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.ForestGrafting

/-! # Raw source tree surgery agrees with the COMB replacement primitives -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- The audited B2 replacement function equals COMB's checked replacement primitive. -/
theorem setAt_eq_replaceAt (t : TTree) (p : Path) (s : TTree) :
    t.setAt p s = Comb.replaceAt t p s := by
  cases p with
  | nil => simp only [TTree.setAt,Comb.replaceAt]
  | cons i p =>
    cases t with
    | leaf => rfl
    | node l m r =>
      fin_cases i <;> simp [TTree.setAt,Comb.replaceAt,
        setAt_eq_replaceAt l,setAt_eq_replaceAt m,setAt_eq_replaceAt r]
termination_by structural t

end WaveTurbulence.Reg
