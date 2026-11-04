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

/-- The raw A-step is precisely two grafts at the original two leaf addresses. -/
theorem raw_opA_forest (R : RawCpl) (ℓ q : GLeaf R.tree) (hne : q ≠ ℓ) (c : MiniCplCode) :
    (R.opA ℓ.1 q.1 c).tree =
      Comb.graftLeafPairForest R.tree ℓ q hne (.node .leaf .leaf .leaf) (.node .leaf .leaf .leaf) := by
  funext j
  obtain ⟨⟨i,p⟩,hi⟩ := ℓ
  obtain ⟨⟨k,r⟩,hk⟩ := q
  fin_cases i <;> fin_cases k <;> fin_cases j <;>
    simp [RawCpl.opA,RawCpl.mapTree,RawCpl.tree,
      Comb.graftLeafPairForest,Comb.graftLeafForest,Comb.graftLeafForest_other,
      Function.update,setAt_eq_replaceAt]

end WaveTurbulence.Reg
