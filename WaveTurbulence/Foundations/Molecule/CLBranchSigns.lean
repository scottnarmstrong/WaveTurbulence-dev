/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLBranchNames
import Mathlib.Tactic

/-! # Old child names preserve every branch sign under the splice -/

public section
namespace WaveTurbulence.Mole
open TTree

theorem contractionPoint_contract {V : Type*} [DecidableEq V] (S : Finset V)
    (a : V) (ha : a ∈ S) (v : ContractVertex S) :
    contractVertex S ((contractionPointEquiv S a ha) v).1 = v := by
  cases v with
  | none => exact (contractVertex_eq_none S a).mpr ha
  | some v => exact dite_eq_right v.2

variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b)

theorem clSplicedBranchName_contract (c : GBranch (clSplicedGardenOfSlots hB hCL D).tree) :
    contractVertex S (clSplicedBranchNameEquiv hB hCL D c).1 = clSplicedBranchEquiv hB hCL D c :=
  contractionPoint_contract S a hB.2.1 _

theorem clSplicedBranchName_sign (c : GBranch (clSplicedGardenOfSlots hB hCL D).tree) :
    (clSplicedGardenOfSlots hB hCL D).sign c.toNode =
      G.sign (clSplicedBranchNameEquiv hB hCL D c).1.toNode := by
  classical
  by_cases hc : c = spliceCrownBranch (clSpliceBoundary hB hCL D)
  · subst c
    rw [clSplicedBranchName_crown]
    rfl
  · obtain ⟨p,rfl⟩ := spliceBranchPieceNew_surjective_except_crown (clSpliceBoundary hB hCL D) c hc
    rw [clSplicedBranchName_piece]
    cases p with
    | inl c => rfl
    | inr p =>
      obtain ⟨i,q⟩ := p
      have hs := clSignedBoundary_sign hB hCL D.excluded D.kept D.excluded_missing
        D.excluded_ne_middle D.kept_ne_middle i
      change nodeSign G.sig (a.1.1,a.1.2++i::q.1) =
        nodeSign G.sig (((clSpliceBoundary hB hCL D).node i).1.1,
          ((clSpliceBoundary hB hCL D).node i).1.2++q.1)
      have hnew : nodeSign G.sig (a.1.1,a.1.2++i::q.1) = pathSign (G.sign (a.child i)) q.1 := by
        change pathSign (G.sig a.1.1) (a.1.2++i::q.1) =
          pathSign (pathSign (G.sig a.1.1) (a.1.2++[i])) q.1
        simpa only [List.append_assoc,List.singleton_append] using
          Comb.pathSign_append (G.sig a.1.1) (a.1.2++[i]) q.1
      have hold : nodeSign G.sig (((clSpliceBoundary hB hCL D).node i).1.1,
          ((clSpliceBoundary hB hCL D).node i).1.2++q.1) =
          pathSign (G.sign ((clSpliceBoundary hB hCL D).node i)) q.1 := by
        simp only [nodeSign,pathSign,Garden.sign,List.count_append,pow_add,mul_assoc]
      rw [hnew,hold]
      exact congrArg (fun z : ℤˣ => pathSign z q.1) hs.symm

end WaveTurbulence.Mole
