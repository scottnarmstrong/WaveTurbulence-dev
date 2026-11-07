/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SignSearchEquations

/-! # The constructed predecessor has the same sign and lies strictly below -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

theorem signHeavySearch_target (sig : Fin w → ℤˣ) (ζ : ℤˣ) (v u : GBranch tree)
    (hu : (signHeavySearch sig ζ v).2 = some u) :
    nodeSign sig u.1 = ζ ∧ v.1.2.length < u.1.2.length ∧ v.toNode.IsDesc u.toNode := by
  induction hm : branchDepthBound tree-v.1.2.length using Nat.strong_induction_on generalizing v with
  | h n ih =>
    cases hn : nextHeavyBranch v with
    | none =>
      rw [signHeavySearch_none sig ζ v hn] at hu
      cases hu
    | some z =>
      by_cases hz : nodeSign sig z.1 = ζ
      · rw [signHeavySearch_same sig ζ hn hz] at hu
        have he := Option.some.inj hu
        subst u
        exact ⟨hz,by have hd := nextHeavyBranch_depth hn; omega,nextHeavyBranch_desc hn⟩
      · rw [signHeavySearch_different sig ζ hn hz] at hu
        have hlt : branchDepthBound tree-z.1.2.length < n := by
          rw [← hm]
          exact nextHeavyBranch_measure_lt hn
        have ht := ih _ hlt z hu rfl
        exact ⟨ht.1,by have hd := nextHeavyBranch_depth hn; omega,(nextHeavyBranch_desc hn).trans ht.2.2⟩

/-- Source typing and ordering of the subtraction-only predecessor are proved
from the terminating search, with no predecessor witness as a premise. -/
theorem signPredecessor_target (sig : Fin w → ℤˣ) (v u : GBranch tree)
    (hu : signPredecessor sig v = some u) :
    nodeSign sig u.1 = nodeSign sig v.1 ∧ v.1.2.length < u.1.2.length ∧ v.toNode.IsDesc u.toNode :=
  signHeavySearch_target sig _ v u hu

end WaveTurbulence.VineEstS2
