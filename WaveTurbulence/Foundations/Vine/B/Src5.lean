/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Src4
import Mathlib.Tactic

/-!
# VINE-B Part II (5): the exterior clocks of a unit (the `G_sb`-level content of G1)

For `τ` in `splicedTimeDomain Gsb lay tt`:
* the hinge clock `τ_{u1}` lies in `[lay u1, lay u1 + 1]`;
* a boundary child of the hinge that is a branch node `c` of `G_sb` has clock `τ c < τ_{u1}` and `τ c ∈ [lay c, lay c + 1]`;
* a boundary child that is a leaf has the root time `tt r` of its tree as `hclk`, and then `τ_{u1} < tt r`
  (the inequality is REVERSED with respect to the `outBox` condition `max (t_{u21}) (t_{u22}) < t_{u1}`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents WaveTurbulence.LGSpine

variable {w : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

/-- The hinge clock lies in its layer interval. -/
theorem hinge_clock_box (hd : Disj blk) (j : J) (tt : Fin w → ℝ) (lay : GBranch Gsb.tree → ℕ)
    {τ : GBranch Gsb.tree → ℝ} (hτ : τ ∈ splicedTimeDomain Gsb lay tt) :
    clockOf Gsb tt τ (Φ.hclk hd j 0) ∈ Set.Icc (lay (Φ.hinge hd j) : ℝ) (lay (Φ.hinge hd j) + 1) :=
  hτ.1 _

/-- A boundary child of the hinge that is a branch node `c` of `G_sb`: its clock is below the hinge clock and in its
layer interval. -/
theorem child_clock (hd : Disj blk) (j : J) (i : Fin 4) (hi : i ≠ 0) (tt : Fin w → ℝ)
    (lay : GBranch Gsb.tree → ℕ) {τ : GBranch Gsb.tree → ℝ} (hτ : τ ∈ splicedTimeDomain Gsb lay tt)
    (c : GBranch Gsb.tree) (hc : nodeClk Gsb (Φ.hmom hd j i) = Sum.inr c) :
    τ c < τ (Φ.hinge hd j) ∧ τ c ∈ Set.Icc (lay c : ℝ) (lay c + 1) := by
  refine ⟨?_, hτ.1 c⟩
  obtain ⟨k, hk⟩ := Φ.hmom_child hd j i hi
  have hcy : c.1 = (Φ.hmom hd j i).1 := by
    unfold nodeClk at hc
    by_cases h : (Φ.hmom hd j i).1.2 ∈ (Gsb.tree (Φ.hmom hd j i).1.1).branching
    · rw [dif_pos h] at hc
      exact (congrArg Subtype.val (Sum.inr.inj hc)).symm
    · rw [dif_neg h] at hc
      exact absurd hc (by simp)
  apply hτ.2.1
  refine ⟨?_, k, ?_⟩
  · rw [hcy, hk]; rfl
  · rw [hcy, hk]; rfl

end SpliceShape

end WaveTurbulence.VineB
