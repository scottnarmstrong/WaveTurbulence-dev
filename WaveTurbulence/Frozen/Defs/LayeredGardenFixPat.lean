/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.FixPat
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchIsChildOf
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIsFlowerParent
public import WaveTurbulence.Frozen.Defs.InstDecidableIsFlowerParent
public import WaveTurbulence.Frozen.Defs.InstFintypeGBranch
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.TTreeBranching
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# LayeredGarden.fixPat

Wave B tier B1 (WaveB1-Flower.lean), source: T L2264. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

open Classical in
/-- **The fixed times** of the pattern vector `pat` (T L2264, L2312, L2331): flower parents ↦ `s`,
and per tree `j`, according to `pat j`, the root ↦ `t` or a neighbour of `𝔣^pr` ↦ `s`. -/
noncomputable def fixPat (pat : Fin w → FixPat) (t s : ℝ) (b : GBranch LG.garden.tree) : Option ℝ :=
  if LG.garden.IsFlowerParent b then some s else
  match pat b.1.1 with
  | .plain => none
  | .dRoot => if b.1.2 = [] then some t else none
  | .dParent => if ∃ c : GBranch LG.garden.tree, LG.garden.IsFlowerParent c ∧ c.IsChildOf b
      then some s else none
  | .dChild i => if ∃ c : GBranch LG.garden.tree, LG.garden.IsFlowerParent c ∧ b.1.1 = c.1.1 ∧
      b.1.2 = c.1.2 ++ [i] then some s else none

end LayeredGarden
end WaveTurbulence
