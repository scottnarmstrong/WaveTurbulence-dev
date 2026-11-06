/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.ProdDyadicCut
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.InstFintypeGNode
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenIsFlowerNode
public import WaveTurbulence.Frozen.Defs.LayeredGardenIsTopLeaf
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.TTreeNodes
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# LayeredGarden.cutWeight1P

Wave B tier B1 (flower cutoff successor, R62), source: T L2283; DH21 L2731. Frozen by ruling D13
(`docs/DECISIONS.md#D13`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)
variable {d : ℕ}

open Classical in
/-- The `M₁` weight, product form (T L2283, L2294; DH21 L2731): per tree, `Ψ_{j₁}` of the norms of the
non-flower top leaves. -/
noncomputable def cutWeight1P (p : ℕ) (L : ℝ) (j₁ : ℕ) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ j : Fin w, prodDyadicCut L j₁ (Finset.univ.filter fun a : GNode LG.garden.tree =>
    a.1.1 = j ∧ LG.IsTopLeaf p a ∧ ¬ LG.IsFlowerNode a) (fun a => ‖k a‖)

end LayeredGarden
end WaveTurbulence
