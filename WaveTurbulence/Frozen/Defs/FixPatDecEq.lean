/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.FixPat

/-!
# FixPat.decEq

Wave B tier B1 (WaveB1-Flower.lean), source: (file) T L2327; T L2283–L2285; T L2331. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- Decidable equality of patterns, written out as for `TTree` and `MarkTag` (CL-17/CL-18: no `deriving` in the
freeze set). -/
def FixPat.decEq : (a b : FixPat) → Decidable (a = b)
  | .plain, .plain => isTrue rfl
  | .plain, .dRoot => isFalse fun h => FixPat.noConfusion h
  | .plain, .dParent => isFalse fun h => FixPat.noConfusion h
  | .plain, .dChild _ => isFalse fun h => FixPat.noConfusion h
  | .dRoot, .plain => isFalse fun h => FixPat.noConfusion h
  | .dRoot, .dRoot => isTrue rfl
  | .dRoot, .dParent => isFalse fun h => FixPat.noConfusion h
  | .dRoot, .dChild _ => isFalse fun h => FixPat.noConfusion h
  | .dParent, .plain => isFalse fun h => FixPat.noConfusion h
  | .dParent, .dRoot => isFalse fun h => FixPat.noConfusion h
  | .dParent, .dParent => isTrue rfl
  | .dParent, .dChild _ => isFalse fun h => FixPat.noConfusion h
  | .dChild _, .plain => isFalse fun h => FixPat.noConfusion h
  | .dChild _, .dRoot => isFalse fun h => FixPat.noConfusion h
  | .dChild _, .dParent => isFalse fun h => FixPat.noConfusion h
  | .dChild i, .dChild j =>
    if h : i = j then isTrue (h ▸ rfl) else isFalse fun e => h (FixPat.dChild.inj e)

end WaveTurbulence
