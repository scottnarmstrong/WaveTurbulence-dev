/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Slot

/-!
# slotOrder

Wave B tier B1 (WaveB1-System.lean), source: (file) WAVE-B §2.3; T L545–L564; T Def `defcm`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Duhamel

variable (L γ δ : ℝ) {d : ℕ}

def slotOrder {Ntr : ℕ} (x : Slot Ntr × Slot Ntr × Slot Ntr) : ℕ :=
  ([x.1, x.2.1, x.2.2].map fun o => o.elim 0 (fun N => (N : ℕ))).sum

end Duhamel
end WaveTurbulence
