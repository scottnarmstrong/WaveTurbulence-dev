/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# MarkTag

Wave B tier B1 (WaveB1-Core.lean), source: WAVE-B v2 §2.2.2; T (timepairtree); T (kqflower). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

/-- The tag of a marked (unpaired) leaf (WAVE-B v2 §2.2.2): `lower` for the lone leaf of a paired
tree (domain constraint `t_{ℓ_lo^pr} > s`, T (timepairtree)), `equal` for a flower (`t_{𝔣^pr} := s`,
T (kqflower)). -/
inductive MarkTag : Type
  | lower : MarkTag
  | equal : MarkTag

end WaveTurbulence
