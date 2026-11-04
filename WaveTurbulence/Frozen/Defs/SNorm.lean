/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.IterPartial
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# SNorm

Wave B tier B1 (WaveB1-System.lean), source: (file) WAVE-B §2.3; T L545–L564; T Def `defcm`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Norms

variable {d : ℕ}

open Classical in
/-- The weighted `C^{Λ₁}` sup quantity `max_{|ρ| ≤ Λ₁} sup_k ⟨k⟩^{Λ₂} |∂^ρ F(k)|`, `⊤` unless
`Λ₁ = 0` or `F` is `C^{Λ₁}`. For `Λ₁ = 0` it is `sup_k ⟨k⟩^{Λ₂} |F(k)|` with no regularity, as in the
source (normX2) and the landed `spatialNorm` (fix 5; as for `XNorm`, CL-13). Reading for `Λ₁ ≥ 1`
(stage-2 O5): classical derivatives; a function with bounded but discontinuous top-order partials has
a finite source norm but `⊤` here. All consumers have `Λ₁ ≥ 1` and supply `C^{Λ₁}` functions, and for
`Λ₁ ≠ 0` a finite value forces `C^{Λ₁}` (`contDiff_of_SNormR_lt_top`). -/
noncomputable def SNorm (Λ₁ Λ₂ : ℕ) (F : Mom d → ℂ) : ℝ≥0∞ :=
  if Λ₁ = 0 ∨ ContDiff ℝ Λ₁ F then
    ⨆ (ρ : Fin d → ℕ) (_ : ∑ j, ρ j ≤ Λ₁) (k : Mom d),
      ENNReal.ofReal (jbr k ^ Λ₂ * ‖iterPartial ρ F k‖)
  else ⊤

end Norms
end WaveTurbulence
