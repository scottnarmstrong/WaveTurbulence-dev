/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.Stage1Gate
import Mathlib.Tactic

/-!
# S2 REPRESENTS: local transcription of the amended Stage 1 gate (AMEND6′+9+10, rulings R54/R55/R56)

LG-SPINE folds two amendments into AMEND6′ (announced as "AMEND6′+9+10"); until the announcement S2 states them
locally, with the exact intended text, and re-pins afterwards:
* **AMEND9 (R54, R55).** In `Stage1Piece.RepresentsInt` the bad-vine gain is `L^{-(η²/2) b_sk}` (V5's
  `VineEstCanonLayerHalf`), not `L^{-η² b_sk}`.  No later use consumes the gain (`class_piece_bound` discards it).
* **AMEND10 (R56, finding F-COUNT3).** `Stage1Counts` clauses (iii) (`≤ 6^N` pieces per class) and (iv) (class count)
  are replaced by one direct piece count `#{π | ḡ = g ∧ ρ̄ = r} ≤ 3^N C₀^N (C₀ r)! (C₀ R)! C₂^{g+r}` (TARGET L2251:
  the terms `K^eqc` are counted by gardens; LF twists replace `(T′, Q′)` so the finer classes are not `≤ 2^n`).
Everything else is textually the AMEND6′ gate of lg-spine-u (`Stage1Gate.lean`, build-fresh-a6g).
-/

@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset
open scoped Classical

/-- AMEND9: `Stage1Piece.RepresentsInt` with the halved bad-vine gain `-(η²/2) b_sk`. -/
def Stage1Piece.RepresentsIntA {P : WTParams} {R : ℕ} (π : Stage1Piece P R) (n : ℕ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (val : ℂ) : Prop :=
  ∃ (Ξ : Type) (_ : MeasurableSpace Ξ) (μ : Measure Ξ) (w : Ξ → ℂ)
    (ctr : Ξ → GardenDart π.Gsb → Mom P.d)
    (edge : Ξ → GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : Ξ → (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ)
    (freq : Ξ → GBranch π.Gsb.tree → ℝ),
    Integrable (fun ξ => w ξ * splicedKernel π.Gsb (π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots) μ ∧
    val = ∫ ξ, w ξ * splicedKernel π.Gsb (π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots ∂μ ∧
    Integrable (fun ξ => ‖w ξ‖) μ ∧
    (∫ ξ, ‖w ξ‖ ∂μ ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
        P.η ^ 7 * (π.Cs.hinges.card : ℝ)) * s) ∧
    ∀ ξ, SplicedAmplitudeBounds π.Gsb (π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))

end WaveTurbulence.LGSpine
