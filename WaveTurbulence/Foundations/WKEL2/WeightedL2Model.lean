/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SchwartzWeightInverse

/-!
# The Banach model of the frozen weighted L² space

An element u of ordinary real L² represents f(k) = ⟨k⟩⁻ˢ u(k). The encode,
decode, membership, and norm identities below identify this model with the
source weighted space. The model norm is proved equal to `weightedL2Norm`.
-/

public section

noncomputable section

open MeasureTheory

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Decode a weighted L² coefficient into a Borel representative of the original function. -/
@[expose] def weightedL2Decode (s : ℝ) (u : Lp ℝ 2 (volume : Measure (Mom d))) : Mom d → ℝ :=
  weightedFunction (-s) u

/-- Encode a function with actual weighted L² membership into the Banach model. -/
@[expose] def weightedL2Encode (s : ℝ) (f : Mom d → ℝ) (hf : MemLp (weightedFunction s f) 2) :
    Lp ℝ 2 (volume : Measure (Mom d)) := hf.toLp (weightedFunction s f)

theorem measurable_weightedL2Decode (s : ℝ) (u : Lp ℝ 2 (volume : Measure (Mom d))) :
    Measurable (weightedL2Decode s u) :=
  measurable_weightedFunction (-s) (Lp.stronglyMeasurable u).measurable

theorem weightedFunction_decode (s : ℝ) (u : Lp ℝ 2 (volume : Measure (Mom d))) :
    weightedFunction s (weightedL2Decode s u) = (u : Mom d → ℝ) := by
  funext k
  exact weightedFunction_neg_cancel s u k

theorem memLp_weightedL2Decode (s : ℝ) (u : Lp ℝ 2 (volume : Measure (Mom d))) :
    MemLp (weightedFunction s (weightedL2Decode s u)) 2 := by
  rw [weightedFunction_decode]
  exact Lp.memLp u

/-- Encoding after decoding gives exactly the original L² class. -/
theorem weightedL2Encode_decode (s : ℝ) (u : Lp ℝ 2 (volume : Measure (Mom d))) :
    weightedL2Encode s (weightedL2Decode s u) (memLp_weightedL2Decode s u) = u := by
  apply Lp.ext
  exact (memLp_weightedL2Decode s u).coeFn_toLp.trans
    (Filter.Eventually.of_forall fun k => congrFun (weightedFunction_decode s u) k)

/-- Decoding after encoding preserves the original function almost everywhere. -/
theorem weightedL2Decode_encode (s : ℝ) (f : Mom d → ℝ) (hf : MemLp (weightedFunction s f) 2) :
    weightedL2Decode s (weightedL2Encode s f hf) =ᵐ[volume] f := by
  filter_upwards [hf.coeFn_toLp] with k hk
  change weightedFunction (-s) (hf.toLp (weightedFunction s f)) k = f k
  calc
    _ = weightedFunction (-s) (weightedFunction s f) k := by
      exact congrArg (fun r : ℝ => (1 + ‖k‖ ^ 2) ^ ((-s) / 2) * r) hk
    _ = _ := by simpa only [neg_neg] using weightedFunction_neg_cancel (-s) f k

/-- The Banach model's norm equals the exact frozen norm of its decoded function. -/
theorem weightedL2Norm_decode (s : ℝ) (u : Lp ℝ 2 (volume : Measure (Mom d))) :
    weightedL2Norm s (weightedL2Decode s u) = ‖u‖ := by
  rw [weightedL2Norm_eq_norm_toLp s _ (memLp_weightedL2Decode s u)]
  exact congrArg norm (weightedL2Encode_decode s u)

/-- Encoding a genuine weighted L² function preserves exactly its frozen norm. -/
theorem norm_weightedL2Encode (s : ℝ) (f : Mom d → ℝ) (hf : MemLp (weightedFunction s f) 2) :
    ‖weightedL2Encode s f hf‖ = weightedL2Norm s f :=
  (weightedL2Norm_eq_norm_toLp s f hf).symm

end WaveTurbulence.WKEL2
