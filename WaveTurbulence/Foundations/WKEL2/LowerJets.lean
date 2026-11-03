/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetIntertwining

/-!
# Lower-order coordinate jets of a completed weighted Sobolev element
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Regard a coordinate word of order at most r as one of order at most m. -/
@[expose] def liftJetIndex {r m : ℕ} (hrm : r ≤ m) (i : JetIndex d r) : JetIndex d m :=
  ⟨⟨i.1.val, by have := i.1.isLt; omega⟩, i.2⟩

theorem liftJetIndex_self (m : ℕ) (i : JetIndex d m) : liftJetIndex le_rfl i = i := by
  rcases i with ⟨n, v⟩
  rfl

/-- The only order-zero coordinate is the empty word. -/
theorem jetIndex_zero_unique (i : JetIndex d 0) : i = zeroJetIndex d 0 := by
  rcases i with ⟨n, v⟩
  fin_cases n
  congr
  exact Subsingleton.elim _ _

/-- The finite lower-order L² jet, as a continuous linear map on a higher completion. -/
@[expose] def weightedSobolevLowerJetCLM (s : ℝ) (m r : ℕ) (hrm : r ≤ m) :
    WeightedSobolevSpace d s m →L[ℝ]
      (JetIndex d r → Lp ℝ 2 (volume : Measure (Mom d))) :=
  ContinuousLinearMap.pi fun i =>
    weightedSobolevCoordinateCLM (d := d) s m (liftJetIndex hrm i)

/-- Lower jets of Schwartz inputs are exactly their original weighted differential expressions. -/
theorem weightedSobolevLowerJetCLM_schwartz (s : ℝ) (m r : ℕ) (hrm : r ≤ m)
    (f : 𝓢(Mom d, ℝ)) :
    weightedSobolevLowerJetCLM s m r hrm (schwartzToWeightedSobolevCLM s m f) =
      weightedJetCLM s r f := by
  funext i
  change weightedSobolevCoordinateCLM s m (liftJetIndex hrm i)
    (schwartzToWeightedSobolevCLM s m f) = _
  rw [weightedSobolevCoordinateCLM_schwartz, weightedJetCLM_apply]
  rfl

/-- Every lower-order jet is bounded by the full completed norm. -/
theorem norm_weightedSobolevLowerJetCLM_le (s : ℝ) (m r : ℕ) (hrm : r ≤ m)
    (u : WeightedSobolevSpace d s m) : ‖weightedSobolevLowerJetCLM s m r hrm u‖ ≤ ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2
  intro i
  exact norm_weightedSobolevCoordinateCLM_le s m (liftJetIndex hrm i) u

/-- The full jet realizes the entire completed norm isometrically. -/
theorem norm_weightedSobolevLowerJetCLM_self (s : ℝ) (m : ℕ)
    (u : WeightedSobolevSpace d s m) : ‖weightedSobolevLowerJetCLM s m m le_rfl u‖ = ‖u‖ := by
  have H : weightedSobolevLowerJetCLM s m m le_rfl u = weightedSobolevJetIsometry s m u := by
    funext i
    change weightedSobolevJetIsometry s m u (liftJetIndex le_rfl i) = _
    rw [liftJetIndex_self]
  rw [H, (weightedSobolevJetIsometry s m).norm_map]

/-- The order-zero lower-jet norm is exactly the base weighted L² norm. -/
theorem norm_weightedSobolevLowerJetCLM_zero (s : ℝ) (m : ℕ)
    (u : WeightedSobolevSpace d s m) :
    ‖weightedSobolevLowerJetCLM s m 0 (Nat.zero_le m) u‖ = ‖weightedSobolevToL2CLM s m u‖ := by
  let : Nonempty (JetIndex d 0) := ⟨zeroJetIndex d 0⟩
  have H : weightedSobolevLowerJetCLM s m 0 (Nat.zero_le m) u =
      fun _ => weightedSobolevToL2CLM s m u := by
    funext i
    rw [jetIndex_zero_unique i]
    rfl
  rw [H, pi_norm_const]

end WaveTurbulence.WKEL2
