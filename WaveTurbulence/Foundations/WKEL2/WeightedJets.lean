/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SchwartzWeightInverse
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Finite weighted derivative and moment jets

The two letters are coordinate multiplication and coordinate differentiation.
Ordered words retain the exact Leibniz identities without suppressing their
multiplicities. All words of length at most m form a finite jet in weighted L².
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap LineDeriv

namespace WaveTurbulence.WKEL2

/-- Coordinate moment letters and coordinate derivative letters. -/
abbrev JetLetter (d : ℕ) := Fin d ⊕ Fin d

variable {d : ℕ}

/-- Coordinate multiplication on Schwartz space. -/
@[expose] def coordinateWeightCLM (i : Fin d) : 𝓢(Mom d, ℝ) →L[ℝ] 𝓢(Mom d, ℝ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ).flip
    (EuclideanSpace.proj i).hasTemperateGrowth

theorem coordinateWeightCLM_apply (i : Fin d) (f : 𝓢(Mom d, ℝ)) (k : Mom d) :
    coordinateWeightCLM i f k = k i * f k := by
  rw [coordinateWeightCLM, SchwartzMap.bilinLeftCLM_apply]
  rfl

/-- The Schwartz operator associated to one coordinate letter. -/
@[expose] def jetLetterCLM : JetLetter d → 𝓢(Mom d, ℝ) →L[ℝ] 𝓢(Mom d, ℝ)
  | .inl i => coordinateWeightCLM i
  | .inr i => LineDeriv.lineDerivOpCLM ℝ 𝓢(Mom d, ℝ) (EuclideanSpace.single i (1 : ℝ) : Mom d)

/-- Compose a word of moment and derivative operators, from right to left. -/
@[expose] def jetWordCLM : List (JetLetter d) → 𝓢(Mom d, ℝ) →L[ℝ] 𝓢(Mom d, ℝ)
  | [] => ContinuousLinearMap.id ℝ _
  | a :: w => (jetLetterCLM a).comp (jetWordCLM w)

theorem jetWordCLM_nil (f : 𝓢(Mom d, ℝ)) : jetWordCLM [] f = f := rfl

theorem jetWordCLM_cons (a : JetLetter d) (w : List (JetLetter d)) (f : 𝓢(Mom d, ℝ)) :
    jetWordCLM (a :: w) f = jetLetterCLM a (jetWordCLM w f) := rfl

/-- Finite index set of all coordinate words of order at most m. -/
abbrev JetIndex (d m : ℕ) := Σ n : Fin (m + 1), Fin n → JetLetter d

/-- The empty word is a distinguished jet coordinate. -/
@[expose] def zeroJetIndex (d m : ℕ) : JetIndex d m := ⟨⟨0, by omega⟩, Fin.elim0⟩

/-- Weighted L² jets of Schwartz functions, with the finite product supremum norm. -/
@[expose] def weightedJetCLM (s : ℝ) (m : ℕ) :
    𝓢(Mom d, ℝ) →L[ℝ] (JetIndex d m → Lp ℝ 2 (volume : Measure (Mom d))) :=
  ContinuousLinearMap.pi fun i => (weightedToL2CLM s).comp (jetWordCLM (List.ofFn i.2))

theorem weightedJetCLM_apply (s : ℝ) (m : ℕ) (f : 𝓢(Mom d, ℝ)) (i : JetIndex d m) :
    weightedJetCLM s m f i = weightedToL2CLM s (jetWordCLM (List.ofFn i.2) f) := rfl

/-- The zero jet is the exact original weighted embedding. -/
theorem weightedJetCLM_zero (s : ℝ) (m : ℕ) (f : 𝓢(Mom d, ℝ)) :
    weightedJetCLM s m f (zeroJetIndex d m) = weightedToL2CLM s f := by
  simp only [weightedJetCLM_apply, zeroJetIndex, List.ofFn_zero, jetWordCLM_nil]

/-- The finite jet map is faithful, including at m = 0. -/
theorem weightedJetCLM_injective (s : ℝ) (m : ℕ) :
    Function.Injective (weightedJetCLM (d := d) s m) := by
  intro f g h
  apply weightedToL2CLM_injective s
  simpa only [weightedJetCLM_zero] using congrFun h (zeroJetIndex d m)

/-- Every coordinate norm is precisely a frozen weighted L² norm. -/
theorem norm_weightedJetCLM_coordinate (s : ℝ) (m : ℕ) (f : 𝓢(Mom d, ℝ))
    (i : JetIndex d m) :
    ‖weightedJetCLM s m f i‖ = weightedL2Norm s (jetWordCLM (List.ofFn i.2) f) := by
  rw [weightedJetCLM_apply, norm_weightedToL2CLM]

end WaveTurbulence.WKEL2
