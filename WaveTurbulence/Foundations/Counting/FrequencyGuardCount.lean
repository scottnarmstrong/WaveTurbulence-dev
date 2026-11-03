/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.LatticeBox
public import WaveTurbulence.Foundations.NumberTheory.FrequencyGuardGeometry
import Mathlib.Tactic

/-!
# Counting actual integer frequencies in endpoint guard intervals

Two endpoint neighborhoods of radius D contain at most 4D+2 integer
frequencies, independently of the truncation set and the endpoint values.
-/

public section

namespace WaveTurbulence.Counting

/-- Any finite selection from two real-centered guard intervals obeys
their combined length plus two bound. -/
theorem card_frequency_guards_le (T : Finset ℤ) (alpha beta : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    ((T.filter (fun nu : ℤ => |(nu:ℝ)-alpha| ≤ D ∨ |(nu:ℝ)-beta| ≤ D)).card:ℝ) ≤
      4*D+2 := by
  classical
  have hsub : T.filter (fun nu : ℤ => |(nu:ℝ)-alpha| ≤ D ∨ |(nu:ℝ)-beta| ≤ D) ⊆
      integerInterval (alpha-D) (alpha+D) ∪ integerInterval (beta-D) (beta+D) := by
    intro nu hnu
    rcases (Finset.mem_filter.mp hnu).2 with ha | hb
    · apply Finset.mem_union_left
      exact (mem_integerInterval _ _ _).mpr (by rcases abs_le.mp ha with ⟨ha1,ha2⟩; constructor <;> linarith)
    · apply Finset.mem_union_right
      exact (mem_integerInterval _ _ _).mpr (by rcases abs_le.mp hb with ⟨hb1,hb2⟩; constructor <;> linarith)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hc : ((T.filter (fun nu : ℤ => |(nu:ℝ)-alpha| ≤ D ∨ |(nu:ℝ)-beta| ≤ D)).card:ℝ) ≤
      (integerInterval (alpha-D) (alpha+D)).card+(integerInterval (beta-D) (beta+D)).card := by
    exact_mod_cast hcard
  have ha := card_integerInterval_le alpha hD
  have hb := card_integerInterval_le beta hD
  linarith only [hc,ha,hb]

end WaveTurbulence.Counting
