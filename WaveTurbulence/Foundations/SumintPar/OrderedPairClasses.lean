/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.OrderedPairFactors

/-!
# The three actual pair classes in the source reduction

Only the first pair of a case-(a) block keeps an ordering strip. Only
the first pair of a case-(c) block has the fractional gap amplitude.
All remaining pairs have the ordinary norm factor.
-/

@[expose] public section
set_option autoImplicit false

open scoped Classical

namespace WaveTurbulence.SumintPar

/-- The first pair of a case-(c) source block. -/
@[expose] def caseCPair {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) : Prop :=
  D.S.nor a.1 = false ∧ D.badKind a.1 = 2 ∧ (a.2:ℕ) = 0

/-- The two special first-pair classes are disjoint. -/
theorem not_caseCPair_of_caseAPair {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a) : ¬ caseCPair D a := by
  intro hc
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  exact h02 (ha.2.1.symm.trans hc.2.1)

/-- A fractional-gap first pair has no ordering multiplier. -/
theorem not_caseAPair_of_caseCPair {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (hc : caseCPair D a) : ¬ caseAPair D a :=
  fun ha => not_caseCPair_of_caseAPair D a ha hc

/-- The gap amplitude is one outside the case-(c) first-pair position. -/
theorem pairGapAmplitude_eq_one_of_not_caseCPair {d : ℕ} (D : SumintDatum d) (η : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (hc : ¬ caseCPair D a) (z : ℝ × ℝ) :
    pairGapAmplitude D η a z = 1 := by
  unfold pairGapAmplitude
  exact ite_eq_right hc

/-- The gap amplitude at a case-(c) first pair is exactly the printed source power. -/
theorem pairGapAmplitude_eq_rpow_of_caseCPair {d : ℕ} (D : SumintDatum d) (η : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (hc : caseCPair D a) (z : ℝ × ℝ) :
    pairGapAmplitude D η a z = |z.1-z.2|^(1-3*η) := by
  unfold pairGapAmplitude
  exact ite_eq_left hc

/-- The literal ordered first-pair factor in case (a). -/
theorem orderedPairNorm_eq_case_a {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a) (z : ℝ × ℝ) :
    orderedPairNorm D L γ δ η p ν r t u a z =
      if |z.1-u a.1| ≤ |z.1-z.2| then ‖pairTimeSum D L γ δ p ν r t a z‖ else 0 := by
  unfold orderedPairNorm
  rw [ite_eq_left ha,pairGapAmplitude_eq_one_of_not_caseCPair D η a (not_caseCPair_of_caseAPair D a ha),one_mul]

/-- The literal weighted first-pair factor in case (c). -/
theorem orderedPairNorm_eq_case_c {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (hc : caseCPair D a) (z : ℝ × ℝ) :
    orderedPairNorm D L γ δ η p ν r t u a z =
      |z.1-z.2|^(1-3*η)*‖pairTimeSum D L γ δ p ν r t a z‖ := by
  unfold orderedPairNorm
  rw [ite_eq_right (not_caseAPair_of_caseCPair D a hc),pairGapAmplitude_eq_rpow_of_caseCPair D η a hc]

end WaveTurbulence.SumintPar
