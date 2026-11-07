/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceFactorTerms

/-!
# Exact source characters inside the standard lattice factors

The unrestricted shifted frequencies account for every lattice-linear
r term. These equalities contain the source half-scale conversion and
hold for arbitrary coefficient values, without any size hypothesis.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- The distinguished standard character has exactly the source linear phase. -/
theorem linearFactor_character_eq {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (ν : D.S.VIdx → Mom d) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) (i : Fin D.S.I) :
    (Real.fourierChar (inner ℝ (linearFactorFrequency D L γ δ ν r t τ i)
      (latticePoint L (x (D.S.x0Slot i)))) : ℂ) =
      (Real.fourierChar (inner ℝ (ν (D.S.x0Slot i)) (latticePoint L (x (D.S.x0Slot i)))) : ℂ) *
        piCharacter (linearSpatialExponent D L γ δ x r t τ i) := by
  simp_rw [fourierChar_eq_piCharacter_double]
  rw [← AddChar.map_add_eq_mul]
  apply congrArg piCharacter
  unfold linearFactorFrequency linearSpatialExponent sourceHalfScale
  simp only [inner_add_left,real_inner_smul_left]
  ring

/-- The bilinear standard character has exactly the source pair phase. -/
theorem pairFactor_character_eq {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (ν : D.S.VIdx → Mom d) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)) :
    (Real.fourierChar (inner ℝ (latticePoint L (x (D.S.xSlot a.1 a.2)))
        (pairFactorFrequencyX D L γ δ ν r t τ a) +
      inner ℝ (latticePoint L (x (D.S.ySlot a.1 a.2))) (pairFactorFrequencyY D L γ δ ν r t τ a) +
      pairFactorTime D L γ δ τ a*inner ℝ (latticePoint L (x (D.S.xSlot a.1 a.2)))
        (latticePoint L (x (D.S.ySlot a.1 a.2)))) : ℂ) =
      (Real.fourierChar (inner ℝ (ν (D.S.xSlot a.1 a.2)) (latticePoint L (x (D.S.xSlot a.1 a.2)))) : ℂ) *
      (Real.fourierChar (inner ℝ (ν (D.S.ySlot a.1 a.2)) (latticePoint L (x (D.S.ySlot a.1 a.2)))) : ℂ) *
        piCharacter (pairSpatialExponent D L γ δ x r t τ a) := by
  simp_rw [fourierChar_eq_piCharacter_double]
  rw [← AddChar.map_add_eq_mul,← AddChar.map_add_eq_mul]
  apply congrArg piCharacter
  unfold pairFactorFrequencyX pairFactorFrequencyY pairFactorTime pairSpatialExponent sourceHalfScale
  simp only [inner_add_right,real_inner_smul_right,real_inner_comm]
  ring

/-- The normal standard character retains exactly either source quadratic form. -/
theorem normalFactor_character_eq {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (ν : D.S.VIdx → Mom d) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) (i : {i : Fin D.S.I // D.S.nor i = true}) :
    (Real.fourierChar (normalFactorTime D L γ δ τ i 0 *
        inner ℝ (latticePoint L (x (D.S.uSlot i.1 i.2 0))) (latticePoint L (x (D.S.uSlot i.1 i.2 1))) +
      normalFactorTime D L γ δ τ i 1 * WeylSums.cubicQuadraticForm (D.Λsel i.1)
        (latticePoint L (x (D.S.uSlot i.1 i.2 0))) (latticePoint L (x (D.S.uSlot i.1 i.2 1)))
        (latticePoint L (x (D.S.uSlot i.1 i.2 2))) +
      ∑ j : Fin 3, inner ℝ (normalFactorFrequency D L γ δ ν r t τ i j)
        (latticePoint L (x (D.S.uSlot i.1 i.2 j)))) : ℂ) =
      (∏ j : Fin 3, (Real.fourierChar (inner ℝ (ν (D.S.uSlot i.1 i.2 j))
        (latticePoint L (x (D.S.uSlot i.1 i.2 j)))) : ℂ)) *
      piCharacter (normalSpatialExponent D L γ δ x r t τ i) := by
  rw [prod_fourierChar_eq_sum]
  simp_rw [fourierChar_eq_piCharacter_double]
  rw [← AddChar.map_add_eq_mul]
  apply congrArg piCharacter
  unfold normalFactorTime normalFactorFrequency normalSpatialExponent sourceHalfScale WeylSums.cubicQuadraticForm
  have ht0 : Fin.castLE (by omega : 2 ≤ 3) (0 : Fin 2) = (0 : Fin 3) := rfl
  have ht1 : Fin.castLE (by omega : 2 ≤ 3) (1 : Fin 2) = (1 : Fin 3) := rfl
  have hf0 : Fin.castLE (by omega : 3 ≤ 4) (0 : Fin 3) = (0 : Fin 4) := rfl
  have hf1 : Fin.castLE (by omega : 3 ≤ 4) (1 : Fin 3) = (1 : Fin 4) := rfl
  have hf2 : Fin.castLE (by omega : 3 ≤ 4) (2 : Fin 3) = (2 : Fin 4) := rfl
  simp only [Fin.sum_univ_three,inner_add_left,real_inner_smul_left,ht0,ht1,hf0,hf1,hf2]
  unfold coreTimeSign
  cases D.Λsel i.1 <;> simp <;> ring

end WaveTurbulence.SumintPar
