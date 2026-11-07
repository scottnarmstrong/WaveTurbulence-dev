/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceFactorCharacters
public import WaveTurbulence.Foundations.SumintPar.InputProducts

/-!
# Pointwise product of the independent source factors

The coordinate cutoff/character product is reindexed through the exact
slot bijection. The spatial characters then multiply to the character
of the complete lattice-dependent source exponent.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- The independent cutoff and Fourier character at one actual input coordinate. -/
@[expose] noncomputable def coordinateInputFactor {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (v : D.S.VIdx) (n : Fin d → ℤ) : ℂ :=
  (inputCutoff (p v) (latticePoint L n) : ℂ)*(Real.fourierChar (inner ℝ (ν v) (latticePoint L n)) : ℂ)

/-- The coordinate product is the literal inserted cutoff times input modulation. -/
theorem prod_coordinateInputFactor {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (x : D.S.VIdx → Fin d → ℤ) :
    (∏ v, coordinateInputFactor D L p ν v (x v)) =
      ((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ) : ℂ)*inputCharacter D L ν x := by
  unfold coordinateInputFactor inputCharacter
  rw [Finset.prod_mul_distrib,Complex.ofReal_prod]

/-- The actual linear summand splits into its coordinate factor and spatial character. -/
theorem linearFactorTerm_at_input {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (x : D.S.VIdx → Fin d → ℤ)
    (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) (i : Fin D.S.I) :
    linearFactorTerm D L γ δ p ν r t τ i (x (D.S.x0Slot i)) =
      coordinateInputFactor D L p ν (D.S.x0Slot i) (x (D.S.x0Slot i))*
        piCharacter (linearSpatialExponent D L γ δ x r t τ i) := by
  unfold linearFactorTerm coordinateInputFactor
  rw [linearFactor_character_eq]
  ring

/-- The actual pair summand splits into its two coordinate factors and spatial character. -/
theorem pairFactorTerm_at_input {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (x : D.S.VIdx → Fin d → ℤ)
    (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)) :
    pairFactorTerm D L γ δ p ν r t τ a (x (D.S.xSlot a.1 a.2),x (D.S.ySlot a.1 a.2)) =
      (coordinateInputFactor D L p ν (D.S.xSlot a.1 a.2) (x (D.S.xSlot a.1 a.2))*
        coordinateInputFactor D L p ν (D.S.ySlot a.1 a.2) (x (D.S.ySlot a.1 a.2)))*
        piCharacter (pairSpatialExponent D L γ δ x r t τ a) := by
  let A : ℂ := ((inputCutoff (p (D.S.xSlot a.1 a.2)) (latticePoint L (x (D.S.xSlot a.1 a.2)))*
    inputCutoff (p (D.S.ySlot a.1 a.2)) (latticePoint L (x (D.S.ySlot a.1 a.2))) : ℝ) : ℂ)
  have hh : pairFactorTerm D L γ δ p ν r t τ a (x (D.S.xSlot a.1 a.2),x (D.S.ySlot a.1 a.2)) =
      A*((Real.fourierChar (inner ℝ (ν (D.S.xSlot a.1 a.2))
        (latticePoint L (x (D.S.xSlot a.1 a.2)))) : ℂ)*
        (Real.fourierChar (inner ℝ (ν (D.S.ySlot a.1 a.2))
          (latticePoint L (x (D.S.ySlot a.1 a.2)))) : ℂ)*
        piCharacter (pairSpatialExponent D L γ δ x r t τ a)) :=
    congrArg (fun z : ℂ => A*z) (pairFactor_character_eq D L γ δ ν x r t τ a)
  rw [hh]
  dsimp [A]
  unfold coordinateInputFactor
  rw [Complex.ofReal_mul]
  ring

/-- The actual normal summand splits into its three coordinate factors and spatial character. -/
theorem normalFactorTerm_at_input {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (x : D.S.VIdx → Fin d → ℤ)
    (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) (i : {i : Fin D.S.I // D.S.nor i = true}) :
    normalFactorTerm D L γ δ p ν r t τ i (fun j => x (D.S.uSlot i.1 i.2 j)) =
      (∏ j : Fin 3, coordinateInputFactor D L p ν (D.S.uSlot i.1 i.2 j) (x (D.S.uSlot i.1 i.2 j)))*
        piCharacter (normalSpatialExponent D L γ δ x r t τ i) := by
  let A : ℂ := ((∏ j : Fin 3, inputCutoff (p (D.S.uSlot i.1 i.2 j))
    (latticePoint L (x (D.S.uSlot i.1 i.2 j))) : ℝ) : ℂ)
  have hh : normalFactorTerm D L γ δ p ν r t τ i (fun j => x (D.S.uSlot i.1 i.2 j)) =
      A*((∏ j : Fin 3, (Real.fourierChar (inner ℝ (ν (D.S.uSlot i.1 i.2 j))
        (latticePoint L (x (D.S.uSlot i.1 i.2 j)))) : ℂ))*
        piCharacter (normalSpatialExponent D L γ δ x r t τ i)) :=
    congrArg (fun z : ℂ => A*z) (normalFactor_character_eq D L γ δ ν x r t τ i)
  rw [hh]
  dsimp [A]
  unfold coordinateInputFactor
  rw [Complex.ofReal_prod,Finset.prod_mul_distrib]
  ring

/-- The complete product of standard summands equals the actual cutoff,
input character and spatial character at every full lattice input. -/
theorem prod_sourceFactorTerm_at_input {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (x : D.S.VIdx → Fin d → ℤ)
    (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) :
    (∏ a : FactorIdx D.S, sourceFactorTerm D L γ δ p ν r t τ a
      (inputFactorEquiv D.S (Fin d → ℤ) x a)) =
      ((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ) : ℂ)*inputCharacter D L ν x *
        piCharacter (spatialPhaseExponent D L γ δ x r t τ) := by
  rw [← prod_coordinateInputFactor]
  rw [prod_source_input_slots D.S (coordinateInputFactor D L p ν) x]
  unfold spatialPhaseExponent
  rw [AddChar.map_add_eq_mul,AddChar.map_add_eq_mul,piCharacter_sum,piCharacter_sum,piCharacter_sum]
  simp only [Fintype.prod_sum_type,sourceFactorTerm]
  change (∏ i, linearFactorTerm D L γ δ p ν r t τ i (x (D.S.x0Slot i))) *
    ((∏ a, pairFactorTerm D L γ δ p ν r t τ a (x (D.S.xSlot a.1 a.2),x (D.S.ySlot a.1 a.2))) *
      ∏ i, normalFactorTerm D L γ δ p ν r t τ i (fun j => x (D.S.uSlot i.1 i.2 j))) = _
  simp_rw [linearFactorTerm_at_input,pairFactorTerm_at_input,normalFactorTerm_at_input]
  simp only [Finset.prod_mul_distrib]
  ac_rfl

end WaveTurbulence.SumintPar
