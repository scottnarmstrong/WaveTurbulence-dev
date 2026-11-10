/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceFactorTerms
public import WaveTurbulence.Foundations.Sumint.CubicPiCutoffRescale
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import WaveTurbulence.Foundations.LemLin.LinearWindow

/-!
# Exact identification of every source factor with its landed lattice sum

The inserted width-four cutoffs give mesh parameter 4L, spatial centres
one quarter as large, linear modulations four times as large and
quadratic time frequencies sixteen times as large. Both normal forms
are covered by the same literal identity.
-/

public section

open WithLp

namespace WaveTurbulence.Sumint

/-- The source linear factor is exactly the landed linear sum after width rescaling. -/
theorem tsum_linearFactorTerm_eq {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) (i : Fin D.S.I) :
    (∑' n : Fin d → ℤ, linearFactorTerm D L γ δ p ν r t τ i n) =
      LemLin.linearLatticeSum (4*L) ((1/4:ℝ) • toLp 2 (p (D.S.x0Slot i)))
        ((4:ℝ) • linearFactorFrequency D L γ δ ν r t τ i) :=
  inputCutoff_linear_sum_eq L (p (D.S.x0Slot i)) (linearFactorFrequency D L γ δ ν r t τ i)

/-- The source pair factor is exactly the landed bilinear sum after width rescaling. -/
theorem tsum_pairFactorTerm_eq {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)) :
    (∑' n : (Fin d → ℤ) × (Fin d → ℤ), pairFactorTerm D L γ δ p ν r t τ a n) =
      WeylSums.bilinearLatticeSum (4*L) (16*pairFactorTime D L γ δ τ a)
        ((1/4:ℝ) • toLp 2 (p (D.S.xSlot a.1 a.2))) ((1/4:ℝ) • toLp 2 (p (D.S.ySlot a.1 a.2)))
        ((4:ℝ) • pairFactorFrequencyX D L γ δ ν r t τ a)
        ((4:ℝ) • pairFactorFrequencyY D L γ δ ν r t τ a) :=
  inputCutoff_bilinear_sum_eq L (pairFactorTime D L γ δ τ a)
    (p (D.S.xSlot a.1 a.2)) (p (D.S.ySlot a.1 a.2))
    (pairFactorFrequencyX D L γ δ ν r t τ a) (pairFactorFrequencyY D L γ δ ν r t τ a)

/-- The normal source factor is exactly the landed cubic sum in either form. -/
theorem tsum_normalFactorTerm_eq {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) (i : {i : Fin D.S.I // D.S.nor i = true}) :
    (∑' n : Fin 3 → Fin d → ℤ, normalFactorTerm D L γ δ p ν r t τ i n) =
      WeylSums.cubicLatticeSum (4*L) (16*normalFactorTime D L γ δ τ i 0)
        (16*normalFactorTime D L γ δ τ i 1) (D.Λsel i.1)
        ((1/4:ℝ) • toLp 2 (p (D.S.uSlot i.1 i.2 0)))
        ((1/4:ℝ) • toLp 2 (p (D.S.uSlot i.1 i.2 1)))
        ((1/4:ℝ) • toLp 2 (p (D.S.uSlot i.1 i.2 2)))
        ((4:ℝ) • normalFactorFrequency D L γ δ ν r t τ i 0)
        ((4:ℝ) • normalFactorFrequency D L γ δ ν r t τ i 1)
        ((4:ℝ) • normalFactorFrequency D L γ δ ν r t τ i 2) :=
  inputCutoff_cubic_pi_sum_eq L (normalFactorTime D L γ δ τ i 0)
    (normalFactorTime D L γ δ τ i 1) (D.Λsel i.1)
    (fun j => p (D.S.uSlot i.1 i.2 j)) (normalFactorFrequency D L γ δ ν r t τ i)

end WaveTurbulence.Sumint
