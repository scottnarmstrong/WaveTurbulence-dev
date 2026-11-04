/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SpatialPhaseExponent
public import WaveTurbulence.Foundations.Sumint.InputFactors
public import WaveTurbulence.Foundations.Sumint.CubicCutoffRescale

/-!
# The literal independent source lattice factors

The half time scale converts the source pi phase to the landed 2pi
character. The shifted frequencies are unrestricted, exactly as required
by the landed linear, bilinear and cubic estimates.
-/

public section

namespace WaveTurbulence.Sumint

/-- The source time scale in the landed Fourier convention. -/
@[expose] noncomputable def sourceHalfScale (L γ δ : ℝ) : ℝ := δ*L^(2*γ)/2

/-- Frequency of the distinguished linear input. -/
@[expose] noncomputable def linearFactorFrequency {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) (i : Fin D.S.I) : Mom d :=
  ν (D.S.x0Slot i)+(sourceHalfScale L γ δ*(τ (.inl ⟨i,0⟩)-t)) • r

/-- Bilinear frequency of one source pair. -/
@[expose] noncomputable def pairFactorTime {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (τ : D.S.TVar → ℝ) (p : Σ i : Fin D.S.I, Fin (D.S.m i)) : ℝ :=
  sourceHalfScale L γ δ*(τ (.inl ⟨p.1,p.2.succ⟩)-τ (.inr (.inl p)))

/-- First unrestricted frequency in a pair factor. -/
@[expose] noncomputable def pairFactorFrequencyX {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ)
    (p : Σ i : Fin D.S.I, Fin (D.S.m i)) : Mom d :=
  ν (D.S.xSlot p.1 p.2)+(sourceHalfScale L γ δ*(τ (.inl ⟨p.1,p.2.succ⟩)-t)*
    (D.ζc p.1 p.2 0 : ℝ)) • r

/-- Second unrestricted frequency in a pair factor. -/
@[expose] noncomputable def pairFactorFrequencyY {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ)
    (p : Σ i : Fin D.S.I, Fin (D.S.m i)) : Mom d :=
  ν (D.S.ySlot p.1 p.2)+(sourceHalfScale L γ δ*(τ (.inl ⟨p.1,p.2.succ⟩)-t)*
    (D.ζc p.1 p.2 1 : ℝ)) • r

/-- The two quadratic time frequencies of a normal source factor. -/
@[expose] noncomputable def normalFactorTime {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (τ : D.S.TVar → ℝ) (i : {i : Fin D.S.I // D.S.nor i = true}) (j : Fin 2) : ℝ :=
  sourceHalfScale L γ δ*(τ (.inr (.inr ⟨i,Fin.castLE (by omega) j⟩))-τ (.inr (.inr ⟨i,2⟩)))

/-- Unrestricted linear modulation of each normal input. -/
@[expose] noncomputable def normalFactorFrequency {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ)
    (i : {i : Fin D.S.I // D.S.nor i = true}) (j : Fin 3) : Mom d :=
  ν (D.S.uSlot i.1 i.2 j)+(sourceHalfScale L γ δ*(τ (.inr (.inr ⟨i,2⟩))-t)*
    (D.ξc i.1 (Fin.castLE (by omega) j) : ℝ)) • r

/-- The actual linear lattice summand at the inserted cutoff width. -/
@[expose] noncomputable def linearFactorTerm {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) (i : Fin D.S.I) (n : Fin d → ℤ) : ℂ :=
  (inputCutoff (p (D.S.x0Slot i)) (latticePoint L n) : ℂ) *
    (Real.fourierChar (inner ℝ (linearFactorFrequency D L γ δ ν r t τ i) (latticePoint L n)) : ℂ)

/-- The actual bilinear lattice summand at the inserted cutoff width. -/
@[expose] noncomputable def pairFactorTerm {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i))
    (n : (Fin d → ℤ) × (Fin d → ℤ)) : ℂ :=
  let X := latticePoint L n.1
  let Y := latticePoint L n.2
  ((inputCutoff (p (D.S.xSlot a.1 a.2)) X*inputCutoff (p (D.S.ySlot a.1 a.2)) Y : ℝ) : ℂ) *
    (Real.fourierChar (inner ℝ X (pairFactorFrequencyX D L γ δ ν r t τ a) +
      inner ℝ Y (pairFactorFrequencyY D L γ δ ν r t τ a) + pairFactorTime D L γ δ τ a*inner ℝ X Y) : ℂ)

/-- The actual normal cubic summand for either of the two quadratic forms. -/
@[expose] noncomputable def normalFactorTerm {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) (i : {i : Fin D.S.I // D.S.nor i = true})
    (n : Fin 3 → Fin d → ℤ) : ℂ :=
  let X := fun j => latticePoint L (n j)
  ((∏ j : Fin 3, inputCutoff (p (D.S.uSlot i.1 i.2 j)) (X j) : ℝ) : ℂ) *
    (Real.fourierChar (normalFactorTime D L γ δ τ i 0*inner ℝ (X 0) (X 1) +
      normalFactorTime D L γ δ τ i 1*WeylSums.cubicQuadraticForm (D.Λsel i.1) (X 0) (X 1) (X 2) +
      ∑ j : Fin 3, inner ℝ (normalFactorFrequency D L γ δ ν r t τ i j) (X j)) : ℂ)

/-- The heterogeneous family of actual source summands. -/
@[expose] noncomputable def sourceFactorTerm {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) : (a : FactorIdx D.S) → FactorInput D.S (Fin d → ℤ) a → ℂ
  | .inl i => linearFactorTerm D L γ δ p ν r t τ i
  | .inr (.inl a) => pairFactorTerm D L γ δ p ν r t τ a
  | .inr (.inr i) => normalFactorTerm D L γ δ p ν r t τ i

end WaveTurbulence.Sumint
