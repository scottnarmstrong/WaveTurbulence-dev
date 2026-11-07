/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceFactorSums

/-!
# Local time functions of the literal source factors

Only the one, two or three time coordinates belonging to a factor enter
its lattice sum. Writing these functions explicitly permits the exact
time-coordinate Fubini theorem to apply to the landed oscillatory bounds.
-/

@[expose] public section
set_option autoImplicit false

open WithLp

namespace WaveTurbulence.SumintPar

/-- Linear source factor as a function of its one input time. -/
@[expose] noncomputable def linearTimeSum {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (i : Fin D.S.I) (s : ℝ) : ℂ :=
  LemLin.linearLatticeSum (4*L) ((1/4:ℝ) • toLp 2 (p (D.S.x0Slot i)))
    ((4:ℝ) • (ν (D.S.x0Slot i)+(sourceHalfScale L γ δ*(s-t)) • r))

/-- Pair source factor as a function of its outer and inner time. -/
@[expose] noncomputable def pairTimeSum {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (z : ℝ × ℝ) : ℂ :=
  WeylSums.bilinearLatticeSum (4*L) (16*(sourceHalfScale L γ δ*(z.1-z.2)))
    ((1/4:ℝ) • toLp 2 (p (D.S.xSlot a.1 a.2)))
    ((1/4:ℝ) • toLp 2 (p (D.S.ySlot a.1 a.2)))
    ((4:ℝ) • (ν (D.S.xSlot a.1 a.2)+
      (sourceHalfScale L γ δ*(z.1-t)*(D.ζc a.1 a.2 0:ℝ)) • r))
    ((4:ℝ) • (ν (D.S.ySlot a.1 a.2)+
      (sourceHalfScale L γ δ*(z.1-t)*(D.ζc a.1 a.2 1:ℝ)) • r))

/-- Normal source factor as a function of its three input times. -/
@[expose] noncomputable def normalTimeSum {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (i : {i : Fin D.S.I // D.S.nor i = true}) (z : Fin 3 → ℝ) : ℂ :=
  WeylSums.cubicLatticeSum (4*L) (16*(coreTimeSign D i.1 0*(sourceHalfScale L γ δ*(z 0-z 2))))
    (16*(coreTimeSign D i.1 1*(sourceHalfScale L γ δ*(z 1-z 2)))) (D.Λsel i.1)
    ((1/4:ℝ) • toLp 2 (p (D.S.uSlot i.1 i.2 0)))
    ((1/4:ℝ) • toLp 2 (p (D.S.uSlot i.1 i.2 1)))
    ((1/4:ℝ) • toLp 2 (p (D.S.uSlot i.1 i.2 2)))
    ((4:ℝ) • (ν (D.S.uSlot i.1 i.2 0)+
      (sourceHalfScale L γ δ*(z 2-t)*(D.ξc i.1 0:ℝ)) • r))
    ((4:ℝ) • (ν (D.S.uSlot i.1 i.2 1)+
      (sourceHalfScale L γ δ*(z 2-t)*(D.ξc i.1 1:ℝ)) • r))
    ((4:ℝ) • (ν (D.S.uSlot i.1 i.2 2)+
      (sourceHalfScale L γ δ*(z 2-t)*(D.ξc i.1 2:ℝ)) • r))

/-- The linear factor depends only on its distinguished source time. -/
theorem tsum_linearFactorTerm_eq_timeSum {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) (i : Fin D.S.I) :
    (∑' n : Fin d → ℤ, linearFactorTerm D L γ δ p ν r t τ i n) =
      linearTimeSum D L γ δ p ν r t i (τ (.inl ⟨i,0⟩)) :=
  tsum_linearFactorTerm_eq D L γ δ p ν r t τ i

/-- The pair factor depends only on its outer and inner source times. -/
theorem tsum_pairFactorTerm_eq_timeSum {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)) :
    (∑' n : (Fin d → ℤ) × (Fin d → ℤ), pairFactorTerm D L γ δ p ν r t τ a n) =
      pairTimeSum D L γ δ p ν r t a
        (τ (.inl ⟨a.1,a.2.succ⟩),τ (.inr (.inl a))) :=
  tsum_pairFactorTerm_eq D L γ δ p ν r t τ a

/-- The normal factor depends only on its three normal source times. -/
theorem tsum_normalFactorTerm_eq_timeSum {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) (i : {i : Fin D.S.I // D.S.nor i = true}) :
    (∑' n : Fin 3 → Fin d → ℤ, normalFactorTerm D L γ δ p ν r t τ i n) =
      normalTimeSum D L γ δ p ν r t i (fun j => τ (.inr (.inr ⟨i,j⟩))) :=
  tsum_normalFactorTerm_eq D L γ δ p ν r t τ i

end WaveTurbulence.SumintPar
