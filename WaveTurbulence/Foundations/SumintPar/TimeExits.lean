/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.TimeDomain
import Mathlib.Tactic

/-!
# The exact endpoint functions after translating all input times

The output t interval is the intersection of the translated unit
intervals. Its endpoints are actual finite extrema, each attained at
an input time. The other two output coordinates have the same exit.
-/

@[expose] public section
set_option autoImplicit false

open Finset Set

namespace WaveTurbulence.SumintPar

/-- The distinguished first input time in the exact time-domain definition. -/
@[expose] def firstTime {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I) : D.S.TVar :=
  .inl ⟨⟨0,hI⟩,0⟩

/-- A nonempty block system supplies a nonempty input-time index set. -/
theorem time_univ_nonempty {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I) :
    (univ : Finset D.S.TVar).Nonempty := ⟨firstTime D hI, mem_univ _⟩

/-- Lower endpoint of the intersection of all translated unit time intervals. -/
@[expose] noncomputable def lowerTimeExit {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (u : D.S.TVar → ℝ) : ℝ :=
  univ.sup' (time_univ_nonempty D hI) (fun v => (D.q v : ℝ)-u v)

/-- Upper endpoint of the same intersection. -/
@[expose] noncomputable def upperTimeExit {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (u : D.S.TVar → ℝ) : ℝ :=
  univ.inf' (time_univ_nonempty D hI) (fun v => (D.q v : ℝ)+1-u v)

/-- A lower-exit bound is exactly the collection of individual lower bounds. -/
theorem lowerTimeExit_le_iff {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (u : D.S.TVar → ℝ) (t : ℝ) :
    lowerTimeExit D hI u ≤ t ↔ ∀ v, (D.q v : ℝ)-u v ≤ t := by
  rw [lowerTimeExit, Finset.sup'_le_iff]
  simp only [Finset.mem_univ, forall_const]

/-- An upper-exit bound is exactly the collection of individual upper bounds. -/
theorem le_upperTimeExit_iff {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (u : D.S.TVar → ℝ) (t : ℝ) :
    t ≤ upperTimeExit D hI u ↔ ∀ v, t ≤ (D.q v : ℝ)+1-u v := by
  rw [upperTimeExit, Finset.le_inf'_iff]
  simp only [Finset.mem_univ, forall_const]

/-- Every lower endpoint is attained at an actual input-time coordinate. -/
theorem lowerTimeExit_attained {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (u : D.S.TVar → ℝ) : ∃ v, lowerTimeExit D hI u = (D.q v : ℝ)-u v := by
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup' (time_univ_nonempty D hI) (fun v => (D.q v : ℝ)-u v)
  exact ⟨v,hv⟩

/-- Every upper endpoint is also attained at an actual input-time coordinate. -/
theorem upperTimeExit_attained {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (u : D.S.TVar → ℝ) : ∃ v, upperTimeExit D hI u = (D.q v : ℝ)+1-u v := by
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_inf' (time_univ_nonempty D hI) (fun v => (D.q v : ℝ)+1-u v)
  exact ⟨v,hv⟩

/-- Negative translated inputs and natural interval indices force a nonnegative lower endpoint. -/
theorem lowerTimeExit_nonneg {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (u : D.S.TVar → ℝ) (hu : ∀ v, u v ≤ 0) : 0 ≤ lowerTimeExit D hI u := by
  let v := firstTime D hI
  have hv : (D.q v : ℝ)-u v ≤ lowerTimeExit D hI u :=
    Finset.le_sup' (fun v => (D.q v : ℝ)-u v) (mem_univ v)
  have hq : (0 : ℝ) ≤ D.q v := Nat.cast_nonneg _
  linarith [hu v]

end WaveTurbulence.SumintPar
