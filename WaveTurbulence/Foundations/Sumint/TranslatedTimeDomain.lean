/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.TimeExits
import Mathlib.Tactic

/-!
# Exact factorization of the translated source time domain

For fixed translated input times the output dependence is one finite
interval and two half-lines with a common exit. All input order
constraints become independent of the output triple.
-/

public section

open Set

namespace WaveTurbulence.Sumint

/-- Static constraints left after simultaneous translation of every input time. -/
@[expose] def staticTimeDomain {d : ℕ} (D : SumintDatum d) : Set (D.S.TVar → ℝ) :=
  {u | (∀ v, u v < 0) ∧ ∀ c ∈ D.constraints, u c.1 < u c.2}

/-- Literal equivalence with the exact draft time domain under the shear. -/
theorem translated_timeDom_iff {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (u : D.S.TVar → ℝ) (t t' t'' : ℝ) :
    (fun v => u v+t) ∈ D.timeDom hI t (t'+t) (t''+t) ↔
      u ∈ staticTimeDomain D ∧ t ∈ Icc (lowerTimeExit D hI u) (upperTimeExit D hI u) ∧
        t' < u (firstTime D hI) ∧ t'' < u (firstTime D hI) := by
  rw [Set.mem_Icc, lowerTimeExit_le_iff, le_upperTimeExit_iff]
  constructor
  · intro h
    have hu : ∀ v, u v < 0 := by
      intro v
      have hv := (h.1 v).2.2
      linarith only [hv]
    have hc : ∀ c ∈ D.constraints, u c.1 < u c.2 := by
      intro c hc
      have hh := h.2.2 c hc
      linarith only [hh]
    have hl : ∀ v, (D.q v : ℝ)-u v ≤ t := by
      intro v
      have hv := (h.1 v).1
      linarith only [hv]
    have hr : ∀ v, t ≤ (D.q v : ℝ)+1-u v := by
      intro v
      have hv := (h.1 v).2.1
      linarith only [hv]
    have hm := max_lt_iff.mp h.2.1
    refine ⟨⟨hu,hc⟩, ⟨hl,hr⟩, ?_, ?_⟩ <;>
      change _ < u (firstTime D hI) <;> dsimp [firstTime] <;> linarith only [hm.1, hm.2]
  · rintro ⟨hu, ⟨hl,hr⟩, ht', ht''⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v
      refine ⟨?_, ?_, ?_⟩
      · linarith only [hl v]
      · linarith only [hr v]
      · linarith only [hu.1 v]
    · apply max_lt_iff.mpr
      change t'+t < u (firstTime D hI)+t ∧ t''+t < u (firstTime D hI)+t
      constructor <;> linarith only [ht', ht'']
    · intro c hc
      linarith only [hu.2 c hc]

/-- The static translated domain is measurable, including every given order constraint. -/
theorem measurableSet_staticTimeDomain {d : ℕ} (D : SumintDatum d) :
    MeasurableSet (staticTimeDomain D) := by
  classical
  unfold staticTimeDomain
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro v
    exact measurableSet_lt (measurable_pi_apply v) measurable_const
  · apply MeasurableSet.iInter
    intro c
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)

end WaveTurbulence.Sumint
