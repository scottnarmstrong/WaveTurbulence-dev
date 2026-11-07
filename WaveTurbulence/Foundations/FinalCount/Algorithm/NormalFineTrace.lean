/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalGeometryStep
public import WaveTurbulence.Foundations.FinalCount.Algorithm.FineGeometryStep
import Mathlib.Tactic

/-! # Actual normal/fine traces cannot terminate with negative initial nu

This is an internal run endpoint, not Prop 10.2: the source scheduler must
construct its full run and identify its good-free specialization. All
step increments used below are proved from the actual graph constructors.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

inductive NormalFineStep : State.{u,v} V → State.{u,v} V → Prop
  | normal {s t : State.{u,v} V} {n : ℕ} : NormalGeometryStep s t n → NormalFineStep s t
  | fine {s t : State.{u,v} V} : FineGeometryStep s t → NormalFineStep s t

theorem NormalFineStep.molecule {s t : State.{u,v} V} (h : NormalFineStep s t)
    (hM : s.graph.IsMolecule) : t.graph.IsMolecule := by
  cases h with
  | normal h => exact h.molecule hM
  | fine h => exact h.molecule hM

theorem NormalFineStep.defect_mono {s t : State.{u,v} V} (h : NormalFineStep s t)
    (hM : s.graph.IsMolecule) : defectPotential s.graph ≤ defectPotential t.graph := by
  cases h with
  | normal h => exact h.defect_mono
  | fine h => exact h.defect_mono hM

inductive NormalFineTrace : State.{u,v} V → State.{u,v} V → ℕ → Prop
  | nil (s : State.{u,v} V) : NormalFineTrace s s 0
  | cons {s t z : State.{u,v} V} {n : ℕ} :
      NormalFineStep s t → NormalFineTrace t z n → NormalFineTrace s z (n+1)

theorem NormalFineTrace.defect_mono {s t : State.{u,v} V} {n : ℕ}
    (h : NormalFineTrace s t n) (hM : s.graph.IsMolecule) : defectPotential s.graph ≤ defectPotential t.graph := by
  induction h with
  | nil s => exact le_refl _
  | cons hstep htrace ih => exact le_trans (hstep.defect_mono hM) (ih (hstep.molecule hM))

/-- The source odd-edge case needs a good operation: a terminating run
consisting of actual normal/fine steps would contradict this theorem. -/
theorem no_terminal_normalFineTrace_of_nu_neg {s t : State.{u,v} V} {n : ℕ}
    (hM : s.graph.IsMolecule) (hnu : appbNu s.graph < 0)
    (htrace : NormalFineTrace s t n) (hterm : Terminal t) : False := by
  have hp := defectPotential_pos_of_nu_neg s.graph hnu
  have ht := defectPotential_zero_terminal t.graph hterm
  have hm := htrace.defect_mono hM
  rw [ht] at hm
  omega

end WaveTurbulence.Mole.AppbAlgorithm
