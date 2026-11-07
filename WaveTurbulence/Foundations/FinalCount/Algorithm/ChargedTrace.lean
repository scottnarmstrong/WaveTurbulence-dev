/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.GeometricPotentialBound
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalActivePotential
import Mathlib.Tactic

/-! # Summing actual potential losses while leaving continuing ladders uncharged

No potential bound is a constructor field. The zero-charge constructor
contains exactly the old degree-four boundary and actual displayed-link
data of a normal ladder step. The source scheduler must supply its normal
and good/fine event-count estimates separately.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

inductive ChargedStep : State.{u,v} V → State.{u,v} V → ℕ → Prop
  | ladder (s : State.{u,v} V) (r : AppbRealization s.graph AppbPatternKind.d33.pattern)
      (hM : s.graph.IsMolecule) (h3 : s.graph.deg (r.vertex 3) = 4)
      (h4 : s.graph.deg (r.vertex 4) = 4) (hlink : appbD33LinkAtoms r ∈ appbLinks s.graph) :
      ChargedStep s (ofMolecule r.post) 0
  | other {s t : State.{u,v} V} (step : GeometricStep s t)
      (hM : s.graph.IsMolecule) (hN : t.graph.IsMolecule) : ChargedStep s t 1

theorem ChargedStep.potential_bound {s t : State.{u,v} V} {n : ℕ} (h : ChargedStep s t n) :
    activeLinkPotential s.graph-20*(n : ℤ) ≤ activeLinkPotential t.graph := by
  cases h with
  | ladder r hM h3 h4 hlink =>
    have hh := d33_normal_activePotential_change s.graph hM r h3 h4
    rw [if_pos hlink] at hh
    change activeLinkPotential s.graph-20*(0 : ℤ) ≤ activeLinkPotential r.post
    omega
  | other step hM hN =>
    simpa only [Nat.cast_one,mul_one] using step.activePotential_drop_le hM hN

theorem ChargedStep.geometric {s t : State.{u,v} V} {n : ℕ} (h : ChargedStep s t n) : GeometricStep s t := by
  cases h with
  | ladder r hM h3 h4 hlink => exact .delete s .d33 r
  | other step hM hN => exact step

inductive ChargedTrace : State.{u,v} V → State.{u,v} V → ℕ → Prop
  | nil (s : State.{u,v} V) : ChargedTrace s s 0
  | cons {s t z : State.{u,v} V} {n m : ℕ} :
      ChargedStep s t n → ChargedTrace t z m → ChargedTrace s z (n+m)

theorem ChargedTrace.potential_bound {s t : State.{u,v} V} {n : ℕ} (h : ChargedTrace s t n) :
    activeLinkPotential s.graph-20*(n : ℤ) ≤ activeLinkPotential t.graph := by
  induction h with
  | nil s => simp only [Nat.cast_zero,mul_zero,sub_zero,le_refl]
  | cons hstep htrace ih =>
    have hh := hstep.potential_bound
    push_cast
    omega

/-- Conditional run endpoint. A source proof must construct its actual
charged run and prove its charge count from the priority schedule. -/
theorem sourceRho_le_charged_trace {s t : State.{u,v} V} {n : ℕ}
    (hM : s.graph.IsMolecule)
    (hc : ∀ a ∈ s.graph.atoms,∀ b ∈ s.graph.atoms,s.graph.SameComponent a b)
    (hne : s.graph.bonds.Nonempty) (htrace : ChargedTrace s t n) (hterm : Terminal t) :
    (sourceRho s.graph : ℤ) ≤ 20*(n : ℤ) := by
  have hi := sourceRho_le_active_initial s.graph hM hc hne
  have ht := activeLinkPotential_terminal t.graph hterm
  have hh := htrace.potential_bound
  omega

end WaveTurbulence.Mole.AppbAlgorithm
