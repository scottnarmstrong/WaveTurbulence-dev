/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBHalfGap
public import WaveTurbulence.Foundations.FinalCount.Algorithm.State
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideInvariants
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideMolecule
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionPostInvariants
import Mathlib.Tactic

/-! # Physical counting problems carried through the actual algorithm

A problem stores its actual graph, admissibility predicate and physical
scale assignment. It stores standing invariants, never an analytic count
conclusion. The no-triple invariant is imposed at source dispatch points;
a temporary reinsertion output can therefore use the same problem carrier
before its optional TB cleanup.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v

structure Problem (V : Type v) [DecidableEq V] (d : ℕ) (L : ℝ) (w : Mom d) (c g : ℝ) where
  state : State.{u,v} V
  admissible : (state.Dart → (Fin d → ℤ)) → Prop
  scales : Finset V → ℝ
  molecule : state.graph.IsMolecule
  noLoops : AppbNoLoops state.graph
  scales_nonneg : ∀ S,0 ≤ scales S
  validLinkScales : AppbValidLinkScales state.graph L w admissible c scales
  mateLabels : ∀ κ,admissible κ → ∀ x,κ (state.graph.mate x) = κ x
  largeGap : ∀ κ,admissible κ → AppbLargeGap state.graph L w κ g

variable {V : Type v} [DecidableEq V] {d : ℕ} {L c g : ℝ} {w : Mom d}

noncomputable def Problem.value (p : Problem.{u,v} V d L w c g) (γ δ C1 : ℝ) : ℝ≥0∞ :=
  appbLinkCountA p.state.graph L γ δ C1 w p.admissible p.scales

def Problem.lowerGap (p : Problem.{u,v} V d L w c g) (g' : ℝ) (h : g' ≤ g) :
    Problem.{u,v} V d L w c g' where
  state := p.state
  admissible := p.admissible
  scales := p.scales
  molecule := p.molecule
  noLoops := p.noLoops
  scales_nonneg := p.scales_nonneg
  validLinkScales := p.validLinkScales
  mateLabels := p.mateLabels
  largeGap := fun κ hκ => (p.largeGap κ hκ).mono h

noncomputable def Problem.side (p : Problem.{u,v} V d L w c g) (S : Finset V)
    (hS : AppbClosedSide p.state.graph S) : Problem.{u,v} V d L w c g where
  state := ofMolecule (appbSideMolecule p.state.graph S hS)
  admissible := appbSideAdmissibility p.state.graph S p.admissible
  scales := p.scales
  molecule := isMolecule_closed_side p.state.graph S hS p.molecule
  noLoops := noLoops_closed_side p.state.graph S hS p.noLoops
  scales_nonneg := p.scales_nonneg
  validLinkScales := validLinkScales_closed_side p.state.graph S hS p.validLinkScales
  mateLabels := projected_mate_labels_closed_side p.state.graph S hS p.mateLabels
  largeGap := projected_largeGap_closed_side p.state.graph S hS p.largeGap

noncomputable def Problem.deletion (p : Problem.{u,v} V d L w c g) {P : AppbPattern}
    (r : AppbRealization p.state.graph P) (q : Fin P.edges.length → (Fin d → ℤ)) :
    Problem.{u,v} V d L w c g where
  state := ofMolecule r.post
  admissible := r.conditionedPostAdmissibility p.admissible q
  scales := p.scales
  molecule := appb_eraseAtoms_isMolecule p.state.graph p.molecule r.removedAtoms
  noLoops := appb_eraseAtoms_noLoops p.state.graph r.removedAtoms p.noLoops
  scales_nonneg := p.scales_nonneg
  validLinkScales := r.conditionedPost_validLinkScales p.validLinkScales q
  mateLabels := conditionedPost_mate_labels r p.admissible q
  largeGap := conditionedPost_largeGap r q p.largeGap

end WaveTurbulence.Mole.AppbAlgorithm
