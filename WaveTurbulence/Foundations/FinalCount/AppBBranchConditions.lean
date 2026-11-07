/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
public import WaveTurbulence.Foundations.FinalCount.AppBTwoComponents
public import WaveTurbulence.Foundations.FinalCount.AppBLargeGap
import Mathlib.Tactic

/-! # DH23 Appendix B branch conditions, including the decoration tests

Bond indices are zero-based positions in the transcribed figure lists.
All direction tests use the actual outgoing representative and its
specified endpoint, so the orientation of an internal bond is retained.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Appendix B standing exclusion of self-connecting bonds. -/
def AppbNoLoops (M : Molecule V D) : Prop := ∀ x, M.atom x ≠ M.atom (M.mate x)

/-- Standing exclusion of triple bonds after the TB stage. -/
def AppbNoTripleBonds (M : Molecule V D) : Prop :=
  ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, a ≠ b → M.bondsBetween a b ≤ 2

/-- Two actual bond directions, viewed from possibly different endpoints,
are opposite. Darts x,y here are the outgoing bond representatives. -/
def AppbOppositeFrom (M : Molecule V D) (a b : V) (x y : D) : Prop :=
  M.atom x = a ↔ M.atom y ≠ b

/-- Source 3S3 graph condition (i), plus (ii). The separate same-component
clauses attach 5 and 6 to the two actual residual pieces. -/
def AppbS33SplitGeometry (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern) : Prop :=
  TwoComponents r.post r.post.atoms (r.vertex 3) (r.vertex 4) ∧
  r.post.SameComponent (r.vertex 3) (r.vertex 5) ∧
  r.post.SameComponent (r.vertex 4) (r.vertex 6) ∧
  AppbOppositeFrom M (r.vertex 1) (r.vertex 2) (r.edge ⟨1,by decide⟩).val (r.edge ⟨3,by decide⟩).val ∧
  AppbOppositeFrom M (r.vertex 1) (r.vertex 2) (r.edge ⟨2,by decide⟩).val (r.edge ⟨4,by decide⟩).val

/-- The precise small-difference and large internal-gap conditions of
3S3-1N and 3S3-3G. The negation selects 3S3-2G. -/
def AppbS33LabelConditions (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern) {d : ℕ}
    (L γ γ0 : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) : Prop :=
  ‖Molecule.kvec L w κ (r.edge ⟨1,by decide⟩).val - Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖ +
    ‖Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val - Molecule.kvec L w κ (r.edge ⟨4,by decide⟩).val‖ ≤ L ^ (-γ) ∧
  (AppbOppositeFrom M (r.vertex 1) (r.vertex 1) (r.edge ⟨0,by decide⟩).val (r.edge ⟨2,by decide⟩).val →
    L ^ (-γ + 2 * γ0 / 3) ≤
      ‖Molecule.kvec L w κ (r.edge ⟨0,by decide⟩).val - Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val‖)

/-- Source 3D3 opposite boundary directions, viewed from the deleted pair. -/
def AppbD33BoundaryOpposite (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern) : Prop :=
  AppbOppositeFrom M (r.vertex 1) (r.vertex 2) (r.edge ⟨2,by decide⟩).val (r.edge ⟨3,by decide⟩).val

/-- The precise tests of 3D3-1N and 3D3-3G. The internal double-bond test
uses opposite directions, following the operation definition at L2225,
correcting “same direction” in the proof's last sentence at L2238. -/
def AppbD33LabelConditions (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern) {d : ℕ}
    (L γ γ0 : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) : Prop :=
  ‖Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val - Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖ ≤ L ^ (-γ) ∧
  (AppbOppositeFrom M (r.vertex 1) (r.vertex 1) (r.edge ⟨0,by decide⟩).val (r.edge ⟨1,by decide⟩).val →
    L ^ (-γ + 2 * γ0 / 3) ≤
      ‖Molecule.kvec L w κ (r.edge ⟨0,by decide⟩).val - Molecule.kvec L w κ (r.edge ⟨1,by decide⟩).val‖)

/-- Actual non-saturation premise of 3D3-3G, excluding the removed pair. -/
def AppbD33ResidualDefect (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern) : Prop :=
  ∃ v ∈ M.atoms, v ≠ r.vertex 1 ∧ v ≠ r.vertex 2 ∧ M.deg v ≠ 4

end WaveTurbulence.Mole
