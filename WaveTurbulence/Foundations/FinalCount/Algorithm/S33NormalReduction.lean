/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformS33Normal
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionPostInvariants
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalGeometryStep
public import WaveTurbulence.Foundations.FinalCount.AppBTwoComponentsSeparation
import Mathlib.Tactic

/-! # Complete source 3S3-1N reduction under its actual split and label tests -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v

structure S33NormalReduction {V : Type v} {D : Type u} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (r : AppbRealization M AppbPatternKind.s33.pattern)
    {d : ℕ} (L γ δ C1 g : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) where
  labels : Fin AppbPatternKind.s33.pattern.edges.length → (Fin d → ℤ)
  step : NormalGeometryStep (ofMolecule M) (ofMolecule r.post) 1
  sourceLabels : ∀ κ,A κ → AppbS33LabelConditions M r L γ (min γ (1-γ)) w κ
  invariants : DeletionPostInvariants r L g w A P labels
  deviation : IsDeviation (appbLinkCountA M L γ δ C1 w A P)
    (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility A labels) P) 1

/-- DH23 3S3-1N: both source split/direction tests, every old boundary
degree four, and the passing decoration tests give a concrete normal step
with all inherited invariants and carrier-uniform constants. -/
theorem exists_s33_normal_reduction (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C₀ L₀ : ℝ,1 ≤ C₀ ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ C₀,∀ L ≥ L₀,∀ δ ∈ Ioc (0 : ℝ) 1,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.s33.pattern),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) →
    (∀ e : D,¬Degen.IsBridge M e) → AppbS33SplitGeometry M r →
    (∀ a ∈ AppbPatternKind.s33.pattern.vertices,a ∉ AppbPatternKind.s33.pattern.removed → M.deg (r.vertex a) = 4) →
    ∀ (g : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ κ,A κ → AppbS33LabelConditions M r L γ (min γ (1-γ)) w κ) →
    (∀ κ,A κ → AppbLargeGap M L w κ g) → Nonempty (S33NormalReduction M r L γ δ C1 g w A P) := by
  obtain ⟨C₀,L₀,hC₀,hbase⟩ := uniform_s33_split_normal_bound d hd γ hγ
  refine ⟨C₀,L₀,hC₀,?_⟩
  intro V D instV instF instD C1 hC1 L hL δ hδ M r hM hno hnt hconn hb hg hd g w A P hlabels hLG
  obtain ⟨q,hq⟩ := hbase V D C1 hC1 L hL δ hδ M r hM hconn hg w A P
  exact ⟨{
    labels := q
    step := .s33 (ofMolecule M) r hb (appb_twoComponents_not_sameComponent r.post hg.1) hd
    sourceLabels := hlabels
    invariants := deletionPostInvariants r L g w A P q hM hno hnt hLG
    deviation := hq }⟩

end WaveTurbulence.Mole.AppbAlgorithm
