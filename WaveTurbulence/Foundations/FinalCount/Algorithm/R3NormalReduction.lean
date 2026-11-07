/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformR3GlobalNormal
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionPostInvariants
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalGeometryStep
import Mathlib.Tactic

/-! # The complete normal branch of source rule six -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v

structure R3NormalReduction {V : Type v} {D : Type u} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r3.pattern)
    {d : ℕ} (L γ δ C1 g : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) where
  labels : Fin AppbPatternKind.r3.pattern.edges.length → (Fin d → ℤ)
  step : NormalGeometryStep (ofMolecule M) (ofMolecule r.post) 1
  invariants : DeletionPostInvariants r L g w A P labels
  deviation : IsDeviation (appbLinkCountA M L γ δ C1 w A P)
    (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility A labels) P) 1

/-- DH23 3R-1N, with the actual component-local no-special test and
carrier-uniform constants. Unrelated components may contain special bonds. -/
theorem exists_r3_normal_reduction (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C₀ L₀ : ℝ,1 ≤ C₀ ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ C₀,∀ L ≥ L₀,∀ δ ∈ Ioc (0 : ℝ) 1,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.r3.pattern),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ e : D,¬Degen.IsBridge M e) →
    (∀ a ∈ AppbPatternKind.r3.pattern.vertices,a ∉ AppbPatternKind.r3.pattern.removed → M.deg (r.vertex a) = 4) →
    (∀ x : Degen.RetainedDart M r.removedAtoms,
      M.SameComponent (r.vertex 1) (M.atom x.val) → ¬AppbSpecial r.post x) →
    ∀ (g : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ κ,A κ → AppbLargeGap M L w κ g) → Nonempty (R3NormalReduction M r L γ δ C1 g w A P) := by
  obtain ⟨C₀,L₀,hC₀,hbase⟩ := uniform_r3_global_normal_bound d hd γ hγ
  refine ⟨C₀,L₀,hC₀,?_⟩
  intro V D instV instF instD C1 hC1 L hL δ hδ M r hM hno hnt hb hd hn g w A P hLG
  obtain ⟨q,hq⟩ := hbase V D C1 hC1 L hL δ hδ M r hM hb w A P
  exact ⟨{
    labels := q
    step := .r3 (ofMolecule M) r hb hd hn
    invariants := deletionPostInvariants r L g w A P q hM hno hnt hLG
    deviation := hq }⟩

end WaveTurbulence.Mole.AppbAlgorithm
