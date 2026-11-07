/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformD33GlobalNormalValid
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionPostInvariants
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalGeometryStep
public import WaveTurbulence.Foundations.FinalCount.AppBTwoComponentsSeparation
import Mathlib.Tactic

/-! # Complete source 3D3-1N reduction from actual physical link scales -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v

structure D33NormalReduction {V : Type v} {D : Type u} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33.pattern)
    {d : ℕ} (L γ δ C1 g : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) where
  labels : Fin AppbPatternKind.d33.pattern.edges.length → (Fin d → ℤ)
  step : NormalGeometryStep (ofMolecule M) (ofMolecule r.post) 0
  invariants : DeletionPostInvariants r L g w A P labels
  deviation : IsDeviation (appbLinkCountA M L γ δ C1 w A P)
    (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility A labels) P) 1

/-- DH23 3D3-1N, including the unconditional-label terminal-rung use in
rule three(c-iii). The physical scale comparison supplies the normal bound. -/
theorem exists_d33_normal_reduction (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C₀ : ℝ,1 ≤ C₀ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ C₀,∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.d33.pattern),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ e : D,¬Degen.IsBridge M e) → AppbD33BoundaryOpposite M r →
    (∀ a ∈ AppbPatternKind.d33.pattern.vertices,a ∉ AppbPatternKind.d33.pattern.removed → M.deg (r.vertex a) = 4) →
    ∀ (g : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    AppbValidLinkScales M L w A c P →
    (∀ κ,A κ → ∀ x,κ (M.mate x) = κ x) →
    (∀ κ,A κ → AppbLargeGap M L w κ g) → Nonempty (D33NormalReduction M r L γ δ C1 g w A P) := by
  obtain ⟨C₀,hC₀,hbase⟩ := uniform_d33_global_normal_of_valid_scales_bound d hd γ hγ c hc
  refine ⟨C₀,hC₀,?_⟩
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := hbase δ hδ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hno hnt hb ho hd g w A P hv hm hLG
  obtain ⟨q,hq⟩ := hL₀ V D C1 hC1 L hL M r hM hb ho w A P hv hm
  exact ⟨{
    labels := q
    step := .d33 (ofMolecule M) r hb hd
    invariants := deletionPostInvariants r L g w A P q hM hno hnt hLG
    deviation := hq }⟩

end WaveTurbulence.Mole.AppbAlgorithm
