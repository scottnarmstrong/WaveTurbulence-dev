/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33LabelBranches
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionPostInvariants
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalGeometryStep
import Mathlib.Tactic

/-! # Complete inherited post problems for the 3D3 normal/good label split -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
open scoped ENNReal
universe u v

structure D33LabelReduction {V : Type v} {D : Type u} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33.pattern)
    {d : ℕ} (L γ δ C1 g : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) where
  normalLabels : Fin AppbPatternKind.d33.pattern.edges.length → (Fin d → ℤ)
  goodLabels : Fin AppbPatternKind.d33.pattern.edges.length → (Fin d → ℤ)
  step : NormalGeometryStep (ofMolecule M) (ofMolecule r.post) 0
  normalInvariants : DeletionPostInvariants r L g w
    (fun κ => A κ ∧ AppbD33LabelConditions M r L γ (min γ (1-γ)) w κ) P normalLabels
  goodInvariants : DeletionPostInvariants r L g w
    (fun κ => A κ ∧ ¬AppbD33LabelConditions M r L γ (min γ (1-γ)) w κ) P goodLabels
  bound : appbLinkCountA M L γ δ C1 w A P ≤
    appbLinkCountA r.post L γ δ C1 w
      (r.conditionedPostAdmissibility (fun κ => A κ ∧ AppbD33LabelConditions M r L γ (min γ (1-γ)) w κ) normalLabels) P+
    ENNReal.ofReal (L^(-5*min γ (1-γ)/8))*appbLinkCountA r.post L γ δ C1 w
      (r.conditionedPostAdmissibility (fun κ => A κ ∧ ¬AppbD33LabelConditions M r L γ (min γ (1-γ)) w κ) goodLabels) P

/-- DH23 source 3D3-1N/2G: both label branches have actual conditioned
post data and preserve every physical invariant. The old degree-four
boundary is exactly the normal graph profile, not an output assumption. -/
theorem exists_d33_label_reduction (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C₀ : ℝ,1 ≤ C₀ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ C₀,∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.d33.pattern),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ e : D,¬Degen.IsBridge M e) → AppbD33BoundaryOpposite M r →
    (∀ a ∈ AppbPatternKind.d33.pattern.vertices,a ∉ AppbPatternKind.d33.pattern.removed → M.deg (r.vertex a) = 4) →
    ∀ (g : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    AppbValidLinkScales M L w A c P → (∀ S,0 ≤ P S) →
    (∀ κ,A κ → ∀ x,κ (M.mate x) = κ x) →
    (∀ κ,A κ → AppbLargeGap M L w κ g) →
      Nonempty (D33LabelReduction M r L γ δ C1 g w A P) := by
  obtain ⟨C₀,hC₀,hbase⟩ := d33_label_branches_bound d hd γ hγ c hc
  refine ⟨C₀,hC₀,?_⟩
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := hbase δ hδ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hno hnt hb ho hd g w A P hv hP hm hLG
  obtain ⟨qN,qG,hbound⟩ := hL₀ V D C1 hC1 L hL M r hM hb ho w A P hv hP hm
  exact ⟨{
    normalLabels := qN
    goodLabels := qG
    step := .d33 (ofMolecule M) r hb hd
    normalInvariants := deletionPostInvariants r L g w _ P qN hM hno hnt (fun κ hκ => hLG κ hκ.1)
    goodInvariants := deletionPostInvariants r L g w _ P qG hM hno hnt (fun κ hκ => hLG κ hκ.1)
    bound := hbound }⟩

end WaveTurbulence.Mole.AppbAlgorithm
