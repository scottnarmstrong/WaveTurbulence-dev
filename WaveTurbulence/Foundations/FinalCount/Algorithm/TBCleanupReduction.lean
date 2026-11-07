/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTBNormal
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionPostInvariants
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GeometricStep
import Mathlib.Tactic

/-! # Complete analytic post problems for a selected optional TB cleanup

The separately named conditional assembly helper consumes an actual
selected TB realization with its proved no-triple post property. Source
reinsertion selectors construct that data; this helper does not replace
those source results.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v

structure TBCleanupReduction {V : Type v} {D : Type u}
    [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) {d : ℕ} (L γ δ C1 g : ℝ) (w : Mom d)
    (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) where
  kind : AppbPatternKind
  kind_mem : kind ∈ ([AppbPatternKind.tb1,.tb2] : List _)
  figure : AppbRealization M kind.pattern
  labels : Fin kind.pattern.edges.length → (Fin d → ℤ)
  step : GeometricStep (ofMolecule M) (ofMolecule figure.post)
  invariants : DeletionPostInvariants figure L g w A P labels
  deviation : IsDeviation (appbLinkCountA M L γ δ C1 w A P)
    (appbLinkCountA figure.post L γ δ C1 w (figure.conditionedPostAdmissibility A labels) P) 1

/-- Conditional assembly helper, distinct from the source cleanup
selection: it constructs the analytic data on the already selected graph.
The actual no-triple post proof is retained as output, never assumed as
an analytic counting estimate. -/
theorem exists_tb_cleanup_reduction_of_selected_figure (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C₀ L₀ : ℝ,1 ≤ C₀ ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ C₀,∀ L ≥ L₀,∀ δ ∈ Ioc (0 : ℝ) 1,∀ (M : Molecule V D),
    M.IsMolecule → AppbNoLoops M →
    ∀ (k : AppbPatternKind),k ∈ ([AppbPatternKind.tb1,.tb2] : List _) →
    ∀ r : AppbRealization M k.pattern,AppbNoTripleBonds r.post →
    ∀ (g : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ κ,A κ → AppbLargeGap M L w κ g) →
      Nonempty (TBCleanupReduction M L γ δ C1 g w A P) := by
  obtain ⟨C₀,L₀,hC₀,hbase⟩ := uniform_tb_normal_bound d hd γ hγ
  refine ⟨C₀,L₀,hC₀,?_⟩
  intro V D instV instF instD C1 hC1 L hL δ hδ M hM hno k hk r hnt g w A P hLG
  obtain ⟨q,hq⟩ := hbase V D C1 hC1 L hL δ hδ M k hk r hM w A P
  exact ⟨{
    kind := k
    kind_mem := hk
    figure := r
    labels := q
    step := .delete (ofMolecule M) k r
    invariants := {
      molecule := appb_eraseAtoms_isMolecule M hM r.removedAtoms
      noLoops := appb_eraseAtoms_noLoops M r.removedAtoms hno
      noTripleBonds := hnt
      largeGap := conditionedPost_largeGap r q hLG
      mateLabels := conditionedPost_mate_labels r A q
      validLinkScales := fun c hv => r.conditionedPost_validLinkScales hv q }
    deviation := hq }⟩

end WaveTurbulence.Mole.AppbAlgorithm
