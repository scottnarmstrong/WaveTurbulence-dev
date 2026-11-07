/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.GoodDeletionReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformD33GlobalBadLabels
import Mathlib.Tactic

/-! # Concrete good deletion reductions for the primary 3D3 failed-label branch -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Filter
universe u v
/-- DH23 3D3-2G with the actual failed source label condition. -/
theorem exists_d33_bad_labels_good_reduction (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ (1 : ℝ),∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.d33.pattern),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ e : D,¬Degen.IsBridge M e) → AppbD33BoundaryOpposite M r →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ S,0 ≤ P S) → (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
    (∀ κ,A κ → ¬AppbD33LabelConditions M r L γ (min γ (1-γ)) w κ) →
      Nonempty (GoodDeletionReduction M .d33 r L γ δ η C1 w A P) := by
  intro δ hδ
  obtain ⟨L₀,hbase⟩ := uniform_d33_global_bad_labels_good_bound d hd γ hγ δ hδ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hno hnt hb ho w A P hP hLG hbad
  obtain ⟨q,hq⟩ := hbase V D C1 hC1 L hL M r hM hb ho w A P hP hbad
  exact ⟨{
    labels := q
    step := .delete (ofMolecule M) .d33 r
    invariants := deletionPostInvariants r L (L^(-γ+η)/2) w A P q hM hno hnt hLG
    deviation := hq }⟩


end WaveTurbulence.Mole.AppbAlgorithm
