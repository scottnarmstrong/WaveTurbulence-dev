/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformD336Good
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GoodDeletionReduction
import Mathlib.Tactic

/-! # Complete source 3D3-6G reduction for every preferred new figure -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Filter
universe u v

/-- DH23 rule three(c-i), the actual nine-bond new figure, with carrier-uniform
threshold, the iterated half-gap premise and all actual post invariants. -/
theorem exists_d336_good_reduction (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ (1 : ℝ),∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.d33new.pattern),M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) → (∀ e : D,¬Degen.IsBridge M e) →
    (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ S,0 ≤ P S) → (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      Nonempty (GoodDeletionReduction M .d33new r L γ δ η C1 w A P) := by
  have hη' : 0 < 2*η/3 := by linarith only [hη]
  have hηγ' : 2*η/3 ≤ min γ (1-γ) := by linarith only [hη,hηγ]
  intro δ hδ
  obtain ⟨Lb,hbase⟩ := uniform_d336_good_bound d hd γ hγ δ (2*η/3) hδ hη' hηγ' m
  obtain ⟨Lh,hh⟩ := eventually_atTop.mp (appb_half_gap_comparison_eventual γ η hη)
  refine ⟨max Lb Lh,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hno hnt hconn hb hsize w A P hP hLG
  have hLG' : ∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+2*η/3)) :=
    fun κ hκ => (hLG κ hκ).mono (hh L ((le_max_right Lb Lh).trans hL))
  obtain ⟨q,hq⟩ := hbase V D C1 hC1 L ((le_max_left Lb Lh).trans hL)
    M r hM hconn hb hsize w A P hP hLG'
  exact ⟨{
    labels := q
    step := .delete (ofMolecule M) .d33new r
    invariants := deletionPostInvariants r L (L^(-γ+η)/2) w A P q hM hno hnt hLG
    deviation := hq }⟩

end WaveTurbulence.Mole.AppbAlgorithm
