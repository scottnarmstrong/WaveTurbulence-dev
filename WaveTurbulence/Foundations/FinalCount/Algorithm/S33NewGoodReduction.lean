/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformS33NewGood
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GoodDeletionReduction
import Mathlib.Tactic

/-! # Complete source 3S3-5G reduction for every preferred new figure -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Filter
universe u v

/-- DH23 rule two(a), all six preferred figures, with carrier-uniform
threshold, the iterated half-gap premise and all actual post invariants. -/
theorem exists_s33_new_good_reduction (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ (1 : ℝ),∀ L ≥ L₀,∀ (M : Molecule V D) (k : AppbPatternKind),
    k ∈ ([AppbPatternKind.s33new1,.s33new2,.s33new3,.s33new4,.s33new5,.s33new6] : List _) →
    ∀ r : AppbRealization M k.pattern,M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) → (∀ e : D,¬Degen.IsBridge M e) →
    (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ S,0 ≤ P S) → (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      Nonempty (GoodDeletionReduction M k r L γ δ η C1 w A P) := by
  have hη' : 0 < 2*η/3 := by linarith only [hη]
  have hηγ' : 2*η/3 ≤ min γ (1-γ) := by linarith only [hη,hηγ]
  intro δ hδ
  obtain ⟨Lb,hbase⟩ := uniform_s33_new_good_bound d hd γ hγ (2*η/3) hη' hηγ' m δ hδ
  obtain ⟨Lh,hh⟩ := eventually_atTop.mp (appb_half_gap_comparison_eventual γ η hη)
  refine ⟨max Lb Lh,?_⟩
  intro V D instV instF instD C1 hC1 L hL M k hk r hM hno hnt hconn hb hsize w A P hP hLG
  have hLG' : ∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+2*η/3)) :=
    fun κ hκ => (hLG κ hκ).mono (hh L ((le_max_right Lb Lh).trans hL))
  obtain ⟨q,hq⟩ := hbase V D C1 hC1 L ((le_max_left Lb Lh).trans hL)
    M k hk r hM hconn hb hsize w A P hP hLG'
  exact ⟨{
    labels := q
    step := .delete (ofMolecule M) k r
    invariants := deletionPostInvariants r L (L^(-γ+η)/2) w A P q hM hno hnt hLG
    deviation := hq }⟩

end WaveTurbulence.Mole.AppbAlgorithm
