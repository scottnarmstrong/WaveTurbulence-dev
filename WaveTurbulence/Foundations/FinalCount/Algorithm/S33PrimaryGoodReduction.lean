/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.GoodDeletionReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformS33ConnectedGood
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformS33BadLabelsGood
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformS33MismatchGood
import Mathlib.Tactic

/-! # Concrete good deletion reductions for the primary 3S3 figure -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Filter
universe u v
/-- DH23 3S3-4G with connected actual residual graph. -/
theorem exists_s33_connected_good_reduction (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ (1 : ℝ),∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.s33.pattern),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) →
    (∀ a ∈ r.post.atoms,∀ b ∈ r.post.atoms,r.post.SameComponent a b) →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ S,0 ≤ P S) → (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      Nonempty (GoodDeletionReduction M .s33 r L γ δ η C1 w A P) := by
  intro δ hδ
  obtain ⟨L₀,hbase⟩ := uniform_s33_connected_post_good_bound d hd γ hγ δ hδ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hno hnt hconn hpost w A P hP hLG
  obtain ⟨q,hq⟩ := hbase V D C1 hC1 L hL M .s33 (by decide) r hM hconn hpost w A P hP
  exact ⟨{
    labels := q
    step := .delete (ofMolecule M) .s33 r
    invariants := deletionPostInvariants r L (L^(-γ+η)/2) w A P q hM hno hnt hLG
    deviation := hq }⟩

/-- DH23 3S3-2G with the actual failed source label condition. -/
theorem exists_s33_bad_labels_good_reduction (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (m : ℕ) :
    ∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ (1 : ℝ),∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.s33.pattern),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) →
    AppbS33SplitGeometry M r → (M.atoms.card : ℝ) ≤ 2*(1+Real.log L)^m →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ S,0 ≤ P S) → (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
    (∀ κ,A κ → ¬AppbS33LabelConditions M r L γ (min γ (1-γ)) w κ) →
      Nonempty (GoodDeletionReduction M .s33 r L γ δ η C1 w A P) := by
  intro δ hδ
  obtain ⟨L₀,hbase⟩ := uniform_s33_bad_labels_good_bound d hd γ hγ m δ hδ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hno hnt hconn hg hsize w A P hP hLG hbad
  obtain ⟨q,hq⟩ := hbase V D C1 hC1 L hL M r hM hconn hg hsize w A P hP hbad
  exact ⟨{
    labels := q
    step := .delete (ofMolecule M) .s33 r
    invariants := deletionPostInvariants r L (L^(-γ+η)/2) w A P q hM hno hnt hLG
    deviation := hq }⟩

/-- DH23 3S3-4G with failed rail-direction test and iterated half-gap. -/
theorem exists_s33_mismatch_good_reduction (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ (1 : ℝ),∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.s33.pattern),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) →
    AppbS33SplitTopology M r → (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    (¬(AppbOppositeFrom M (r.vertex 1) (r.vertex 2) (r.edge ⟨1,by decide⟩).val (r.edge ⟨3,by decide⟩).val ∧
       AppbOppositeFrom M (r.vertex 1) (r.vertex 2) (r.edge ⟨2,by decide⟩).val (r.edge ⟨4,by decide⟩).val)) →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ S,0 ≤ P S) → (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      Nonempty (GoodDeletionReduction M .s33 r L γ δ η C1 w A P) := by
  have hη' : 0 < 2*η/3 := by linarith only [hη]
  have hηγ' : 2*η/3 ≤ min γ (1-γ) := by linarith only [hη,hηγ]
  intro δ hδ
  obtain ⟨Lb,hbase⟩ := uniform_s33_mismatch_good_bound d hd γ hγ (2*η/3) hη' hηγ' m δ hδ
  obtain ⟨Lh,hh⟩ := eventually_atTop.mp (appb_half_gap_comparison_eventual γ η hη)
  refine ⟨max Lb Lh,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hno hnt hconn hg hsize hm w A P hP hLG
  have hLG' : ∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+2*η/3)) :=
    fun κ hκ => (hLG κ hκ).mono (hh L ((le_max_right Lb Lh).trans hL))
  obtain ⟨q,hq⟩ := hbase V D C1 hC1 L ((le_max_left Lb Lh).trans hL)
    M r hM hconn hg hsize hm w A P hP hLG'
  exact ⟨{
    labels := q
    step := .delete (ofMolecule M) .s33 r
    invariants := deletionPostInvariants r L (L^(-γ+η)/2) w A P q hM hno hnt hLG
    deviation := hq }⟩

end WaveTurbulence.Mole.AppbAlgorithm
