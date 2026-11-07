/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.S33ReinsertReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33ReinsertReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.S33PrimaryGoodReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33BadLabelReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.AdmissibilityPartition
import Mathlib.Tactic

/-! # Both source label branches when the passing branch reinserts a bond -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v

/-- DH23 rule three(c-ii): passing labels give the actual 3D3-3G post
problem, and failing labels give the actual 3D3-2G post problem. -/
theorem exists_d33_reinsert_label_reductions (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ (1 : ℝ),∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.d33.pattern),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) →
    AppbD33BoundaryOpposite M r → (∀ e : D,¬Degen.IsBridge M e) → AppbD33ResidualDefect M r →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ S,0 ≤ P S) → (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      Nonempty (D33ReinsertReduction M r L γ δ C1 (L^(-γ+η)/2) w
        (fun κ => A κ ∧ AppbD33LabelConditions M r L γ (min γ (1-γ)) w κ) P) ∧
      Nonempty (GoodDeletionReduction M .d33 r L γ δ η C1 w
        (fun κ => A κ ∧ ¬AppbD33LabelConditions M r L γ (min γ (1-γ)) w κ) P) := by
  intro δ hδ
  obtain ⟨Li,hi⟩ := exists_d33_reinsert_reduction d (by omega) γ hγ δ hδ
  obtain ⟨Lb,hb⟩ := exists_d33_bad_labels_good_reduction d hd γ η hγ δ hδ
  refine ⟨max Li Lb,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hno hnt hc ho hn hdef w A P hP hLG
  constructor
  · exact hi V D C1 hC1 L ((le_max_left Li Lb).trans hL) M r hM hno hc ho hn hdef
      (L^(-γ+η)/2) w _ P hP (fun κ hκ => hLG κ hκ.1) (fun κ hκ => hκ.2)
  · exact hb V D C1 hC1 L ((le_max_right Li Lb).trans hL) M r hM hno hnt hn ho
      w _ P hP (fun κ hκ => hLG κ hκ.1) (fun κ hκ => hκ.2)

/-- DH23 rule two(c): after choosing the defective 35 pair, both label
branches have actual good post problems; no label-test outcome is assumed. -/
theorem exists_s33_reinsert_label_reductions (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (m : ℕ) :
    ∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ (1 : ℝ),∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.s33.pattern),
    (M.atoms.card : ℝ) ≤ (1+Real.log L)^m → M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) → AppbS33SplitGeometry M r →
    ¬(M.deg (r.vertex 3) = 4 ∧ M.deg (r.vertex 5) = 4) →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ S,0 ≤ P S) → (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      Nonempty (S33ReinsertReduction M r L γ δ C1 (L^(-γ+η)/2) w
        (fun κ => A κ ∧ AppbS33LabelConditions M r L γ (min γ (1-γ)) w κ) P) ∧
      Nonempty (GoodDeletionReduction M .s33 r L γ δ η C1 w
        (fun κ => A κ ∧ ¬AppbS33LabelConditions M r L γ (min γ (1-γ)) w κ) P) := by
  intro δ hδ
  obtain ⟨Li,hi⟩ := exists_s33_reinsert_reduction d (by omega) γ hγ m δ hδ
  obtain ⟨Lb,hb⟩ := exists_s33_bad_labels_good_reduction d hd γ η hγ m δ hδ
  refine ⟨max Li Lb,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hsize hM hno hnt hc hg hdef w A P hP hLG
  constructor
  · exact hi V D C1 hC1 L ((le_max_left Li Lb).trans hL) M r hsize hM hno hc hg hdef
      (L^(-γ+η)/2) w _ P hP (fun κ hκ => hLG κ hκ.1) (fun κ hκ => hκ.2)
  · have hsize' : (M.atoms.card : ℝ) ≤ 2*(1+Real.log L)^m := by
      have hn : (0 : ℝ) ≤ M.atoms.card := Nat.cast_nonneg _
      linarith only [hsize,hn]
    exact hb V D C1 hC1 L ((le_max_right Li Lb).trans hL) M r hM hno hnt hc hg hsize'
      w _ P hP (fun κ hκ => hLG κ hκ.1) (fun κ hκ => hκ.2)

end WaveTurbulence.Mole.AppbAlgorithm
