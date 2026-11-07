/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.S33NormalReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.S33PrimaryGoodReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.AdmissibilityPartition
import Mathlib.Tactic

/-! # Both actual label branches of the normal split 3S3 case -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v

/-- DH23 rule two(b), degree-four boundary case: the passing test gives
3S3-1N and its complement gives 3S3-2G, each with a concrete post problem.
The original problem is covered by the binary partition theorem. -/
theorem exists_s33_normal_label_reductions (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C₀ : ℝ,1 ≤ C₀ ∧ ∀ m : ℕ,∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ C₀,∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.s33.pattern),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) → (∀ e : D,¬Degen.IsBridge M e) →
    AppbS33SplitGeometry M r → (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    (∀ a ∈ AppbPatternKind.s33.pattern.vertices,a ∉ AppbPatternKind.s33.pattern.removed → M.deg (r.vertex a) = 4) →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ S,0 ≤ P S) → (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      Nonempty (S33NormalReduction M r L γ δ C1 (L^(-γ+η)/2) w
        (fun κ => A κ ∧ AppbS33LabelConditions M r L γ (min γ (1-γ)) w κ) P) ∧
      Nonempty (GoodDeletionReduction M .s33 r L γ δ η C1 w
        (fun κ => A κ ∧ ¬AppbS33LabelConditions M r L γ (min γ (1-γ)) w κ) P) := by
  obtain ⟨C₀,Ln,hC₀,hn⟩ := exists_s33_normal_reduction d hd γ hγ
  refine ⟨C₀,hC₀,?_⟩
  intro m δ hδ
  obtain ⟨Lg,hg⟩ := exists_s33_bad_labels_good_reduction d hd γ η hγ m δ hδ
  refine ⟨max Ln Lg,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hno hnt hc hb hgeom hsize hdeg w A P hP hLG
  constructor
  · exact hn V D C1 hC1 L ((le_max_left Ln Lg).trans hL) δ hδ M r hM hno hnt hc hb hgeom hdeg
      (L^(-γ+η)/2) w _ P (fun κ hκ => hκ.2) (fun κ hκ => hLG κ hκ.1)
  · have hsize' : (M.atoms.card : ℝ) ≤ 2*(1+Real.log L)^m := by
      have hn : (0 : ℝ) ≤ M.atoms.card := Nat.cast_nonneg _
      linarith only [hsize,hn]
    exact hg V D C1 (hC₀.trans hC1) L ((le_max_right Ln Lg).trans hL) M r hM hno hnt hc hgeom hsize'
      w _ P hP (fun κ hκ => hLG κ hκ.1) (fun κ hκ => hκ.2)

end WaveTurbulence.Mole.AppbAlgorithm
