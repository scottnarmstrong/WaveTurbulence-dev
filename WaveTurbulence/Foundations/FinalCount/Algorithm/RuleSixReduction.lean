/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.RuleSixSelection
public import WaveTurbulence.Foundations.FinalCount.Algorithm.R3NormalReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.R32GoodReduction
import Mathlib.Tactic

/-! # Source rule six selects a complete normal or good counting reduction -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v

/-- DH23 Appendix B rule six, including the actual special-bond test in
the scanned component. The result contains concrete post predicates and
proved deviations; no analytic bound is an input. -/
theorem exists_rule_six_reduction (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ C₀ : ℝ,1 ≤ C₀ ∧ ∀ m : ℕ,∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ C₀,∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.r3.pattern),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) →
    (∀ e : D,¬Degen.IsBridge M e) →
    (∀ a ∈ AppbPatternKind.r3.pattern.vertices,a ∉ AppbPatternKind.r3.pattern.removed → M.deg (r.vertex a) = 4) →
    (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ S,0 ≤ P S) → (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
    Nonempty (R3NormalReduction M r L γ δ C1 (L^(-γ+η)/2) w A P) ∨
      ∃ t : AppbRealization r.post AppbPatternKind.s33new3.pattern,
        M.SameComponent (r.vertex 1) (t.vertex 1) ∧ Nonempty (R32GoodReduction M r t L γ δ η C1 w A P) := by
  obtain ⟨C₀,LN,hC₀,hN⟩ := exists_r3_normal_reduction d hd γ hγ
  refine ⟨C₀,hC₀,?_⟩
  intro m δ hδ
  obtain ⟨LG,hG⟩ := exists_r32_good_reduction d hd γ hγ δ η hδ hη hηγ m
  refine ⟨max LN LG,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hno hnt hconn hb hd hsize w A P hP hLG
  cases exists_rule_six_selection M hno r with
  | normal hn =>
    exact Or.inl (hN V D C1 hC1 L ((le_max_left LN LG).trans hL) δ hδ M r hM hno hnt hb hd hn
      (L^(-γ+η)/2) w A P hLG)
  | good t hc =>
    exact Or.inr ⟨t,hc,hG V D C1 (hC₀.trans hC1) L ((le_max_right LN LG).trans hL)
      M r t hM hno hnt hconn hb hsize w A P hP hLG⟩

end WaveTurbulence.Mole.AppbAlgorithm
