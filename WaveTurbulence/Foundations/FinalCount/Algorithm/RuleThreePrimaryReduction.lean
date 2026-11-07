/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33CommonTailReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33LabelReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D336GoodReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ReinsertLabelReductions
public import WaveTurbulence.Foundations.FinalCount.Algorithm.TerminalRungNextPriority
import Mathlib.Tactic

/-! # All primary double-rung decisions with their actual analytic outputs -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v

inductive RuleThreePrimaryReduction {V : Type v} {D : Type u}
    [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33.pattern)
    {d : ℕ} (L γ δ η C1 : ℝ) (w : Mom d)
    (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) : Prop
  | wrongDirections (ho : ¬AppbD33BoundaryOpposite M r)
      (h : Nonempty (GoodDeletionReduction M .d33 r L γ δ η C1 w A P)) :
      RuleThreePrimaryReduction M r L γ δ η C1 w A P
  | continuing (ho : AppbD33BoundaryOpposite M r) (hc : D33Continues r)
      (h : Nonempty (D33LabelReduction M r L γ δ C1 (L^(-γ+η)/2) w A P)) :
      RuleThreePrimaryReduction M r L γ δ η C1 w A P
  | newFigure (ho : AppbD33BoundaryOpposite M r) (hc : ¬D33Continues r)
      (t : AppbRealization M AppbPatternKind.d33new.pattern)
      (ht : t.vertex 1 = r.vertex 1 ∧ t.vertex 2 = r.vertex 2 ∧
        t.vertex 3 = r.vertex 3 ∧ t.vertex 4 = r.vertex 4)
      (h : Nonempty (GoodDeletionReduction M .d33new t L γ δ η C1 w A P)) :
      RuleThreePrimaryReduction M r L γ δ η C1 w A P
  | commonTail (ho : AppbD33BoundaryOpposite M r) (hc : ¬D33Continues r) (hn : ¬HasD33New r)
      (t : AppbRealization r.post AppbPatternKind.d33same.pattern)
      (ht : (t.vertex 1 = r.vertex 3 ∧ t.vertex 2 = r.vertex 4) ∨
        (t.vertex 1 = r.vertex 4 ∧ t.vertex 2 = r.vertex 3))
      (h : Nonempty (D33CommonTailReduction M r t L γ δ η C1 w A P)) :
      RuleThreePrimaryReduction M r L γ δ η C1 w A P
  | defective (ho : AppbD33BoundaryOpposite M r) (hc : ¬D33Continues r)
      (hn : ¬HasD33New r) (ht : ¬HasD33ResidualCommon r) (hdef : HasD33ComponentDefect r)
      (hi : Nonempty (D33ReinsertReduction M r L γ δ C1 (L^(-γ+η)/2) w
        (fun κ => A κ ∧ AppbD33LabelConditions M r L γ (min γ (1-γ)) w κ) P))
      (hg : Nonempty (GoodDeletionReduction M .d33 r L γ δ η C1 w
        (fun κ => A κ ∧ ¬AppbD33LabelConditions M r L γ (min γ (1-γ)) w κ) P)) :
      RuleThreePrimaryReduction M r L γ δ η C1 w A P
  | terminalRung (ho : AppbD33BoundaryOpposite M r) (hc : ¬D33Continues r)
      (hn : ¬HasD33New r) (ht : ¬HasD33ResidualCommon r)
      (hreg : ∀ b ∈ M.atoms,M.SameComponent (r.vertex 1) b → b ∉ r.removedAtoms → M.deg b = 4)
      (h : Nonempty (D33NormalReduction M r L γ δ C1 (L^(-γ+η)/2) w A P))
      (hnext : r.post.bonds.Nonempty ∧ ¬HasDegreeThreePair r.post 2 ∧ GraphPriority r.post) :
      RuleThreePrimaryReduction M r L γ δ η C1 w A P

/-- DH23 algorithm three(b)--(c): every ordered geometric decision and
both actual label branches are supplied with their concrete post problems.
The source terminal-rung scan's next priority is proved, not assumed. -/
theorem exists_rule_three_primary_reduction (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ))
    (c : ℝ) (hc : 1 ≤ c) :
    ∃ C₀ : ℝ,1 ≤ C₀ ∧ ∀ m : ℕ,∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ C₀,∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.d33.pattern),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) → (∀ e : D,¬Degen.IsBridge M e) →
    (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    AppbValidLinkScales M L w A c P → (∀ S,0 ≤ P S) →
    (∀ κ,A κ → ∀ x,κ (M.mate x) = κ x) →
    (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      RuleThreePrimaryReduction M r L γ δ η C1 w A P := by
  obtain ⟨Cb,hCb,hb⟩ := exists_d33_label_reduction d hd γ hγ c hc
  obtain ⟨Cn,hCn,hn⟩ := exists_d33_normal_reduction d hd γ hγ c hc
  obtain ⟨Ct,hCt,ht⟩ := exists_d33_common_tail_reduction d hd γ η hγ hη hηγ c hc
  refine ⟨max Cb (max Cn Ct),hCb.trans (le_max_left _ _),?_⟩
  intro m δ hδ
  obtain ⟨Lb,hLb⟩ := hb δ hδ
  obtain ⟨Ln,hLn⟩ := hn δ hδ
  obtain ⟨Lt,hLt⟩ := ht δ hδ
  obtain ⟨Lg,hLg⟩ := exists_d336_good_reduction d hd γ η hγ hη hηγ m δ hδ
  obtain ⟨Lw,hLw⟩ := exists_d33_same_direction_good_reduction d hd γ η hγ hη hηγ δ hδ
  obtain ⟨Li,hLi⟩ := exists_d33_reinsert_label_reductions d hd γ η hγ δ hδ
  refine ⟨max Lb (max Ln (max Lt (max Lg (max Lw Li)))),?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hno hnt hconn hbridge hsize w A P hv hP hm hLG
  obtain ⟨hCb',hCrest⟩ := max_le_iff.mp hC1
  obtain ⟨hCn',hCt'⟩ := max_le_iff.mp hCrest
  have hC1' := hCb.trans hCb'
  obtain ⟨hLb',hLrest⟩ := max_le_iff.mp hL
  obtain ⟨hLn',hLrest⟩ := max_le_iff.mp hLrest
  obtain ⟨hLt',hLrest⟩ := max_le_iff.mp hLrest
  obtain ⟨hLg',hLrest⟩ := max_le_iff.mp hLrest
  obtain ⟨hLw',hLi'⟩ := max_le_iff.mp hLrest
  cases exists_d33_rule_selection M r with
  | wrongDirections ho =>
    exact .wrongDirections ho (hLw V D C1 hC1' L hLw' M r hM hno hnt hconn hbridge ho w A P hP hLG)
  | continuing ho hcont =>
    have hd := hcont.boundary_four
    exact .continuing ho hcont (hLb V D C1 hCb' L hLb' M r hM hno hnt hbridge ho
      (d33_boundary_four_table r hd.1 hd.2) (L^(-γ+η)/2) w A P hv hP hm hLG)
  | newFigure ho hcont hnew =>
    obtain ⟨t,ht⟩ := hnew
    exact .newFigure ho hcont t ht (hLg V D C1 hC1' L hLg' M t hM hno hnt hconn hbridge hsize w A P hP hLG)
  | residualCommon ho hcont hnew htail =>
    obtain ⟨t,ht⟩ := htail
    exact .commonTail ho hcont hnew t ht (hLt V D C1 hCt' L hLt' M r hM hno hnt hconn hbridge ho t ht w A P hv hP hm hLG)
  | residualDefect ho hcont hnew htail hdef =>
    obtain ⟨hi,hg⟩ := hLi V D C1 hC1' L hLi' M r hM hno hnt hconn ho hbridge hdef.residualDefect w A P hP hLG
    exact .defective ho hcont hnew htail hdef hi hg
  | terminalRung ho hcont hnew htail hreg =>
    exact .terminalRung ho hcont hnew htail hreg
      (hLn V D C1 hCn' L hLn' M r hM hno hnt hbridge ho (d33_terminal_boundary_four r hreg)
        (L^(-γ+η)/2) w A P hv hm hLG)
      (terminal_rung_next_priority M hM hno hnt hconn r ho hcont htail hreg)

end WaveTurbulence.Mole.AppbAlgorithm
