/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.RuleTwoGeometry
public import WaveTurbulence.Foundations.FinalCount.Algorithm.S33NewGoodReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.S33LabelReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ReinsertLabelReductions
import Mathlib.Tactic

/-! # Complete actual analytic dispatch for source rule two -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v

inductive RuleTwoReduction {V : Type v} {D : Type u}
    [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) {d : ℕ} (L γ δ η C1 : ℝ) (w : Mom d)
    (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) : Prop
  | newFigure (k : AppbPatternKind)
      (hk : k ∈ ([AppbPatternKind.s33new1,.s33new2,.s33new3,.s33new4,.s33new5,.s33new6] : List _))
      (r : AppbRealization M k.pattern)
      (h : Nonempty (GoodDeletionReduction M k r L γ δ η C1 w A P)) :
      RuleTwoReduction M L γ δ η C1 w A P
  | connected (hn : ¬NewSinglePairFigure M)
      (r : AppbRealization M AppbPatternKind.s33.pattern)
      (hc : ∀ a ∈ r.post.atoms,∀ b ∈ r.post.atoms,r.post.SameComponent a b)
      (h : Nonempty (GoodDeletionReduction M .s33 r L γ δ η C1 w A P)) :
      RuleTwoReduction M L γ δ η C1 w A P
  | wrongDirections (hn : ¬NewSinglePairFigure M)
      (r : AppbRealization M AppbPatternKind.s33.pattern) (ht : AppbS33SplitTopology M r)
      (ho : ¬(AppbOppositeFrom M (r.vertex 1) (r.vertex 2) (r.edge ⟨1,by decide⟩).val (r.edge ⟨3,by decide⟩).val ∧
        AppbOppositeFrom M (r.vertex 1) (r.vertex 2) (r.edge ⟨2,by decide⟩).val (r.edge ⟨4,by decide⟩).val))
      (h : Nonempty (GoodDeletionReduction M .s33 r L γ δ η C1 w A P)) :
      RuleTwoReduction M L γ δ η C1 w A P
  | regular (hn : ¬NewSinglePairFigure M)
      (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
      (hd : ∀ a ∈ AppbPatternKind.s33.pattern.vertices,
        a ∉ AppbPatternKind.s33.pattern.removed → M.deg (r.vertex a) = 4)
      (hN : Nonempty (S33NormalReduction M r L γ δ C1 (L^(-γ+η)/2) w
        (fun κ => A κ ∧ AppbS33LabelConditions M r L γ (min γ (1-γ)) w κ) P))
      (hG : Nonempty (GoodDeletionReduction M .s33 r L γ δ η C1 w
        (fun κ => A κ ∧ ¬AppbS33LabelConditions M r L γ (min γ (1-γ)) w κ) P)) :
      RuleTwoReduction M L γ δ η C1 w A P
  | defective (hn : ¬NewSinglePairFigure M)
      (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
      (hd : ¬(M.deg (r.vertex 3) = 4 ∧ M.deg (r.vertex 5) = 4))
      (hI : Nonempty (S33ReinsertReduction M r L γ δ C1 (L^(-γ+η)/2) w
        (fun κ => A κ ∧ AppbS33LabelConditions M r L γ (min γ (1-γ)) w κ) P))
      (hG : Nonempty (GoodDeletionReduction M .s33 r L γ δ η C1 w
        (fun κ => A κ ∧ ¬AppbS33LabelConditions M r L γ (min γ (1-γ)) w κ) P)) :
      RuleTwoReduction M L γ δ η C1 w A P

/-- DH23 algorithm two(a)--(d): all graph tests and actual decoration
branches are constructed from the source standing premises. In particular,
no counting estimate or selected output is a premise of this result. -/
theorem exists_rule_two_reduction (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ C₀ : ℝ,1 ≤ C₀ ∧ ∀ m : ℕ,∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ C₀,∀ L ≥ L₀,∀ (M : Molecule V D),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) → (∀ e : D,¬Degen.IsBridge M e) →
    RuleTwoFigure M → (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ S,0 ≤ P S) → (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      RuleTwoReduction M L γ δ η C1 w A P := by
  obtain ⟨C₀,hC₀,hn⟩ := exists_s33_normal_label_reductions d hd γ η hγ
  refine ⟨C₀,hC₀,?_⟩
  intro m δ hδ
  obtain ⟨Ln,hLn⟩ := hn m δ hδ
  obtain ⟨Lg,hLg⟩ := exists_s33_new_good_reduction d hd γ η hγ hη hηγ m δ hδ
  obtain ⟨Lc,hLc⟩ := exists_s33_connected_good_reduction d hd γ η hγ δ hδ
  obtain ⟨Lw,hLw⟩ := exists_s33_mismatch_good_reduction d hd γ η hγ hη hηγ m δ hδ
  obtain ⟨Li,hLi⟩ := exists_s33_reinsert_label_reductions d hd γ η hγ m δ hδ
  refine ⟨max Ln (max Lg (max Lc (max Lw Li))),?_⟩
  intro V D instV instF instD C1 hC1 L hL M hM hno hnt hc hb hfig hsize w A P hP hLG
  have hLn' : Ln ≤ L := (le_max_left _ _).trans hL
  have htail : max Lg (max Lc (max Lw Li)) ≤ L := (le_max_right _ _).trans hL
  have hLg' : Lg ≤ L := (le_max_left _ _).trans htail
  have htail' : max Lc (max Lw Li) ≤ L := (le_max_right _ _).trans htail
  have hLc' : Lc ≤ L := (le_max_left _ _).trans htail'
  have htail'' : max Lw Li ≤ L := (le_max_right _ _).trans htail'
  have hLw' : Lw ≤ L := (le_max_left _ _).trans htail''
  have hLi' : Li ≤ L := (le_max_right _ _).trans htail''
  have hC1' := hC₀.trans hC1
  cases exists_rule_two_geometry M hc hb hfig with
  | newFigure h =>
    obtain ⟨k,hk,⟨r⟩⟩ := h
    exact .newFigure k hk r (hLg V D C1 hC1' L hLg' M k hk r hM hno hnt hc hb hsize w A P hP hLG)
  | connected hn r hp =>
    exact .connected hn r hp (hLc V D C1 hC1' L hLc' M r hM hno hnt hc hp w A P hP hLG)
  | wrongDirections hn r ht ho =>
    exact .wrongDirections hn r ht ho (hLw V D C1 hC1' L hLw' M r hM hno hnt hc ht hsize ho w A P hP hLG)
  | regular hn r hg hd =>
    obtain ⟨hN,hG⟩ := hLn V D C1 hC1 L hLn' M r hM hno hnt hc hb hg hsize hd w A P hP hLG
    exact .regular hn r hg hd hN hG
  | defective hn r hg hd =>
    obtain ⟨hI,hG⟩ := hLi V D C1 hC1' L hLi' M r hsize hM hno hnt hc hg hd w A P hP hLG
    exact .defective hn r hg hd hI hG

end WaveTurbulence.Mole.AppbAlgorithm
