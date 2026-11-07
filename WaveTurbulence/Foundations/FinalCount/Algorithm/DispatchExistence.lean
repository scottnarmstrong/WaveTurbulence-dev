/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.Dispatch
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GraphPriorities
import Mathlib.Tactic

/-! # Every nonterminal source input has a concrete analytic dispatch

This constructs the next source operation, including its label branches.
It does not yet iterate the dispatch or assert the good-operation count.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v

private theorem r3_boundary_four_table {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} (r : AppbRealization M AppbPatternKind.r3.pattern)
    (h2 : M.deg (r.vertex 2) = 4) (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4) :
    ∀ a ∈ AppbPatternKind.r3.pattern.vertices,
      a ∉ AppbPatternKind.r3.pattern.removed → M.deg (r.vertex a) = 4 := by
  intro a ha hka
  have hlabels : AppbPatternKind.r3.pattern.vertices \ AppbPatternKind.r3.pattern.removed = {2,3,4} := by decide
  have ha' : a = 2 ∨ a = 3 ∨ a = 4 := by
    have hh := Finset.mem_sdiff.mpr ⟨ha,hka⟩
    rw [hlabels] at hh
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  rcases ha' with rfl | rfl | rfl <;> assumption

/-- DH23 Appendix B rules one through seven, with every count bound and
actual post problem proved from the standing premises. Thresholds are
uniform in both finite graph carriers. Full iteration is a separate result. -/
theorem exists_dispatch (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ))
    (c : ℝ) (hc : 1 ≤ c) :
    ∃ C₀ : ℝ,1 ≤ C₀ ∧ ∀ m : ℕ,∀ δ ∈ Ioc (0 : ℝ) 1,∀ C1 ≥ C₀,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ L ≥ L₀,∀ (M : Molecule V D),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) → M.bonds.Nonempty →
    (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    AppbValidLinkScales M L w A c P → (∀ S,0 ≤ P S) →
    (∀ κ,A κ → ∀ x,κ (M.mate x) = κ x) →
    (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      Dispatch M L γ δ η C1 w A P := by
  obtain ⟨C2,hC2,h2⟩ := exists_rule_two_reduction d hd γ η hγ hη hηγ
  obtain ⟨C3,hC3,h3⟩ := exists_rule_three_primary_reduction d hd γ η hγ hη hηγ c hc
  obtain ⟨C6,hC6,h6⟩ := exists_rule_six_reduction d hd γ η hγ hη hηγ
  refine ⟨max C2 (max C3 C6),hC2.trans (le_max_left _ _),?_⟩
  intro m δ hδ C1 hC1
  obtain ⟨hC2',hCtail⟩ := max_le_iff.mp hC1
  obtain ⟨hC3',hC6'⟩ := max_le_iff.mp hCtail
  have hC1' : 1 ≤ C1 := hC2.trans hC2'
  obtain ⟨L2,hL2⟩ := h2 m δ hδ
  obtain ⟨L3,hL3⟩ := h3 m δ hδ
  obtain ⟨L6,hL6⟩ := h6 m δ hδ
  obtain ⟨Lc,hLc⟩ := exists_d33_common_good_reduction d hd γ η hγ hη hηγ δ hδ
  obtain ⟨L4,hL4⟩ := exists_d34_good_reduction d hd γ hγ η δ hδ
  obtain ⟨L5,hL5⟩ := exists_s32_good_reduction d hd γ η hγ hη hηγ δ hδ
  obtain ⟨L7,hL7⟩ := exists_rule_seven_fine_reduction d (by omega) δ γ η C1 hδ hγ hη hηγ hC1'
  refine ⟨max L2 (max L3 (max L6 (max Lc (max L4 (max L5 (max L7 (Real.exp 1))))))),?_⟩
  intro V D instV instF instD L hL M hM hno hnt hconn hne hsize w A P hv hP hm hLG
  obtain ⟨hL2',hLtail⟩ := max_le_iff.mp hL
  obtain ⟨hL3',hLtail⟩ := max_le_iff.mp hLtail
  obtain ⟨hL6',hLtail⟩ := max_le_iff.mp hLtail
  obtain ⟨hLc',hLtail⟩ := max_le_iff.mp hLtail
  obtain ⟨hL4',hLtail⟩ := max_le_iff.mp hLtail
  obtain ⟨hL5',hLtail⟩ := max_le_iff.mp hLtail
  obtain ⟨hL7',hexp⟩ := max_le_iff.mp hLtail
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hexp
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hexp
  cases exists_graph_priority M hM hno hnt hne with
  | bridge e he =>
    exact .bridge ⟨e,he⟩ (exists_bridge_reduction (ofMolecule M) hM hno hnt ⟨e,he⟩ hLp hδ.1
      (zero_lt_one.trans_le hC1') hlog γ (L^(-γ+η)/2) w A P hP hLG)
  | single hb hfig =>
    exact .single hb (hL2 V D C1 hC2' L hL2' M hM hno hnt hconn hb hfig hsize w A P hP hLG)
  | double hb h1 hfig =>
    rcases hfig with hfig | hfig
    · obtain ⟨r⟩ := hfig
      exact .double hb h1 r (hL3 V D C1 hC3' L hL3' M r hM hno hnt hconn hb hsize w A P hv hP hm hLG)
    · obtain ⟨r⟩ := hfig
      exact .common hb h1 r (hLc V D C1 hC1' L hLc' M r hM hno hnt hconn hb w A P hP hLG)
  | mixedDouble hb h1 h2 hfig =>
    obtain ⟨k,hk,⟨r⟩⟩ := hfig
    have hk' : k ∈ appbD34Kinds := hk
    exact .mixedDouble hb h1 h2 k hk' r (hL4 V D C1 hC1' L hL4' M k hk' r hM hno hnt hconn hb w A P hP hLG)
  | mixedSingle hb h1 h2 h4 hfig =>
    obtain ⟨k,hk,⟨r⟩⟩ := hfig
    have hk' : k ∈ appbS32Kinds := hk
    exact .mixedSingle hb h1 h2 h4 k hk' r (hL5 V D C1 hC1' L hL5' M k hk' r hM hno hnt hconn hb w A P hP hLG)
  | regular hb h1 h2 h4 h32 r hd2 hd3 hd4 =>
    rcases hL6 V D C1 hC6' L hL6' M r hM hno hnt hconn hb
        (r3_boundary_four_table r hd2 hd3 hd4) hsize w A P hP hLG with hn | ⟨t,hc,hg⟩
    · exact .regularNormal hb h1 h2 h4 h32 r hn
    · exact .regularGood hb h1 h2 h4 h32 r t hc hg
  | fine hb h3 hfig =>
    exact .fine hb h3 (hL7 V D L hL7' M hM hno hnt hconn hb h3 hne w A P hLG)

end WaveTurbulence.Mole.AppbAlgorithm
