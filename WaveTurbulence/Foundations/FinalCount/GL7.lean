/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL6
/-! **G3-LOWDEG (R48), part 7**: the structural conclusion `FinalStructL` of the LOW case (TARGET `finalmol`, structural part,
without `Flat`): degrees `1..4`, non-`ε` atoms of degree `≤ 2`, at most `R` imperfect components (`R` = the INITIAL index; the
current index `R' ≤ R` is smaller), every perfect component contains a `β`-atom. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

structure FinalStructL (R : ℕ) (s : St.{u} V D₀) : Prop where
  /-- at most `2R` atoms of odd degree -/
  odd_card_le : (s.M.atoms.filter fun a => ¬ Even (s.M.deg a)).card ≤ 2 * R
  odd_deg : ∀ a ∈ s.M.atoms, ¬ Even (s.M.deg a) → s.M.deg a = 1 ∨ s.M.deg a = 3
  deg_range : ∀ a ∈ s.M.atoms, 1 ≤ s.M.deg a ∧ s.M.deg a ≤ 4
  ab_deg : ∀ a ∈ s.M.atoms, s.cls a ≠ .eps → s.M.deg a ≤ 2
  /-- at most `R` imperfect components -/
  imperfect : ∃ reps : Finset V, reps ⊆ s.M.atoms ∧ reps.card ≤ R ∧ ∀ a ∈ s.M.atoms,
      (∃ b ∈ s.M.atoms, s.M.SameComponent a b ∧ contrib s b ≠ 0) → ∃ r ∈ reps, s.M.SameComponent a r
  /-- a perfect component contains a `β`-atom -/
  perfect_beta : ∀ a ∈ s.M.atoms, (∀ b ∈ s.M.atoms, s.M.SameComponent a b → contrib s b = 0) →
    ∃ b ∈ s.M.atoms, s.M.SameComponent a b ∧ s.cls b = .beta

theorem FinalStructL.of_good {s : St.{u} V D₀} {R' : ℕ} (hR' : R' ≤ R) (hg : Good R' s) (hC : CompBeta s) :
    FinalStructL R s where
  odd_card_le := by
    have hcard : ((s.M.atoms.filter fun a => ¬ Even (s.M.deg a)).card : ℤ) ≤ ∑ a ∈ s.M.atoms, contrib s a := by
      have h1 : ((s.M.atoms.filter fun a => ¬ Even (s.M.deg a)).card : ℤ) =
          ∑ a ∈ s.M.atoms, (if ¬ Even (s.M.deg a) then (1 : ℤ) else 0) := by
        rw [Finset.card_filter]; push_cast; rfl
      rw [h1]
      refine Finset.sum_le_sum fun a ha => ?_
      by_cases hodd : Even (s.M.deg a)
      · rw [if_neg (by simpa using hodd)]; exact hg.contrib_nonneg ha
      · rw [if_pos hodd]
        have h0 := hg.contrib_nonneg ha
        have : contrib s a ≠ 0 := by
          intro h00
          apply hodd
          have hpar : Even (contrib s a + (s.M.deg a : ℤ)) := by
            unfold contrib; simp only [sub_add_cancel]; exact Cls.even_base _
          rw [h00, zero_add] at hpar
          exact (Int.even_coe_nat _).1 hpar
        omega
    have := hg.sum_contrib
    have h2 : ((s.M.atoms.filter fun a => ¬ Even (s.M.deg a)).card : ℤ) ≤ 2 * ((R' : ℕ) : ℤ) := by
      rw [← this]; exact hcard
    have h3 : (R' : ℤ) ≤ (R : ℤ) := by exact_mod_cast hR'
    have h4 : (s.M.atoms.filter fun a => ¬ Even (s.M.deg a)).card ≤ 2 * R' := by exact_mod_cast h2
    omega
  odd_deg := by
    intro a ha hodd
    have h4 := deg_le_four s.M (hg.1.bounds a ha)
    by_cases he : s.cls a = .eps
    · have := hg.1.eps a ha he
      interval_cases hd : s.M.deg a
      · exact Or.inl rfl
      · exact absurd (by decide) hodd
      · exact Or.inr rfl
      · exact absurd (by decide) hodd
    · have := (hg.1.ab a ha he).1
      have h1 := (hg.1.ab a ha he).2.2 (hg.2 a ha)
      interval_cases hd : s.M.deg a
      · exact Or.inl rfl
      · exact absurd (by decide) hodd
  deg_range := by
    intro a ha
    have h4 := deg_le_four s.M (hg.1.bounds a ha)
    by_cases he : s.cls a = .eps
    · have := hg.1.eps a ha he; omega
    · have := (hg.1.ab a ha he).2.2 (hg.2 a ha); omega
  ab_deg := fun a ha he => (hg.1.ab a ha he).1
  imperfect := by
    obtain ⟨reps, h1, h2, h3⟩ := hg.imperfect_le
    exact ⟨reps, h1, h2.trans hR', h3⟩
  perfect_beta := by
    intro a ha hper
    obtain ⟨b, hb, hab, hprop⟩ := hC a ha (hg.2 a ha)
    rcases hprop with h | h
    · exact ⟨b, hb, hab, h⟩
    · exact absurd (hper b hb hab) h

end WaveTurbulence.FinalCountG3
