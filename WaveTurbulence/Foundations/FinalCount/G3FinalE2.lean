/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3FinalE
/-! **FINALCOUNT-G3: TARGET `finalmol` in the corrected form** (errata E9).

For a run `HRunE … t` with `t` tame-atom erasures:
* at most `R + t` imperfect components (not `R`);
* `ε`-atoms need not have degree `≥ 3` (neighbours of an erased atom can have degree `1` or `2`) once `t > 0`;
* `ε`-atoms are LG, or tame (`Tm`) when they have a zero gap;
* the balance of the degree-`2` atoms is claimed for `α`/`β`-atoms only;
* an even component without an `ε`-atom of degree `≤ 2` that is also free of... (perfect components) has a `β`-atom,
  is a cycle (double bond, length `≥ 4`, triangle with `≤ 1` `α`-atom) or has chains with two distinct `ε` ends.
For `t = 0` all the original statements hold. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- **Prop 9.5 / `finalmol`, structural part, with `t` erasures.** -/
structure FinalStructE (R t : ℕ) (s : St.{u} V D₀) : Prop where
  /-- at most `2(R + t)` atoms of odd degree; exactly `2R` if no erasure -/
  odd_card_le : (s.M.atoms.filter fun a => ¬ Even (s.M.deg a)).card ≤ 2 * (R + t)
  odd_card : t = 0 → (s.M.atoms.filter fun a => ¬ Even (s.M.deg a)).card = 2 * R
  odd_deg : ∀ a ∈ s.M.atoms, ¬ Even (s.M.deg a) → s.M.deg a = 1 ∨ s.M.deg a = 3
  deg_range : ∀ a ∈ s.M.atoms, 1 ≤ s.M.deg a ∧ s.M.deg a ≤ 4
  /-- atoms of degree `≤ 2` are `α`/`β`-atoms, except `ε`-atoms damaged by an erasure -/
  low_deg : ∀ a ∈ s.M.atoms, s.M.deg a ≤ 2 →
    (∃ ρ kp, s.cls a = .alpha ρ kp) ∨ s.cls a = .beta ∨ (s.cls a = .eps ∧ 0 < t)
  eps_deg : t = 0 → ∀ a ∈ s.M.atoms, s.cls a = .eps → 3 ≤ s.M.deg a
  ab_deg : ∀ a ∈ s.M.atoms, s.cls a ≠ .eps → s.M.deg a ≤ 2
  /-- at most `R + t` imperfect components -/
  imperfect : ∃ reps : Finset V, reps ⊆ s.M.atoms ∧ reps.card ≤ R + t ∧ ∀ a ∈ s.M.atoms,
      (∃ b ∈ s.M.atoms, s.M.SameComponent a b ∧ contrib s b ≠ 0) → ∃ r ∈ reps, s.M.SameComponent a r
  /-- a perfect component contains a `β`-atom -/
  perfect_beta : ∀ a ∈ s.M.atoms, (∀ b ∈ s.M.atoms, s.M.SameComponent a b → contrib s b = 0) →
    ∃ b ∈ s.M.atoms, s.M.SameComponent a b ∧ s.cls b = .beta

theorem FinalStructE.of_inv {t : ℕ} {s : St.{u} V D₀} (hg0 : t = 0 → Good R s) {R' : ℕ} (hR' : R' ≤ R + t)
    (hg : Good R' s) (hC : CompBeta s)
    (hF : t = 0 → Flat s) : FinalStructE R t s where
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
    have h3 : (R' : ℤ) ≤ ((R + t : ℕ) : ℤ) := by exact_mod_cast hR'
    have h4 : (s.M.atoms.filter fun a => ¬ Even (s.M.deg a)).card ≤ 2 * R' := by exact_mod_cast h2
    omega
  odd_card := fun ht => by
    subst ht
    exact (hF rfl).odd_card (hg0 rfl)
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
  low_deg := by
    intro a ha hd
    by_cases he : s.cls a = .eps
    · right; right
      refine ⟨he, ?_⟩
      by_contra h0
      have ht : t = 0 := by omega
      have := (hF ht).eps3 ha he
      omega
    · rcases hc : s.cls a with _ | ⟨ρ, kp⟩ | _ | _
      · exact absurd hc he
      · exact Or.inl ⟨ρ, kp, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact absurd hc (hg.2 a ha)
  eps_deg := fun ht a ha he => (hF ht).eps3 ha he
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
