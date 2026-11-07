/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.FinalCount.G3Flat
/-! **FINALCOUNT-G3**: the degree / classification / component part of DH23 Prop 9.5 (L1806--L1817) and TARGET
Prop `finalmol` (L2182--L2190), for the final molecule of a run. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **Prop 9.5, structural part** for a state `s` (the final state of a run). -/
structure FinalStruct (R : ℕ) (s : St.{u} V D₀) : Prop where
  /-- exactly `2R` atoms of odd degree (`R = 1`: "two atoms of degree 1 and 3"), each of degree `1` or `3` -/
  odd_card : (s.M.atoms.filter fun a => ¬ Even (s.M.deg a)).card = 2 * R
  odd_deg : ∀ a ∈ s.M.atoms, ¬ Even (s.M.deg a) → s.M.deg a = 1 ∨ s.M.deg a = 3
  /-- all degrees are `1, 2, 3, 4` ("all the other atoms have degree 2 and 4") -/
  deg_range : ∀ a ∈ s.M.atoms, 1 ≤ s.M.deg a ∧ s.M.deg a ≤ 4
  /-- atoms of degree `1, 2` are `α`- or `β`-atoms; `ε`-atoms have degree `3, 4` -/
  low_deg : ∀ a ∈ s.M.atoms, s.M.deg a ≤ 2 → (∃ ρ kp, s.cls a = .alpha ρ kp) ∨ s.cls a = .beta
  eps_deg : ∀ a ∈ s.M.atoms, s.cls a = .eps → 3 ≤ s.M.deg a
  /-- an `α`- or `β`-atom has degree `≤ 2` -/
  ab_deg : ∀ a ∈ s.M.atoms, s.cls a ≠ .eps → s.M.deg a ≤ 2
  /-- at most `R` imperfect components (TARGET finalmol L2188--L2190) -/
  imperfect : ∃ reps : Finset V, reps ⊆ s.M.atoms ∧ reps.card ≤ R ∧ ∀ a ∈ s.M.atoms,
      (∃ b ∈ s.M.atoms, s.M.SameComponent a b ∧ contrib s b ≠ 0) → ∃ r ∈ reps, s.M.SameComponent a r
  /-- every component without an atom of odd degree (an even component) contains a `β`-atom -/
  even_beta : ∀ a ∈ s.M.atoms, (∀ b ∈ s.M.atoms, s.M.SameComponent a b → Even (s.M.deg b)) →
      ∃ b ∈ s.M.atoms, s.M.SameComponent a b ∧ s.cls b = .beta
  /-- for `R = 1` all odd atoms lie in one component (the odd component) -/
  odd_comp : R = 1 → ∀ a ∈ s.M.atoms, ∀ b ∈ s.M.atoms, ¬ Even (s.M.deg a) → ¬ Even (s.M.deg b) →
      s.M.SameComponent a b

theorem FinalStruct.of_good {R : ℕ} {s : St.{u} V D₀} (hg : Good R s) (hC : CompBeta s) (hF : Flat s) :
    FinalStruct R s where
  odd_card := hF.odd_card hg
  odd_deg := by
    intro a ha hodd
    have hle := deg_le_four s.M (hg.1.bounds a ha)
    by_cases he : s.cls a = .eps
    · have := hF.eps3 ha he
      interval_cases hd : s.M.deg a
      · exact Or.inr rfl
      · exact absurd (by decide) hodd
    · have := (hg.1.ab a ha he).1
      have := (hg.1.ab a ha he).2.2 (hg.2 a ha)
      interval_cases hd : s.M.deg a
      · exact Or.inl rfl
      · exact absurd (by decide) hodd
  deg_range := by
    intro a ha
    have hle := deg_le_four s.M (hg.1.bounds a ha)
    by_cases he : s.cls a = .eps
    · have := hF.eps3 ha he; omega
    · have := (hg.1.ab a ha he).2.2 (hg.2 a ha); omega
  low_deg := by
    intro a ha hd
    by_cases he : s.cls a = .eps
    · have := hF.eps3 ha he; omega
    · rcases hc : s.cls a with _ | ⟨ρ, kp⟩ | _ | _
      · exact absurd hc he
      · exact Or.inl ⟨ρ, kp, rfl⟩
      · exact Or.inr rfl
      · exact absurd hc (hg.2 a ha)
  eps_deg := fun a ha he => hF.eps3 ha he
  ab_deg := fun a ha he => (hg.1.ab a ha he).1
  imperfect := hg.imperfect_le
  even_beta := by
    intro a ha hev
    obtain ⟨b, hb, hab, hprop⟩ := hC a ha (hg.2 a ha)
    rcases hprop with h | h
    · exact ⟨b, hb, hab, h⟩
    · exfalso
      rw [hF.contrib_eq hg hb] at h
      rw [if_neg (by simpa using hev b hb hab)] at h
      exact h rfl
  odd_comp := by
    rintro rfl a ha b hb hoa hob
    obtain ⟨reps, _, hcard, hcov⟩ := hg.imperfect_le
    have hnz : ∀ x ∈ s.M.atoms, ¬ Even (s.M.deg x) → contrib s x ≠ 0 := by
      intro x hx hodd h0
      apply hodd
      unfold contrib at h0
      have h1 : (s.cls x).base = (s.M.deg x : ℤ) := by linarith
      have h2 : Even (s.cls x).base := by
        rcases hc : s.cls x <;> simp [Cls.base] <;> decide
      rw [h1] at h2
      exact (Int.even_coe_nat _).mp h2
    obtain ⟨ra, hra, hara⟩ := hcov a ha ⟨a, ha, Relation.EqvGen.refl _, hnz a ha hoa⟩
    obtain ⟨rb, hrb, hbrb⟩ := hcov b hb ⟨b, hb, Relation.EqvGen.refl _, hnz b hb hob⟩
    have : ra = rb := by
      have : reps.card ≤ 1 := hcard
      exact Finset.card_le_one.1 this ra hra rb hrb
    subst this
    exact Relation.EqvGen.trans _ _ _ hara (Relation.EqvGen.symm _ _ hbrb)

theorem good_flat_rtg {R : ℕ} {step : St.{u} V D₀ → St.{u} V D₀ → Prop}
    (hstep : ∀ s s', step s s' → Good R s → Flat s → Good R s' ∧ Flat s') {a b : St.{u} V D₀}
    (h : Relation.ReflTransGen step a b) : Good R a → Flat a → Good R b ∧ Flat b := by
  induction h with
  | refl => exact fun g c => ⟨g, c⟩
  | tail _ hs ih =>
    exact fun g c => by
      obtain ⟨g', c'⟩ := ih g c
      exact hstep _ _ hs g' c'

/-- Along a run, the state is flat. -/
theorem Run.flat {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}
    {sf : St.{u} V D₀} (hr : Run L γ η w κ (St.init M₀) sf) (hS : SubHyp R M₀) : Flat sf := by
  obtain ⟨s₁, s₂, s₃, h1, _, h2, _, h3, _, h4, _⟩ := hr
  have g0 : Good R (St.init M₀) := ⟨hS.inv, St.init_clean M₀⟩
  have r1 := good_flat_rtg (fun _ _ h g f => ⟨h.good g, h.flat f⟩) h1 g0 (Flat.init hS)
  have r2 := good_flat_rtg (fun _ _ h g f => ⟨h.good g, h.flat f g.2⟩) h2 r1.1 r1.2
  have r3 := good_flat_rtg (fun _ _ h g f => ⟨h.good g, h.flat f⟩) h3 r2.1 r2.2
  exact (good_flat_rtg (fun _ _ h g f => ⟨h.good g, h.flat f⟩) h4 r3.1 r3.2).2

/-- The structural part of Prop 9.5 for the final molecule of a run of the stage-2 algorithm. -/
theorem Run.finalStruct {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}
    {sf : St.{u} V D₀} (hr : Run L γ η w κ (St.init M₀) sf) (hS : SubHyp R M₀) : FinalStruct R sf := by
  obtain ⟨hg, hC⟩ := hr.goodComp hS
  exact FinalStruct.of_good hg hC (hr.flat hS)

end WaveTurbulence.FinalCountG3
