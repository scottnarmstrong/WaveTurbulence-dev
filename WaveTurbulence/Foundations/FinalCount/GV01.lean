/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL19
public import WaveTurbulence.Foundations.FinalCount.GM08
public import WaveTurbulence.Foundations.FinalCount.G3AncJoint
public import WaveTurbulence.Foundations.FinalCount.G3Anc
public import WaveTurbulence.Foundations.FinalCount.G3Init
/-! **G3-LOWDEG port of `G3AncJoint`** (only the declarations that change: `SubHypL->SubHypL`, `HRunL->HRunL`, `InvL->InvL`, `FinalStructM->FinalStructM`, `Prop95ConclAtL->Prop95ConclAtL`; names get suffix `L`). -/
@[expose] public section
open WaveTurbulence.VineParamContract

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀}

theorem sum_deg_ne_fourL {R : ℕ} (hS : SubHypL R M₀) (h4 : ∀ b ∈ M₀.atoms, M₀.deg b = 4) : False := by
  have h1 := sum_deg_eq M₀
  have h2 := card_darts_eq_two_bonds M₀
  have h3 := hS.count
  have h5 : ∑ b ∈ M₀.atoms, M₀.deg b = 4 * M₀.atoms.card := by
    rw [Finset.sum_congr rfl h4]; simp [mul_comm]
  have := hS.one_le
  omega

/-- **E10, part 1**: the joints of a final component all of whose other atoms are `ε` of degree `4` have distinct
ancestors. -/
theorem anc_ne_jointsL {R : ℕ} (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s) (hS : SubHypL R M₀)
    {j₁ j₂ : V} (h1 : j₁ ∈ hf.s.M.atoms) (h2 : j₂ ∈ hf.s.M.atoms) (hne : j₁ ≠ j₂)
    (hd1 : hf.s.M.deg j₁ = 2) (hd2 : hf.s.M.deg j₂ = 2) (hn1 : hf.s.cls j₁ ≠ .eps) (hn2 : hf.s.cls j₂ ≠ .eps)
    (hsame : hf.s.M.SameComponent j₁ j₂)
    (hcomp : ∀ b ∈ hf.s.M.atoms, hf.s.M.SameComponent j₁ b →
      b = j₁ ∨ b = j₂ ∨ (hf.s.cls b = .eps ∧ hf.s.M.deg b = 4)) :
    hf.anc j₁ ≠ hf.anc j₂ := by
  intro hEq
  set a := hf.anc j₁ with ha
  have ham : a ∈ M₀.atoms := hA.mem j₁ h1
  -- the four darts at the joints exhaust the darts at `a`
  have hdis : Disjoint (hf.s.M.dartsAt j₁) (hf.s.M.dartsAt j₂) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
    exact hne (hx1.symm.trans hx2)
  have hsub : ((hf.s.M.dartsAt j₁) ∪ (hf.s.M.dartsAt j₂)).image hf.s.down ⊆ M₀.dartsAt a := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
    rw [hA.atom x]
    rcases hx with hx | hx
    · rw [hx]
    · rw [hx, ← hEq]
  have hc4 : (((hf.s.M.dartsAt j₁) ∪ (hf.s.M.dartsAt j₂)).image hf.s.down).card = 4 := by
    rw [Finset.card_image_of_injective _ hA.inj, Finset.card_union_of_disjoint hdis]
    have e1 : (hf.s.M.dartsAt j₁).card = 2 := hd1
    have e2 : (hf.s.M.dartsAt j₂).card = 2 := hd2
    omega
  have hle : M₀.deg a ≤ 4 := deg_le_four M₀ (hS.bounds a ham)
  have hall : M₀.dartsAt a = ((hf.s.M.dartsAt j₁) ∪ (hf.s.M.dartsAt j₂)).image hf.s.down :=
    (Finset.eq_of_subset_of_card_le hsub (by have : (M₀.dartsAt a).card ≤ 4 := hle; omega)).symm
  have hdeg_a : M₀.deg a = 4 := by
    have : (M₀.dartsAt a).card = 4 := by rw [hall]; exact hc4
    exact this
  -- the ancestor set
  let InS : V → Prop := fun b => b = a ∨ ∃ c ∈ hf.s.M.atoms, hf.s.M.SameComponent j₁ c ∧ hf.s.cls c = .eps ∧ b = c
  have hmateS : ∀ x : hf.s.D, hf.s.M.SameComponent j₁ (hf.s.M.atom x) → InS (M₀.atom (M₀.mate (hf.s.down x))) := by
    intro x hx
    rw [hD.mate x, hA.atom]
    have hc : hf.s.M.SameComponent j₁ (hf.s.M.atom (hf.s.M.mate x)) :=
      Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.rel _ _ ⟨x, rfl, rfl⟩)
    rcases hcomp _ (hf.s.M.atom_mem _) hc with e | e | ⟨hε, _⟩
    · left; rw [e]
    · left; rw [e, ← hEq]
    · right
      exact ⟨_, hf.s.M.atom_mem _, hc, hε, hA.eps _ (hf.s.M.atom_mem _) hε⟩
  have hclosed : ∀ z : D₀, InS (M₀.atom z) → InS (M₀.atom (M₀.mate z)) := by
    intro z hz
    rcases hz with hz | ⟨c, hcm, hcc, hcε, hz⟩
    · have : z ∈ M₀.dartsAt a := by simp [Molecule.dartsAt, hz]
      rw [hall] at this
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 this
      apply hmateS
      rcases Finset.mem_union.1 hx with hx | hx
      · simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [hx]; exact Relation.EqvGen.refl _
      · simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [hx]; exact hsame
    · obtain ⟨x, hx⟩ := hA.surj c hcm hcε z hz
      have hax : hf.s.M.atom x = c := hA.uniq _ (hf.s.M.atom_mem x) c hcm hcε (by rw [← hA.atom x, hx, hz])
      rw [← hx]
      exact hmateS x (by rw [hax]; exact hcc)
  have hiff : ∀ u v, M₀.Adj u v → (InS u ↔ InS v) := by
    rintro u v ⟨z, rfl, rfl⟩
    refine ⟨hclosed z, fun h => ?_⟩
    have := hclosed _ h
    rwa [M₀.mate_mate] at this
  have hall' : ∀ u v, Relation.EqvGen M₀.Adj u v → (InS u ↔ InS v) := by
    intro u v h
    induction h with
    | rel _ _ h => exact hiff _ _ h
    | refl _ => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  refine sum_deg_ne_fourL hS (fun b hb => ?_)
  have hbS : InS b := (hall' a b (hS.conn a ham b hb)).1 (Or.inl rfl)
  rcases hbS with hb | ⟨c, hcm, hcc, hcε, hb⟩
  · rw [hb]; exact hdeg_a
  · rw [hb, hA.deg_eps hcm hcε]
    rcases hcomp c hcm hcc with e | e | ⟨_, h4⟩
    · exact absurd (e ▸ hcε) hn1
    · exact absurd (e ▸ hcε) hn2
    · exact h4

end WaveTurbulence.FinalCountG3

