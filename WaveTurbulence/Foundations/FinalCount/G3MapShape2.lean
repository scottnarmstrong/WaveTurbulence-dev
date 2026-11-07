/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3MapShape
/-! **FINALCOUNT-G3: `FinalShape` for a component** (second part: parity, `β`-atoms, cycles, chains). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {Tm : V → Prop} {hf : HSt V D₀}

/-- `odd`: the component contains an atom of odd degree. -/
def CompOdd (hf : HSt V D₀) (a₀ : V) : Prop := ∃ b ∈ (compMol hf.s.M a₀).atoms, ¬ Even ((compMol hf.s.M a₀).deg b)

section shape2
variable (hC : Prop95ConclAt L γ η w κ R hf Tm) {a₀ : V} (ha₀ : a₀ ∈ hf.s.M.atoms)
include hC ha₀

theorem shape_evenDeg : ¬ CompOdd hf a₀ → ∀ a ∈ (compMol hf.s.M a₀).atoms,
    (compMol hf.s.M a₀).deg a = 2 ∨ (compMol hf.s.M a₀).deg a = 4 := by
  intro hn a ha
  have h := (mem_compMol _ _).1 ha
  have hev : Even ((compMol hf.s.M a₀).deg a) := by
    by_contra hc; exact hn ⟨a, ha, hc⟩
  rw [compMol_deg _ _ h.2] at hev ⊢
  have hr := hC.struct.deg_range a h.1
  obtain ⟨k, hk⟩ := hev
  omega

theorem shape_oddDeg (hR : R = 1) : CompOdd hf a₀ → ∃ u ∈ (compMol hf.s.M a₀).atoms, ∃ x ∈ (compMol hf.s.M a₀).atoms,
    u ≠ x ∧ ((compMol hf.s.M a₀).deg u = 1 ∨ (compMol hf.s.M a₀).deg u = 3) ∧
    ((compMol hf.s.M a₀).deg x = 1 ∨ (compMol hf.s.M a₀).deg x = 3) ∧
    ∀ a ∈ (compMol hf.s.M a₀).atoms, a ≠ u → a ≠ x →
      (compMol hf.s.M a₀).deg a = 2 ∨ (compMol hf.s.M a₀).deg a = 4 := by
  rintro ⟨b, hb, hbo⟩
  have hb' := (mem_compMol _ _).1 hb
  rw [compMol_deg _ _ hb'.2] at hbo
  have hcard := hC.struct.odd_card
  rw [hR, mul_one] at hcard
  obtain ⟨u, x, hux, hset⟩ := Finset.card_eq_two.1 hcard
  have hmem : ∀ a, a ∈ hf.s.M.atoms ∧ ¬ Even (hf.s.M.deg a) ↔ a = u ∨ a = x := by
    intro a
    have := congrArg (fun S => a ∈ S) hset
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, eq_iff_iff] at this
    exact this
  have hbux := (hmem b).1 ⟨hb'.1, hbo⟩
  have hu := (hmem u).2 (Or.inl rfl)
  have hx := (hmem x).2 (Or.inr rfl)
  have hcomp : hf.s.M.SameComponent u x := hC.struct.odd_comp hR u hu.1 x hx.1 hu.2 hx.2
  have hbu : hf.s.M.SameComponent a₀ u ∧ hf.s.M.SameComponent a₀ x := by
    rcases hbux with rfl | rfl
    · exact ⟨hb'.2, Relation.EqvGen.trans _ _ _ hb'.2 hcomp⟩
    · exact ⟨Relation.EqvGen.trans _ _ _ hb'.2 (Relation.EqvGen.symm _ _ hcomp), hb'.2⟩
  refine ⟨u, (mem_compMol _ _).2 ⟨hu.1, hbu.1⟩, x, (mem_compMol _ _).2 ⟨hx.1, hbu.2⟩, hux, ?_, ?_, ?_⟩
  · rw [compMol_deg _ _ hbu.1]; exact hC.struct.odd_deg u hu.1 hu.2
  · rw [compMol_deg _ _ hbu.2]; exact hC.struct.odd_deg x hx.1 hx.2
  · intro a ha hau hax
    have h := (mem_compMol _ _).1 ha
    rw [compMol_deg _ _ h.2]
    have hev : Even (hf.s.M.deg a) := by
      by_contra hc
      rcases (hmem a).1 ⟨h.1, hc⟩ with e | e
      · exact hau e
      · exact hax e
    have hr := hC.struct.deg_range a h.1
    obtain ⟨k, hk⟩ := hev
    omega

theorem shape_evenBeta : ¬ CompOdd hf a₀ → ∃ a ∈ (compMol hf.s.M a₀).atoms, (toCls (hf.s.cls a)).IsBeta := by
  intro hn
  obtain ⟨b, hb, hsc, hcb⟩ := hC.struct.even_beta a₀ ha₀ (by
    intro b hb hsc
    have hm : b ∈ (compMol hf.s.M a₀).atoms := (mem_compMol _ _).2 ⟨hb, hsc⟩
    by_contra hc
    exact hn ⟨b, hm, by rwa [compMol_deg _ _ hsc]⟩)
  exact ⟨b, (mem_compMol _ _).2 ⟨hb, hsc⟩, by rw [toCls_isBeta]; exact Or.inl hcb⟩

end shape2

end WaveTurbulence.FinalCountG3
