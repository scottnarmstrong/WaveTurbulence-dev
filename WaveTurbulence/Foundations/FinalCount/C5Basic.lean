/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.ChainOrient
public import WaveTurbulence.Foundations.FinalCount.Case23_96
public import WaveTurbulence.Foundations.FinalCount.G8R.Prop104One
import Mathlib.Tactic

/-! # Prop 9.6, case (5): structure of `M₀` with `V_α = V_β = 1` -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem cls_nonEps_cases {c : Cls} (h : ¬ c.IsEps) : c.IsAlpha ∨ c.IsBeta := by
  cases c <;> simp_all [Cls.IsAlpha, Cls.IsBeta, Cls.IsEps]

/-- The atoms of an even component with `V_α = V_β = 1`. -/
theorem c5_atoms {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd) (hnodd : ¬ odd)
    (ha : (alphaAtoms M.atoms cls).card = 1) (hb : (betaAtoms M.atoms cls).card = 1) :
    ∃ a₀ b₀, a₀ ∈ M.atoms ∧ b₀ ∈ M.atoms ∧ (cls a₀).IsAlpha ∧ (cls b₀).IsBeta ∧ a₀ ≠ b₀ ∧
      (∀ v ∈ M.atoms, ¬ (cls v).IsEps ↔ (v = a₀ ∨ v = b₀)) ∧ M.deg a₀ = 2 ∧ M.deg b₀ = 2 ∧
      (∀ v ∈ M.atoms, v ≠ a₀ → v ≠ b₀ → M.deg v = 4) := by
  classical
  obtain ⟨a₀, ha0⟩ := card_eq_one.mp ha
  obtain ⟨b₀, hb0⟩ := card_eq_one.mp hb
  have haA : a₀ ∈ alphaAtoms M.atoms cls := by rw [ha0]; exact mem_singleton_self _
  have hbB : b₀ ∈ betaAtoms M.atoms cls := by rw [hb0]; exact mem_singleton_self _
  obtain ⟨ha1, ha2⟩ := mem_filter.mp haA
  obtain ⟨hb1, hb2⟩ := mem_filter.mp hbB
  have hne : a₀ ≠ b₀ := by
    rintro rfl
    cases hc : cls a₀ <;> simp_all [Cls.IsAlpha, Cls.IsBeta]
  have hchar : ∀ v ∈ M.atoms, ¬ (cls v).IsEps ↔ (v = a₀ ∨ v = b₀) := by
    intro v hv
    constructor
    · intro hn
      rcases cls_nonEps_cases hn with h | h
      · left
        have : v ∈ alphaAtoms M.atoms cls := mem_filter.mpr ⟨hv, h⟩
        rw [ha0] at this; exact mem_singleton.mp this
      · right
        have : v ∈ betaAtoms M.atoms cls := mem_filter.mpr ⟨hv, h⟩
        rw [hb0] at this; exact mem_singleton.mp this
    · rintro (rfl | rfl)
      · exact alpha_not_eps ha2
      · exact beta_not_eps hb2
  have hd2 : ∀ v ∈ M.atoms, ¬ (cls v).IsEps → M.deg v = 2 := by
    intro v hv hn
    have := (hS.classes v hv).mpr hn
    rcases hS.evenDeg hnodd v hv with h | h <;> omega
  refine ⟨a₀, b₀, ha1, hb1, ha2, hb2, hne, hchar, hd2 a₀ ha1 (alpha_not_eps ha2), hd2 b₀ hb1 (beta_not_eps hb2), ?_⟩
  intro v hv h1 h2
  have hn : (cls v).IsEps := by
    by_contra hn
    rcases (hchar v hv).mp hn with h | h
    · exact h1 h
    · exact h2 h
  have : ¬ M.deg v ≤ 2 := fun h => ((hS.classes v hv).mp h) hn
  rcases hS.evenDeg hnodd v hv with h | h <;> omega

/-- `2 · bonds = 4V - 4`. -/
theorem c5_two_bonds {M : Molecule V D} {a₀ b₀ : V} (ha : a₀ ∈ M.atoms) (hb : b₀ ∈ M.atoms) (hne : a₀ ≠ b₀)
    (h1 : M.deg a₀ = 2) (h2 : M.deg b₀ = 2) (h4 : ∀ v ∈ M.atoms, v ≠ a₀ → v ≠ b₀ → M.deg v = 4) :
    2 * M.bonds.card + 4 = 4 * M.atoms.card := by
  have hs := Mole.sum_degrees_eq_two_mul_bonds M
  have hsub : ({a₀, b₀} : Finset V) ⊆ M.atoms := by
    intro v hv; rcases mem_insert.mp hv with rfl | h
    · exact ha
    · rw [mem_singleton.mp h]; exact hb
  rw [← sum_sdiff hsub] at hs
  have e1 : ∑ v ∈ M.atoms \ {a₀, b₀}, M.deg v = 4 * (M.atoms.card - 2) := by
    rw [sum_congr rfl (fun v hv => h4 v (mem_sdiff.mp hv).1 (fun h => (mem_sdiff.mp hv).2 (by simp [h]))
      (fun h => (mem_sdiff.mp hv).2 (by simp [h])))]
    rw [sum_const, card_sdiff_of_subset hsub, card_pair hne, smul_eq_mul]; ring
  rw [e1, sum_pair hne, h1, h2] at hs
  have : 2 ≤ M.atoms.card := by
    have := card_le_card hsub; rw [card_pair hne] at this; exact this
  omega


/-- A balanced two-exit set is a `TwoExit` structure. -/
theorem twoExit_of_chain (M : Molecule V D) {K : Finset V} {y₁ y₂ : D} (hK : K ⊆ M.atoms)
    (hbal : ∀ v ∈ K, M.outdeg v = M.indeg v) (hcross : crossDarts M K = {y₁, y₂}) (hne : y₁ ≠ y₂)
    (hfar : M.atom (M.mate y₁) ≠ M.atom (M.mate y₂)) :
    ∃ T : TwoExit M, T.Y = K ∧ ((T.x = y₁ ∧ T.y = y₂) ∨ (T.x = y₂ ∧ T.y = y₁)) := by
  have hopp := chain_cross_opposite M K hbal hne hcross
  by_cases h1 : M.out y₁ = true
  · have h2 : M.out y₂ = false := by
      cases h : M.out y₂ <;> simp_all
    exact ⟨⟨K, hK, y₁, y₂, hcross, hne, hfar, h1, h2⟩, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · have h1' : M.out y₁ = false := by simpa using h1
    have h2 : M.out y₂ = true := by
      cases h : M.out y₂ <;> simp_all
    refine ⟨⟨K, hK, y₂, y₁, ?_, hne.symm, hfar.symm, h2, h1'⟩, rfl, Or.inr ⟨rfl, rfl⟩⟩
    rw [hcross]; exact pair_comm _ _

/-- Bond count after erasing a chain of degree-two atoms. -/
theorem erase_chain_bonds (M : Molecule V D) (T : TwoExit M) (hdeg : ∀ v ∈ T.Y, M.deg v = 2) :
    (Degen.eraseAtoms M T.Y).bonds.card + T.Y.card + 1 = M.bonds.card := by
  have h1 := two_mul_piece_bonds M T.sub
  rw [T.cross, card_pair T.ne, sum_congr rfl hdeg, sum_const, smul_eq_mul] at h1
  have h2 := T.bonds_eq
  omega

end
end WaveTurbulence.FinalCountG8
