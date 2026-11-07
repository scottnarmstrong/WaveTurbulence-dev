/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C5Basic
public import WaveTurbulence.Foundations.FinalCount.C4Close
public import WaveTurbulence.Foundations.FinalCount.Cycle96
import Mathlib.Tactic

/-! # Prop 9.6, case (4): the chain data of a component with `V_α = 0`, `V_β = 2`

The two `β`-atoms `b, b′` lie on chains with distinct `ε`-atoms at their ends (`FinalShape.chains`); either `b, b′` are
adjacent (one chain `{b, b′}`) or not (two chains `{b}`, `{b′}`).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The data of two separate `β`-chains `u → b → v`, `u′ → b′ → v′` (orientations normalised). -/
structure Case4TwoData (M : Molecule V D) (cls : V → Cls) (b b' : V) (y₁ y₂ y₃ y₄ : D) : Prop where
  hb : b ∈ M.atoms
  hb' : b' ∈ M.atoms
  hbb' : b ≠ b'
  hnb : ¬ (cls b).IsEps
  hnb' : ¬ (cls b').IsEps
  hbeta : (cls b).IsBeta
  hbeta' : (cls b').IsBeta
  heps : ∀ v ∈ M.atoms, v ≠ b → v ≠ b' → (cls v).IsEps
  hdeg2 : M.deg b = 2
  hdeg2' : M.deg b' = 2
  hdeg4 : ∀ v ∈ M.atoms, v ≠ b → v ≠ b' → M.deg v = 4
  hnadj : ¬ M.Adj b b'
  hKb : IsChainSet M cls {b}
  hKb' : IsChainSet M cls {b'}
  hc1 : crossDarts M {b} = {y₁, y₂}
  hc2 : crossDarts M {b'} = {y₃, y₄}
  ho1 : M.out y₁ = false
  ho2 : M.out y₂ = true
  ho3 : M.out y₃ = false
  ho4 : M.out y₄ = true
  hfar1 : M.atom (M.mate y₁) ≠ M.atom (M.mate y₂)
  hfar2 : M.atom (M.mate y₃) ≠ M.atom (M.mate y₄)
  hendsE : ∀ y ∈ ({y₁, y₂, y₃, y₄} : Finset D), (cls (M.atom (M.mate y))).IsEps

/-- The data of one `β`-chain `u → b → b′ → v`. -/
structure Case4OneData (M : Molecule V D) (cls : V → Cls) (b b' : V) (x₁ x₂ y y' : D) : Prop where
  hb : b ∈ M.atoms
  hb' : b' ∈ M.atoms
  hbb' : b ≠ b'
  hnb : ¬ (cls b).IsEps
  hnb' : ¬ (cls b').IsEps
  hbeta : (cls b).IsBeta
  hbeta' : (cls b').IsBeta
  heps : ∀ v ∈ M.atoms, v ≠ b → v ≠ b' → (cls v).IsEps
  hdeg2 : M.deg b = 2
  hdeg2' : M.deg b' = 2
  hdeg4 : ∀ v ∈ M.atoms, v ≠ b → v ≠ b' → M.deg v = 4
  hadj : M.Adj b b'
  hK : IsChainSet M cls {b, b'}
  hc : crossDarts M {b, b'} = {x₁, x₂}
  hne : x₁ ≠ x₂
  ho1 : M.out x₁ = false
  ho2 : M.out x₂ = true
  hfar : M.atom (M.mate x₁) ≠ M.atom (M.mate x₂)
  hendsE : (cls (M.atom (M.mate x₁))).IsEps ∧ (cls (M.atom (M.mate x₂))).IsEps
  hyb : M.atom y = b
  hyb' : M.atom y' = b
  hyy' : y ≠ y'

theorem c4_atoms {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd) (hnodd : ¬ odd)
    (ha : (alphaAtoms M.atoms cls).card = 0) (hb : (betaAtoms M.atoms cls).card = 2) :
    ∃ b b', b ∈ M.atoms ∧ b' ∈ M.atoms ∧ b ≠ b' ∧ (cls b).IsBeta ∧ (cls b').IsBeta ∧
      (∀ v ∈ M.atoms, v ≠ b → v ≠ b' → (cls v).IsEps) ∧ M.deg b = 2 ∧ M.deg b' = 2 ∧
      (∀ v ∈ M.atoms, v ≠ b → v ≠ b' → M.deg v = 4) := by
  classical
  obtain ⟨b, b', hne, hset⟩ := card_eq_two.mp hb
  have hbB : b ∈ betaAtoms M.atoms cls := by rw [hset]; simp
  have hb'B : b' ∈ betaAtoms M.atoms cls := by rw [hset]; simp
  obtain ⟨hb1, hb2⟩ := mem_filter.mp hbB
  obtain ⟨hb1', hb2'⟩ := mem_filter.mp hb'B
  have hα : ∀ v ∈ M.atoms, ¬ (cls v).IsAlpha := by
    intro v hv hα
    have : v ∈ alphaAtoms M.atoms cls := mem_filter.mpr ⟨hv, hα⟩
    rw [card_eq_zero.mp ha] at this; simp at this
  have hchar : ∀ v ∈ M.atoms, v ≠ b → v ≠ b' → (cls v).IsEps := by
    intro v hv h1 h2
    by_contra hn
    rcases cls_nonEps_cases hn with h | h
    · exact hα v hv h
    · have : v ∈ betaAtoms M.atoms cls := mem_filter.mpr ⟨hv, h⟩
      rw [hset] at this; simp at this
      rcases this with h | h
      · exact h1 h
      · exact h2 h
  have hd2 : ∀ v ∈ M.atoms, ¬ (cls v).IsEps → M.deg v = 2 := by
    intro v hv hn
    have := (hS.classes v hv).mpr hn
    rcases hS.evenDeg hnodd v hv with h | h <;> omega
  refine ⟨b, b', hb1, hb1', hne, hb2, hb2', hchar, hd2 b hb1 (beta_not_eps hb2), hd2 b' hb1' (beta_not_eps hb2'), ?_⟩
  intro v hv h1 h2
  have hn : (cls v).IsEps := hchar v hv h1 h2
  have : ¬ M.deg v ≤ 2 := fun h => ((hS.classes v hv).mp h) hn
  rcases hS.evenDeg hnodd v hv with h | h <;> omega

theorem orient {M : Molecule V D} {K : Finset V} {p q : D} (hc : crossDarts M K = {p, q}) (hne : M.out p ≠ M.out q) :
    ∃ y₁ y₂, crossDarts M K = {y₁, y₂} ∧ M.out y₁ = false ∧ M.out y₂ = true ∧
      ((y₁ = p ∧ y₂ = q) ∨ (y₁ = q ∧ y₂ = p)) := by
  cases hp : M.out p
  · have hq : M.out q = true := by cases h : M.out q <;> simp_all
    exact ⟨p, q, hc, hp, hq, Or.inl ⟨rfl, rfl⟩⟩
  · have hq : M.out q = false := by cases h : M.out q <;> simp_all
    exact ⟨q, p, by rw [hc]; exact pair_comm _ _, hq, hp, Or.inr ⟨rfl, rfl⟩⟩

theorem c4_data {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd) (hnodd : ¬ odd)
    (hnc : ¬ ∀ a ∈ M.atoms, M.deg a = 2) (ha : (alphaAtoms M.atoms cls).card = 0)
    (hb : (betaAtoms M.atoms cls).card = 2) :
    (∃ b b' y₁ y₂ y₃ y₄, Case4TwoData M cls b b' y₁ y₂ y₃ y₄) ∨
      (∃ b b' x₁ x₂ y y', Case4OneData M cls b b' x₁ x₂ y y') := by
  classical
  obtain ⟨b, b', hb1, hb1', hbb', hβ, hβ', heps, hd2, hd2', hd4⟩ := c4_atoms hS hnodd ha hb
  have hbal := shape_balanced hS hnodd
  have hnb : ¬ (cls b).IsEps := beta_not_eps hβ
  have hnb' : ¬ (cls b').IsEps := beta_not_eps hβ'
  have hnE : ∀ v ∈ M.atoms, ¬ (cls v).IsEps → v = b ∨ v = b' := by
    intro v hv hn
    by_contra h; push Not at h
    exact hn (heps v hv h.1 h.2)
  have hadjmem : ∀ u v, M.Adj u v → v ∈ M.atoms := by
    rintro u v ⟨x, _, rfl⟩; exact M.atom_mem _
  by_cases hadj : M.Adj b b'
  · right
    have hK : IsChainSet M cls {b, b'} := by
      refine ⟨⟨b, by simp⟩, ?_, ?_, ?_, ?_⟩
      · intro v hv; rcases mem_insert.mp hv with rfl | h
        · exact hb1
        · rw [mem_singleton.mp h]; exact hb1'
      · intro v hv; rcases mem_insert.mp hv with rfl | h
        · exact hnb
        · rw [mem_singleton.mp h]; exact hnb'
      · intro u hu v huv hvn
        have := hnE v (hadjmem u v huv) hvn
        simpa using this
      · intro u hu v hv
        have hu' : u = b ∨ u = b' := by simpa using hu
        have hv' : v = b ∨ v = b' := by simpa using hv
        rcases hu' with h1 | h1 <;> rcases hv' with h2 | h2 <;> rw [h1, h2]
        · exact Relation.EqvGen.refl _
        · exact Relation.EqvGen.rel _ _ ⟨by simp, by simp, hadj⟩
        · exact Relation.EqvGen.rel _ _ ⟨by simp, by simp, Mole.adj_symmetric M hadj⟩
        · exact Relation.EqvGen.refl _
    obtain ⟨p, q, hcross, hpq, hep, heq, hne⟩ := hS.chains hnodd hnc _ hK
    have hbalK : ∀ v ∈ ({b, b'} : Finset V), M.outdeg v = M.indeg v := fun v hv => by
      rcases mem_insert.mp hv with rfl | h
      · exact hbal _ hb1
      · rw [mem_singleton.mp h]; exact hbal _ hb1'
    have hopp := chain_cross_opposite M _ hbalK hpq hcross
    obtain ⟨x₁, x₂, hc, ho1, ho2, hpm⟩ := orient hcross hopp
    obtain ⟨y, y', hy, hy', hyy'⟩ := exists_two_darts M hd2
    refine ⟨b, b', x₁, x₂, y, y', ⟨hb1, hb1', hbb', hnb, hnb', hβ, hβ', heps, hd2, hd2', hd4, hadj, hK, hc, ?_, ho1, ho2, ?_, ?_, hy, hy', hyy'⟩⟩
    · intro h; rw [h] at ho1; rw [ho1] at ho2; exact Bool.noConfusion ho2
    · rcases hpm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne
      · exact hne.symm
    · rcases hpm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hep, heq⟩
      · exact ⟨heq, hep⟩
  · left
    have hKb : IsChainSet M cls {b} := by
      refine ⟨⟨b, by simp⟩, by simpa using hb1, by simpa using hnb, ?_, ?_⟩
      · intro u hu v huv hvn
        have hu' := mem_singleton.mp hu
        have := hnE v (hadjmem u v huv) hvn
        rcases this with rfl | rfl
        · simp
        · exact absurd (hu' ▸ huv) hadj
      · intro u hu v hv
        rw [mem_singleton.mp hu, mem_singleton.mp hv]; exact Relation.EqvGen.refl _
    have hKb' : IsChainSet M cls {b'} := by
      refine ⟨⟨b', by simp⟩, by simpa using hb1', by simpa using hnb', ?_, ?_⟩
      · intro u hu v huv hvn
        have hu' := mem_singleton.mp hu
        have := hnE v (hadjmem u v huv) hvn
        rcases this with rfl | rfl
        · exact absurd (hu' ▸ Mole.adj_symmetric M huv) hadj
        · simp
      · intro u hu v hv
        rw [mem_singleton.mp hu, mem_singleton.mp hv]; exact Relation.EqvGen.refl _
    obtain ⟨p, q, hcross, hpq, hep, heq, hne⟩ := hS.chains hnodd hnc _ hKb
    obtain ⟨p', q', hcross', hpq', hep', heq', hne'⟩ := hS.chains hnodd hnc _ hKb'
    have hbalb : ∀ v ∈ ({b} : Finset V), M.outdeg v = M.indeg v := fun v hv => by
      rw [mem_singleton.mp hv]; exact hbal _ hb1
    have hbalb' : ∀ v ∈ ({b'} : Finset V), M.outdeg v = M.indeg v := fun v hv => by
      rw [mem_singleton.mp hv]; exact hbal _ hb1'
    obtain ⟨y₁, y₂, hc1, ho1, ho2, hpm⟩ := orient hcross (chain_cross_opposite M _ hbalb hpq hcross)
    obtain ⟨y₃, y₄, hc2, ho3, ho4, hpm'⟩ := orient hcross' (chain_cross_opposite M _ hbalb' hpq' hcross')
    refine ⟨b, b', y₁, y₂, y₃, y₄, ⟨hb1, hb1', hbb', hnb, hnb', hβ, hβ', heps, hd2, hd2', hd4, hadj, hKb, hKb', hc1, hc2, ho1, ho2, ho3, ho4, ?_, ?_, ?_⟩⟩
    · rcases hpm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne
      · exact hne.symm
    · rcases hpm' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne'
      · exact hne'.symm
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · rcases hpm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      · rcases hpm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      · rcases hpm' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      · rcases hpm' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption

end
end WaveTurbulence.FinalCountG8
