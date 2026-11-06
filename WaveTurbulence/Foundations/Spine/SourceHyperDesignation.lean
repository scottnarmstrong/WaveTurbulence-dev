/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceHyperUnion
public import WaveTurbulence.Foundations.Spine.SourceDVExit
import Mathlib.Tactic
/-! Two hyper-block designations of the same atom set, where the set contains an ordinary block
`Pa` at one joint `a` missing the other joint `b`, use the same deleted bond up to mates. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem hyper_designation_eq {X Pa : Finset V} {a b c1 c2 c : V} (e e' : D)
    (he : M.ends e = s(a, b)) (hB : (Mole.eraseBond M e).IsBlock X a b)
    (he' : M.ends e' = s(c1, c2)) (hB' : (Mole.eraseBond M e').IsBlock X c1 c2)
    (hPB : M.IsBlock Pa a c) (hPX : Pa ⊆ X) (hbP : b ∉ Pa) : e = e' ∨ e = M.mate e' := by
  have hd := Mole.hyperBlock_degrees M ⟨e, he, hB⟩
  have hd' := Mole.hyperBlock_degrees M ⟨e', he', hB'⟩
  have haX : a ∈ X := hB.2.1
  have hbX : b ∈ X := hB.2.2.1
  have hab : a ≠ b := hB.2.2.2.1
  have hac : a ∈ ({c1, c2} : Finset V) := by
    by_contra h
    simp only [mem_insert, mem_singleton, not_or] at h
    have := hd'.2.2 a haX h.1 h.2
    omega
  have hbc : b ∈ ({c1, c2} : Finset V) := by
    by_contra h
    simp only [mem_insert, mem_singleton, not_or] at h
    have := hd'.2.2 b hbX h.1 h.2
    omega
  have hends : M.ends e' = s(a, b) := by
    rw [he']
    simp only [mem_insert, mem_singleton] at hac hbc
    rcases hac with rfl | rfl
    · rcases hbc with rfl | rfl
      · exact absurd rfl hab
      · rfl
    · rcases hbc with rfl | rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hab
  -- the darts of e and e' at a
  have key : ∀ f : D, M.ends f = s(a, b) → ∃ g : D, (g = f ∨ g = M.mate f) ∧ M.atom g = a ∧
      M.atom (M.mate g) = b := by
    intro f hf
    rcases Sym2.eq_iff.mp hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨f, Or.inl rfl, h1, h2⟩
    · exact ⟨M.mate f, Or.inr rfl, h2, by rw [M.mate_mate]; exact h1⟩
  obtain ⟨d, hdf, hda, hdb⟩ := key e he
  obtain ⟨d', hdf', hda', hdb'⟩ := key e' hends
  have hdd : d = d' := by
    by_contra hne
    have hZ : M.atoms ⊇ X := by
      intro x hx; exact hB.1 hx
    have hsub : (M.dartsAt a).filter (M.InGroup Pa) ∪ {d, d'} ⊆
        (M.dartsAt a).filter (M.InGroup X) := by
      intro t ht
      rcases Finset.mem_union.mp ht with h | h
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
        exact Finset.mem_filter.mpr ⟨h1, ⟨hPX h2.1, hPX h2.2⟩⟩
      · rcases Finset.mem_insert.mp h with rfl | h
        · exact Finset.mem_filter.mpr ⟨(Mole.mem_dartsAt M a _).mpr hda, hda ▸ haX, hdb ▸ hbX⟩
        · rw [Finset.mem_singleton.mp h]
          exact Finset.mem_filter.mpr ⟨(Mole.mem_dartsAt M a _).mpr hda', hda' ▸ haX, hdb' ▸ hbX⟩
    have hdis : Disjoint ((M.dartsAt a).filter (M.InGroup Pa)) {d, d'} := by
      rw [Finset.disjoint_left]
      intro t ht ht'
      have h2 := (Finset.mem_filter.mp ht).2.2
      rcases Finset.mem_insert.mp ht' with rfl | h
      · exact hbP (hdb ▸ h2)
      · rw [Finset.mem_singleton.mp h] at h2; exact hbP (hdb' ▸ h2)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis, Finset.card_pair hne] at hc
    have h2 : M.degIn Pa a = ((M.dartsAt a).filter (M.InGroup Pa)).card := rfl
    have h3 : M.degIn X a = ((M.dartsAt a).filter (M.InGroup X)).card := rfl
    have h4 := (Mole.block_joint_degrees M hPB).1
    omega
  subst hdd
  rcases hdf with h | h <;> rcases hdf' with h' | h'
  · exact Or.inl (h.symm.trans h')
  · exact Or.inr (h.symm.trans h')
  · right
    have := congrArg M.mate (h.symm.trans h')
    rwa [M.mate_mate] at this
  · left
    have := congrArg M.mate (h.symm.trans h')
    simpa [M.mate_mate] using this

end WaveTurbulence.LGSpine
