/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineSigmaExpansion
public import WaveTurbulence.Foundations.WaveB.Molecules
/-! The number of bonds between the joints of an actual vine is the template sigma:
`2` for type I, `1` for type V, `0` otherwise. -/
public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.LGSpine
open Finset WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem bondsBetween_eq_count_groupBonds {M : Molecule V D} {S : Finset V} {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) :
    M.bondsBetween a b = Multiset.count s(a, b) (M.groupBonds S) := by
  unfold Molecule.bondsBetween Molecule.groupBonds Molecule.bonds
  rw [Multiset.count_map, Finset.filter_filter]
  have : ((Finset.univ.filter fun x => M.out x = true ∧ M.ends x = s(a, b))) =
      Finset.univ.filter fun x => M.out x = true ∧ M.InGroup S x ∧ s(a, b) = M.ends x := by
    ext x
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      have hin : M.InGroup S x := by
        have : M.atom x = a ∧ M.atom (M.mate x) = b ∨ M.atom x = b ∧ M.atom (M.mate x) = a := by
          have := h2; unfold Molecule.ends at this; simpa using this
        rcases this with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact ⟨h3 ▸ ha, h4 ▸ hb⟩
        · exact ⟨h3 ▸ hb, h4 ▸ ha⟩
      exact ⟨h1, hin, h2.symm⟩
    · rintro ⟨h1, _, h3⟩
      exact ⟨h1, h3.symm⟩
  rw [this, ← Finset.filter_val, Finset.filter_filter, Finset.card_def]
  simp only [and_assoc]


theorem isVine_bondsBetween {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (h : M.IsVine X S a b) :
    M.bondsBetween a b = (match X with | .I => 2 | .V => 1 | _ => 0) := by
  obtain ⟨hB, k, hk, f, hf, himg, hj, he⟩ := h
  rw [bondsBetween_eq_count_groupBonds hB.2.1 hB.2.2.1]
  have hf01 : s(f a, f b) = s(0, 1) := by
    have h0 : (0 : ℕ) ∈ ({f a, f b} : Finset ℕ) := by rw [hj]; simp
    have h1 : (1 : ℕ) ∈ ({f a, f b} : Finset ℕ) := by rw [hj]; simp
    simp only [mem_insert, mem_singleton] at h0 h1
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · omega
    · rw [← h0, ← h1]
    · rw [← h0, ← h1]; exact Sym2.eq_swap
    · omega
  have h1 : Multiset.count s(a, b) (M.groupBonds S) =
      Multiset.count s(f a, f b) ((M.groupBonds S).map (Sym2.map f)) := by
    rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
    congr 1
    apply Multiset.filter_congr
    intro e he'
    unfold Molecule.groupBonds at he'
    simp only [Multiset.mem_map, Finset.mem_val, mem_filter, mem_univ, true_and] at he'
    obtain ⟨x, ⟨_, hx⟩, rfl⟩ := he'
    simp only [Molecule.ends, Sym2.map_mk]
    constructor
    · intro hh; have := congrArg (Sym2.map f) hh; simpa using this
    · intro hh
      have := (Sym2.eq_iff.mp hh)
      rcases this with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [hf.eq_iff hB.2.1 hx.1] at h3
        rw [hf.eq_iff hB.2.2.1 hx.2] at h4
        rw [h3, h4]
      · rw [hf.eq_iff hB.2.1 hx.2] at h3
        rw [hf.eq_iff hB.2.2.1 hx.1] at h4
        rw [h3, h4]; exact Sym2.eq_swap
  have h5 : Multiset.count s(a, b) (M.groupBonds S) = Multiset.count s((0 : ℕ), (1 : ℕ))
      (((X.expand k).bonds.map fun p => s(p.1, p.2) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) := by
    rw [h1, he, hf01]
  have h2 := Vine.expand_sigma X k hk
  have h6 : Multiset.count s((0 : ℕ), (1 : ℕ))
      (((X.expand k).bonds.map fun p => s(p.1, p.2) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) =
      Vine.templateSigma (X.expand k) := by
    unfold Vine.templateSigma
    rw [Multiset.coe_count, List.count_eq_countP, List.countP_map]
    apply List.countP_congr
    intro p _
    simp only [Function.comp, Vine.isJointBond, beq_iff_eq, decide_eq_true_eq, Sym2.eq_iff]
    obtain ⟨p1, p2⟩ := p
    simp
  rw [h5, h6]
  exact h2.trans (by cases X <;> rfl)

end WaveTurbulence.LGSpine
