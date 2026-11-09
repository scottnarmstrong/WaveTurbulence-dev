/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DeriveClass

/-!
# Derivation of the cell decomposition, IV: ports

A **port** is the set of bonds crossing a region `X ⊆ S` (`portSet X`). In a block of a molecule every port has an
even number of bonds (N1 Lemma D, balance). A port with exactly two bonds has one bond leaving `X` and one entering
(`lemmaD_oneInOneOut`), and, in a T-vine, their interior ends are distinct (M4 Lemma A, `AttachInput`).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract Struct

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V}

/-- The bonds crossing `X`. -/
noncomputable def portSet (X : Finset V) : Finset (Bond M S) := by
  classical
  exact univ.filter fun e => Crosses X e

theorem mem_portSet {X : Finset V} {e : Bond M S} : e ∈ portSet X ↔ Crosses X e := by
  classical
  unfold portSet; simp

theorem crossSign_cases {X : Finset V} (e : Bond M S) :
    (Crosses X e ∧ (crossSign X e = 1 ∨ crossSign X e = -1)) ∨ (¬ Crosses X e ∧ crossSign X e = 0) := by
  unfold Crosses crossSign
  by_cases h1 : tl e ∈ X <;> by_cases h2 : hd e ∈ X <;> simp [h1, h2]

/-- **Ports are even** (balance). -/
theorem portSet_even (hM : M.IsMolecule) (hB : M.IsBlock S a b) {X : Finset V} (hX : X ⊆ S) :
    Even (portSet (M := M) (S := S) X).card := by
  classical
  have hs := sum_crossSign hM hB hX
  have hsplit : (∑ e : Bond M S, crossSign X e) =
      ((univ.filter fun e : Bond M S => crossSign X e = 1).card : ℤ) -
        (univ.filter fun e : Bond M S => crossSign X e = -1).card := by
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rcases crossSign_cases (X := X) e with ⟨-, h | h⟩ | ⟨-, h⟩ <;> simp [h]
  have hp : portSet (M := M) (S := S) X =
      (univ.filter fun e : Bond M S => crossSign X e = 1) ∪ (univ.filter fun e : Bond M S => crossSign X e = -1) := by
    ext e
    simp only [mem_portSet, mem_union, mem_filter, mem_univ, true_and]
    rcases crossSign_cases (X := X) e with ⟨h1, h | h⟩ | ⟨h1, h⟩ <;> simp [h1, h]
  rw [hp, card_union_of_disjoint]
  · refine ⟨(univ.filter fun e : Bond M S => crossSign X e = 1).card, ?_⟩
    omega
  · rw [Finset.disjoint_filter]; intro e _ h1 h2; rw [h1] at h2; norm_num at h2

/-- A two-bond port: the two bonds, one leaving and one entering, with distinct interior ends. -/
structure Port2 (M : Molecule V D) (S X : Finset V) (a b : V) where
  out : Bond M S
  inn : Bond M S
  ne : out ≠ inn
  set_eq : portSet X = {out, inn}
  out_tl : tl out ∈ X
  out_hd : hd out ∉ X
  inn_hd : hd inn ∈ X
  inn_tl : tl inn ∉ X
  distinct : ∀ w, w ≠ a → w ≠ b → ¬ ((tl out = w ∨ hd out = w) ∧ (tl inn = w ∨ hd inn = w))

theorem crossesIn_iff {X : Finset V} (e : Bond M S) : CrossesIn M S X e.1 ↔ Crosses X e := by
  unfold CrossesIn Crosses
  have hS := (bond_spec e).2
  simp only [hS, true_and]
  change (tl e ∈ X ↔ hd e ∉ X) ↔ _
  by_cases h1 : tl e ∈ X <;> by_cases h2 : hd e ∈ X <;> simp [h1, h2]

/-- **A two-bond port** of a T-vine (Lemma D and Lemma A). -/
theorem port2_of (hM : M.IsMolecule) (hT : M.IsTVine S a b) (hA : AttachInput) {X : Finset V} (hX : X ⊆ S)
    (hc : (portSet (M := M) (S := S) X).card = 2) : Nonempty (Port2 M S X a b) := by
  classical
  have hB := hT.1
  obtain ⟨e, f, hef, hset⟩ := Finset.card_eq_two.mp hc
  have hcut : ∀ g, Crosses X g ↔ g = e ∨ g = f := by
    intro g; rw [← mem_portSet, hset]; simp
  have hio := lemmaD_oneInOneOut hM hB hX hef hcut
  have hdist : ∀ w, w ≠ a → w ≠ b → ¬ ((tl e = w ∨ hd e = w) ∧ (tl f = w ∨ hd f = w)) := by
    intro w hwa hwb
    have hbe : e.1 ∈ M.bonds := by simp [Molecule.bonds, (bond_spec e).1]
    have hbf : f.1 ∈ M.bonds := by simp [Molecule.bonds, (bond_spec f).1]
    have := hA M S a b hT X hX e.1 hbe f.1 hbf (fun h => hef (Subtype.ext h))
      ((crossesIn_iff e).mpr ((hcut e).mpr (Or.inl rfl))) ((crossesIn_iff f).mpr ((hcut f).mpr (Or.inr rfl)))
      (by
        intro g hg hcg
        have hgS : M.InGroup S g := hcg.1
        have hgo : M.out g = true := by simpa [Molecule.bonds] using hg
        let g' : Bond M S := ⟨g, mem_internalBondSet hgo hgS⟩
        rcases (hcut g').mp ((crossesIn_iff g').mp hcg) with h | h
        · left; exact congrArg Subtype.val h
        · right; exact congrArg Subtype.val h) w hwa hwb
    simp only [Molecule.ends, Sym2.mem_iff] at this
    rintro ⟨h1, h2⟩
    exact this ⟨by rcases h1 with h | h <;> [left; right] <;> exact h.symm,
      by rcases h2 with h | h <;> [left; right] <;> exact h.symm⟩
  rcases hio with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact ⟨⟨e, f, hef, hset, h1, h2, h3, h4, hdist⟩⟩
  · refine ⟨⟨f, e, hef.symm, by rw [hset, Finset.pair_comm], h3, h4, h1, h2, fun w hwa hwb h => ?_⟩⟩
    exact hdist w hwa hwb ⟨h.2, h.1⟩

end WaveTurbulence.TVine.Chart
