/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreCaseB
import Mathlib.Tactic

/-! # Graph facts for core case II (bi-bridge)

A bi-bridge of a core `𝕄` is a side `S` with exactly two crossing darts. If `𝕄 ∖ ℓ` has no bridge, `ℓ` does not
cross a bi-bridge, so some side contains both ends of `ℓ`; we take such a side `S` with the fewest atoms. Then:
* the crossing darts `x₁, x₂` have opposite directions (flow balance) and distinct atoms `a₁ ≠ a₂` (no cut vertex);
* **`a₁, a₂` are not doubly bonded in `𝕄 ∖ ℓ`** (minimality): otherwise `S ∖ {a₁, a₂}` is a smaller side with two
  crossing darts, or `ℓ` crosses it and `𝕄 ∖ ℓ` has a bridge. So re-inserting `a₁ → a₂` creates no triple bond, and
  Prop 10.2 applies to `S` with the new bond. (This replaces DH23's use of Prop 10.4(1) at L1969.)
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **A minimal bi-bridge side through `ℓ`.** -/
theorem exists_min_bibridge {M : Molecule V D} (e : D)
    (hnoB : ∀ S ⊆ M.atoms, (crossDarts (MoleProp.eraseBond M e) S).card ≠ 1)
    (hII : ∃ S ⊆ M.atoms, ∃ a ∈ S, ∃ b ∈ M.atoms, b ∉ S ∧ (crossDarts M S).card = 2) :
    ∃ S ⊆ M.atoms, M.atom e ∈ S ∧ M.atom (M.mate e) ∈ S ∧ (crossDarts M S).card = 2 ∧ (∃ b ∈ M.atoms, b ∉ S) ∧
      ∀ S' ⊆ M.atoms, M.atom e ∈ S' → M.atom (M.mate e) ∈ S' → (crossDarts M S').card = 2 →
        (∃ b ∈ M.atoms, b ∉ S') → S.card ≤ S'.card := by
  classical
  obtain ⟨S0, hS0, a, ha, b, hb, hbS, h2⟩ := hII
  have hc := card_cross_eraseBond M e S0
  have hn := hnoB S0 hS0
  have hpq : (M.atom e ∈ S0 ↔ M.atom (M.mate e) ∈ S0) := by
    constructor
    · intro h; by_contra h'; rw [ite_of_pos ⟨h, h'⟩, ite_of_not (fun h'' => h''.2 h)] at hc; omega
    · intro h; by_contra h'; rw [ite_of_not (fun h'' => h''.2 h), ite_of_pos ⟨h, h'⟩] at hc; omega
  obtain ⟨S1, hS1, hp1, hq1, h21, hw1⟩ : ∃ S1 ⊆ M.atoms, M.atom e ∈ S1 ∧ M.atom (M.mate e) ∈ S1 ∧
      (crossDarts M S1).card = 2 ∧ ∃ b ∈ M.atoms, b ∉ S1 := by
    by_cases hp : M.atom e ∈ S0
    · exact ⟨S0, hS0, hp, hpq.mp hp, h2, b, hb, hbS⟩
    · refine ⟨M.atoms \ S0, sdiff_subset, mem_sdiff.mpr ⟨M.atom_mem _, hp⟩,
        mem_sdiff.mpr ⟨M.atom_mem _, fun h => hp (hpq.mpr h)⟩, by rw [card_crossDarts_compl, h2],
        a, hS0 ha, fun h => (mem_sdiff.mp h).2 ha⟩
  let F := M.atoms.powerset.filter fun S => M.atom e ∈ S ∧ M.atom (M.mate e) ∈ S ∧ (crossDarts M S).card = 2 ∧
    ∃ b ∈ M.atoms, b ∉ S
  have hF : S1 ∈ F := mem_filter.mpr ⟨mem_powerset.mpr hS1, hp1, hq1, h21, hw1⟩
  obtain ⟨S, hSF, hmin⟩ := exists_min_image F card ⟨S1, hF⟩
  obtain ⟨hSp, hp, hq, h2S, hwS⟩ := mem_filter.mp hSF
  exact ⟨S, mem_powerset.mp hSp, hp, hq, h2S, hwS, fun S' hS' hp' hq' h2' hw' =>
    hmin S' (mem_filter.mpr ⟨mem_powerset.mpr hS', hp', hq', h2', hw'⟩)⟩

/-- **The crossing darts of a bi-bridge side**: opposite directions. -/
theorem bibridge_darts {M : Molecule V D} (hM : IsCore M) {S : Finset V} (hS : S ⊆ M.atoms)
    (h2 : (crossDarts M S).card = 2) :
    ∃ x₁ x₂, x₁ ≠ x₂ ∧ crossDarts M S = {x₁, x₂} ∧ M.out x₁ = true ∧ M.out x₂ = false := by
  classical
  obtain ⟨x, y, hxy, hs⟩ := card_eq_two.mp h2
  have hbal := cross_out_eq_in M (S := S) fun v hv => by
    obtain ⟨h1, h2⟩ := hM.out_eq v (hS hv); rw [h1, h2]
  rw [hs] at hbal
  rw [filter_insert, filter_insert, filter_singleton, filter_singleton] at hbal
  by_cases hx : M.out x = true <;> by_cases hy : M.out y = true
  · simp [hx, hy, hxy] at hbal
  · exact ⟨x, y, hxy, hs, hx, by simpa using hy⟩
  · exact ⟨y, x, hxy.symm, by rw [hs, pair_comm], hy, by simpa using hx⟩
  · simp only [Bool.not_eq_true] at hx hy
    simp [hx, hy, hxy] at hbal

/-- **No cut vertex ⇒ the two crossing darts have distinct atoms.** -/
theorem bibridge_atoms_ne {M : Molecule V D}
    (hcutv : ∀ w ∈ M.atoms, ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, a ≠ w → b ≠ w →
      (Degen.eraseAtoms M {w}).SameComponent a b)
    {S : Finset V} (hS : S ⊆ M.atoms) {x₁ x₂ : D} (hs : crossDarts M S = {x₁, x₂}) {p q : V} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) {b : V} (hb : b ∈ M.atoms) (hbS : b ∉ S) : M.atom x₁ ≠ M.atom x₂ := by
  classical
  intro h
  set a := M.atom x₁
  have ha : a ∈ S := (mem_crossDarts.mp (by rw [hs]; exact mem_insert_self _ _ : x₁ ∈ crossDarts M S)).1
  obtain ⟨c, hcS, hca⟩ : ∃ c ∈ S, c ≠ a := by
    by_cases hpa : p = a
    · exact ⟨q, hq, fun h' => hpq (hpa.trans h'.symm)⟩
    · exact ⟨p, hp, hpa⟩
  have hclosed : ∀ z, (Degen.eraseAtoms M {a}).atom z ∈ S.erase a →
      (Degen.eraseAtoms M {a}).atom ((Degen.eraseAtoms M {a}).mate z) ∈ S.erase a := by
    intro z hz
    have hz1 := mem_erase.mp hz
    have hz2 : M.atom (M.mate z.val) ≠ a := fun h' => z.property.2 (by rw [h']; exact mem_singleton_self a)
    refine mem_erase.mpr ⟨hz2, ?_⟩
    by_contra hout
    have hc : z.val ∈ crossDarts M S := mem_crossDarts.mpr ⟨hz1.2, hout⟩
    rw [hs] at hc
    rcases mem_insert.mp hc with h' | h'
    · exact hz1.1 (by change M.atom z.val = a; rw [h'])
    · exact hz1.1 (by change M.atom z.val = a; rw [mem_singleton.mp h', ← h])
  have hcon := hcutv a (hS ha) c (hS hcS) b hb hca (fun h' => hbS (h' ▸ ha))
  exact hbS (mem_of_mem_erase ((mem_iff_of_sameComponent_of_closed hclosed hcon).mp (mem_erase.mpr ⟨hca, hcS⟩)))

/-- **Removing the doubly bonded crossing atoms** leaves a side with two crossing darts. -/
theorem cross_sdiff_pair {M : Molecule V D} (hM : IsCore M) {S : Finset V} (hS : S ⊆ M.atoms) {x₁ x₂ : D}
    (hs : crossDarts M S = {x₁, x₂}) (hne : M.atom x₁ ≠ M.atom x₂)
    (hbb : M.bondsBetween (M.atom x₁) (M.atom x₂) = 2) :
    (crossDarts M (S \ {M.atom x₁, M.atom x₂})).card = 2 := by
  classical
  set a₁ := M.atom x₁
  set a₂ := M.atom x₂
  have hx1 : x₁ ∈ crossDarts M S := by rw [hs]; exact mem_insert_self _ _
  have hx2 : x₂ ∈ crossDarts M S := by rw [hs]; exact mem_insert_of_mem (mem_singleton_self _)
  have ha1 : a₁ ∈ S := (mem_crossDarts.mp hx1).1
  have ha2 : a₂ ∈ S := (mem_crossDarts.mp hx2).1
  set P : Finset V := {a₁, a₂}
  have hPS : P ⊆ S := by intro z hz; rcases mem_insert.mp hz with rfl | hz; · exact ha1
                         · rw [mem_singleton.mp hz]; exact ha2
  -- `|∂P| = 4`
  have hP4 : (crossDarts M P).card = 4 := by
    have h := card_cross_add_sum M hM.loop P
    rw [sum_pair hne, sum_pair hne, show P.erase a₁ = {a₂} by
        ext z; simp only [P, mem_erase, mem_insert, mem_singleton]; constructor
        · rintro ⟨h1, h2 | h2⟩; · exact absurd h2 h1
          · exact h2
        · rintro rfl; exact ⟨hne.symm, Or.inr rfl⟩,
      show P.erase a₂ = {a₁} by
        ext z; simp only [P, mem_erase, mem_insert, mem_singleton]; constructor
        · rintro ⟨h1, h2 | h2⟩; · exact h2
          · exact absurd h2 h1
        · rintro rfl; exact ⟨hne, Or.inl rfl⟩,
      sum_singleton, sum_singleton, bondsBetween_symm M a₂ a₁, hbb,
      hM.reg _ (hS ha1), hM.reg _ (hS ha2)] at h
    omega
  -- the darts of `∂P` leaving `S` are `x₁, x₂`
  have hA : (crossDarts M P).filter (fun y => M.atom (M.mate y) ∉ S) = {x₁, x₂} := by
    ext y
    simp only [mem_filter, mem_crossDarts]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      rw [← hs]; exact mem_crossDarts.mpr ⟨hPS h1, h3⟩
    · intro hy
      rw [← hs] at hy
      obtain ⟨h1, h2⟩ := mem_crossDarts.mp hy
      rw [hs] at hy
      refine ⟨⟨?_, fun h => h2 (hPS h)⟩, h2⟩
      rcases mem_insert.mp hy with rfl | hy'
      · exact mem_insert_self _ _
      · rw [mem_singleton.mp hy']; exact mem_insert_of_mem (mem_singleton_self _)
  have hZ : ((crossDarts M P).filter (fun y => ¬ M.atom (M.mate y) ∉ S)).card = 2 := by
    have h := card_filter_add_card_filter_not (s := crossDarts M P) (fun y => M.atom (M.mate y) ∉ S)
    rw [hA, card_pair (fun h' => hne (congrArg M.atom h')), hP4] at h
    omega
  rw [← hZ]
  refine card_bij (fun x _ => M.mate x) ?_ ?_ ?_
  · intro x hx
    obtain ⟨h1, h2⟩ := mem_crossDarts.mp hx
    obtain ⟨h1S, h1P⟩ := mem_sdiff.mp h1
    have hmS : M.atom (M.mate x) ∈ S := by
      by_contra hm
      have hc : x ∈ crossDarts M S := mem_crossDarts.mpr ⟨h1S, hm⟩
      rw [hs] at hc
      rcases mem_insert.mp hc with rfl | hc'
      · exact h1P (mem_insert_self _ _)
      · rw [mem_singleton.mp hc'] at h1P; exact h1P (mem_insert_of_mem (mem_singleton_self _))
    have hmP : M.atom (M.mate x) ∈ P := by
      by_contra hm; exact h2 (mem_sdiff.mpr ⟨hmS, hm⟩)
    refine mem_filter.mpr ⟨mem_crossDarts.mpr ⟨hmP, by rw [M.mate_mate]; exact h1P⟩, ?_⟩
    rw [M.mate_mate]; exact not_not.mpr h1S
  · intro x _ y _ h; have := congrArg M.mate h; rwa [M.mate_mate, M.mate_mate] at this
  · intro y hy
    obtain ⟨hy1, hy2⟩ := mem_filter.mp hy
    obtain ⟨h1, h2⟩ := mem_crossDarts.mp hy1
    refine ⟨M.mate y, mem_crossDarts.mpr ⟨mem_sdiff.mpr ⟨not_not.mp hy2, h2⟩, ?_⟩, M.mate_mate y⟩
    rw [M.mate_mate]; exact fun h => (mem_sdiff.mp h).2 h1

/-- **Minimality: the crossing atoms are not doubly bonded in `𝕄 ∖ ℓ`.** -/
theorem bibridge_no_double {M : Molecule V D} (hM : IsCore M) (e : D)
    (hnoB : ∀ S ⊆ M.atoms, (crossDarts (MoleProp.eraseBond M e) S).card ≠ 1)
    {S : Finset V} (hS : S ⊆ M.atoms) (hp : M.atom e ∈ S) (hq : M.atom (M.mate e) ∈ S) (hb : ∃ b ∈ M.atoms, b ∉ S)
    (hmin : ∀ S' ⊆ M.atoms, M.atom e ∈ S' → M.atom (M.mate e) ∈ S' → (crossDarts M S').card = 2 →
      (∃ b ∈ M.atoms, b ∉ S') → S.card ≤ S'.card)
    {x₁ x₂ : D} (hs : crossDarts M S = {x₁, x₂}) (hne : M.atom x₁ ≠ M.atom x₂) :
    (MoleProp.eraseBond M e).bondsBetween (M.atom x₁) (M.atom x₂) ≤ 1 := by
  classical
  have hadd := bondsBetween_eraseBond_add M e (M.atom x₁) (M.atom x₂)
  have hle := hM.le2 (M.atom x₁) (M.atom x₂)
  by_contra hlt
  push Not at hlt
  have hends : M.ends e ≠ s(M.atom x₁, M.atom x₂) := by
    intro h; rw [ite_of_pos h] at hadd; omega
  rw [ite_of_not hends] at hadd
  have hbb : M.bondsBetween (M.atom x₁) (M.atom x₂) = 2 := by omega
  have h2' := cross_sdiff_pair hM hS hs hne hbb
  set S' := S \ {M.atom x₁, M.atom x₂}
  have hS' : S' ⊆ M.atoms := sdiff_subset.trans hS
  obtain ⟨b, hbM, hbS⟩ := hb
  have hx1 : x₁ ∈ crossDarts M S := by rw [hs]; exact mem_insert_self _ _
  have hx2 : x₂ ∈ crossDarts M S := by rw [hs]; exact mem_insert_of_mem (mem_singleton_self _)
  by_cases hpq : M.atom e ∈ S' ∧ M.atom (M.mate e) ∈ S'
  · -- a smaller side
    have := hmin S' hS' hpq.1 hpq.2 h2' ⟨b, hbM, fun h => hbS (mem_sdiff.mp h).1⟩
    have hsub : S' ⊆ S := sdiff_subset
    have hlt' : S'.card < S.card := card_lt_card ⟨hsub, fun h =>
      (mem_sdiff.mp (h (mem_crossDarts.mp hx1).1)).2 (mem_insert_self _ _)⟩
    omega
  · -- `ℓ` crosses the smaller side: a bridge of `𝕄 ∖ ℓ`
    have hc := card_cross_eraseBond M e S'
    rw [h2'] at hc
    apply hnoB S' hS'
    have hpS : M.atom e ∈ S' ∨ M.atom (M.mate e) ∈ S' := by
      by_contra hno
      push Not at hno
      have hp' : M.atom e = M.atom x₁ ∨ M.atom e = M.atom x₂ := by
        have := hno.1; simp only [S', mem_sdiff, mem_insert, mem_singleton, not_and, not_not] at this
        exact this hp
      have hq' : M.atom (M.mate e) = M.atom x₁ ∨ M.atom (M.mate e) = M.atom x₂ := by
        have := hno.2; simp only [S', mem_sdiff, mem_insert, mem_singleton, not_and, not_not] at this
        exact this hq
      apply hends
      unfold Molecule.ends
      rcases hp' with h1 | h1 <;> rcases hq' with h2 | h2
      · exact absurd (h1.trans h2.symm) (hM.loop e)
      · rw [h1, h2]
      · rw [h1, h2]; exact Sym2.eq_swap
      · exact absurd (h1.trans h2.symm) (hM.loop e)
    rcases hpS with h | h
    · have h' : M.atom (M.mate e) ∉ S' := fun h' => hpq ⟨h, h'⟩
      rw [ite_of_pos ⟨h, h'⟩, ite_of_not (fun h'' => h''.2 h)] at hc; omega
    · have h' : M.atom e ∉ S' := fun h' => hpq ⟨h', h⟩
      rw [ite_of_not (fun h'' => h''.2 h), ite_of_pos ⟨h, h'⟩] at hc; omega

end WaveTurbulence.MoleProp4
