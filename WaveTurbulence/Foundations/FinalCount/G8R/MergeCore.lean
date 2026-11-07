/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.MergeGraph
import Mathlib.Tactic

/-! # The merged molecule stays in the core class

DH23 L1977: "M″ has no quadruple bond (otherwise M′ would be a triangle of double bonds) and no triple bond (otherwise
M′ would contain a triangle with one single bond and two double bonds, and the two outgoing bonds of this triangle would
form a bi-bridge)". Formally: if `𝕄` is core, `v₁ = v₂` is a double bond and `𝕄` has no cut with exactly two crossing
darts, then `bb(v₁, y) + bb(v₂, y) ≤ 2` for every `y` (the three atoms `v₁, v₂, y` would have at most two crossing
darts), so the merged molecule has no triple bond. It is not `T` when an atom outside every double bond survives.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [Fintype D] [DecidableEq D] in
theorem sum_three {f : V → V → ℕ} {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ u ∈ ({a, b, c} : Finset V), ∑ w ∈ ({a, b, c} : Finset V).erase u, f u w =
      f a b + f a c + (f b a + f b c) + (f c a + f c b) := by
  have e1 : ({a, b, c} : Finset V).erase a = {b, c} := by
    ext x; simp only [mem_erase, mem_insert, mem_singleton]; aesop
  have e2 : ({a, b, c} : Finset V).erase b = {a, c} := by
    ext x; simp only [mem_erase, mem_insert, mem_singleton]; aesop
  have e3 : ({a, b, c} : Finset V).erase c = {a, b} := by
    ext x; simp only [mem_erase, mem_insert, mem_singleton]; aesop
  rw [sum_insert (by simp [hab, hac]), sum_insert (by simp [hbc]), sum_singleton, e1, e2, e3,
    sum_pair hbc, sum_pair hac, sum_pair hab]
  ring

/-- **No two-dart cut ⇒ the merged atom has no triple bond.** -/
theorem merge_pair_sum_le_two {M : Molecule V D} (hM : IsCore M) {v₁ v₂ : V} (hv₁ : v₁ ∈ M.atoms)
    (hv₂ : v₂ ∈ M.atoms) (hne : v₁ ≠ v₂) (h2 : M.bondsBetween v₁ v₂ = 2) (h4 : 4 ≤ M.atoms.card)
    (hcut : ∀ S ⊆ M.atoms, ∀ a ∈ S, ∀ b ∈ M.atoms, b ∉ S → (crossDarts M S).card ≠ 2)
    {y : V} (hy1 : y ≠ v₁) (hy2 : y ≠ v₂) : M.bondsBetween v₁ y + M.bondsBetween v₂ y ≤ 2 := by
  classical
  by_contra hlt
  push Not at hlt
  have hy : y ∈ M.atoms := by
    rcases Nat.eq_zero_or_pos (M.bondsBetween v₁ y) with h | h
    · exact mem_atoms_of_bondsBetween_pos (a := v₂) (by omega)
    · exact mem_atoms_of_bondsBetween_pos h
  set S : Finset V := {v₁, v₂, y}
  have hS : S ⊆ M.atoms := by
    intro x hx; simp only [S, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hsum := card_cross_add_sum M hM.loop S
  rw [sum_three hne hy1.symm hy2.symm] at hsum
  have hdeg : ∑ u ∈ S, M.deg u = 12 := by
    rw [sum_congr rfl fun u hu => hM.reg u (hS hu)]
    simp only [S, sum_const, smul_eq_mul]
    rw [card_insert_of_notMem (by simp [hne, hy1.symm]), card_insert_of_notMem (by simp [hy2.symm]),
      card_singleton]
  rw [hdeg, bondsBetween_symm M v₂ v₁, bondsBetween_symm M y v₁, bondsBetween_symm M y v₂] at hsum
  have hcard : S.card = 3 := by
    simp only [S]
    rw [card_insert_of_notMem (by simp [hne, hy1.symm]), card_insert_of_notMem (by simp [hy2.symm]),
      card_singleton]
  obtain ⟨b, hb, hbS⟩ : ∃ b ∈ M.atoms, b ∉ S := by
    by_contra h; push Not at h
    have := card_le_card (show M.atoms ⊆ S from h); omega
  have hv₁S : v₁ ∈ S := by simp [S]
  have hne' := crossDarts_nonempty M hM.conn hv₁S hv₁ hb hbS
  have hpos := card_pos.mpr hne'
  have h2' := hcut S hS v₁ hv₁S b hb hbS
  have hev := cross_even_of_reg M hM.reg hS
  obtain ⟨k, hk⟩ := hev
  omega

/-- **The merged molecule is core**, given no two-dart cut and that it is not `T`. -/
theorem merge_isCore {M : Molecule V D} (hM : IsCore M) {v₁ v₂ : V} (hv₁ : v₁ ∈ M.atoms) (hv₂ : v₂ ∈ M.atoms)
    (hne : v₁ ≠ v₂) (h2 : M.bondsBetween v₁ v₂ = 2) (h4 : 4 ≤ M.atoms.card)
    (hcut : ∀ S ⊆ M.atoms, ∀ a ∈ S, ∀ b ∈ M.atoms, b ∉ S → (crossDarts M S).card ≠ 2)
    (hT : ¬ IsT (mergePair M v₁ v₂ hv₁ hne)) : IsCore (mergePair M v₁ v₂ hv₁ hne) := by
  classical
  have hio1 := hM.out_eq v₁ hv₁
  have hio2 := hM.out_eq v₂ hv₂
  refine ⟨fun a ha => ?_, Merge.loopFree hM.loop, fun a ha => ?_, Merge.connected hM.conn, fun a b => ?_, hT⟩
  · rw [Merge.atoms_eq] at ha
    by_cases h1 : a = v₁
    · subst h1
      have e1 := Merge.outdeg_v₁ (M := M) (hv₁ := hv₁) (hne := hne)
      have e2 := Merge.indeg_v₁ (M := M) (hv₁ := hv₁) (hne := hne)
      omega
    · rw [Merge.outdeg_of_ne h1 (ne_of_mem_erase ha), Merge.indeg_of_ne h1 (ne_of_mem_erase ha)]
      exact hM.cap a (mem_of_mem_erase ha)
  · rw [Merge.atoms_eq] at ha
    by_cases h1 : a = v₁
    · subst h1
      have e := Merge.deg_v₁ (M := M) (hv₁ := hv₁) (hne := hne)
      rw [hM.reg _ hv₁, hM.reg _ hv₂] at e
      omega
    · rw [Merge.deg_of_ne h1 (ne_of_mem_erase ha)]; exact hM.reg a (mem_of_mem_erase ha)
  · by_cases ha2 : a = v₂
    · rw [ha2, Merge.bondsBetween_v₂]; omega
    by_cases hb2 : b = v₂
    · rw [hb2, bondsBetween_symm, Merge.bondsBetween_v₂]; omega
    by_cases ha1 : a = v₁
    · by_cases hb1 : b = v₁
      · rw [ha1, hb1, bondsBetween_self_eq_zero (Merge.loopFree hM.loop)]; omega
      · rw [ha1, Merge.bondsBetween_v₁ hb1 hb2]
        exact merge_pair_sum_le_two hM hv₁ hv₂ hne h2 h4 hcut hb1 hb2
    · by_cases hb1 : b = v₁
      · rw [hb1, bondsBetween_symm, Merge.bondsBetween_v₁ ha1 ha2]
        exact merge_pair_sum_le_two hM hv₁ hv₂ hne h2 h4 hcut ha1 ha2
      · rw [Merge.bondsBetween_far ha1 ha2 hb1 hb2]; exact hM.le2 a b

omit [DecidableEq D] in
/-- **The merged molecule is not `T`** if some atom `p ∉ {v₁, v₂}` lies on no double bond of `𝕄`. -/
theorem merge_not_T {M : Molecule V D} {v₁ v₂ : V} (hv₁ : v₁ ∈ M.atoms) (hne : v₁ ≠ v₂) {p : V}
    (hp1 : p ≠ v₁) (hp2 : p ≠ v₂) (hp : p ∈ M.atoms) (hpd : ∀ w, M.bondsBetween p w ≠ 2) :
    ¬ IsT (mergePair M v₁ v₂ hv₁ hne) := by
  rintro ⟨e, f, g, hef, hfg, heg, hs, h1, h2, h3, _⟩
  have hpm : p ∈ (mergePair M v₁ v₂ hv₁ hne).atoms := by rw [Merge.atoms_eq]; exact mem_erase.mpr ⟨hp2, hp⟩
  -- two distinct partners of `p` in `T`
  obtain ⟨b₁, b₂, hb, e1, e2⟩ : ∃ b₁ b₂, b₁ ≠ b₂ ∧ (mergePair M v₁ v₂ hv₁ hne).bondsBetween p b₁ = 2 ∧
      (mergePair M v₁ v₂ hv₁ hne).bondsBetween p b₂ = 2 := by
    rw [hs] at hpm
    simp only [mem_insert, mem_singleton] at hpm
    rcases hpm with rfl | rfl | rfl
    · exact ⟨f, g, hfg, h1, h3⟩
    · exact ⟨e, g, heg, by rw [bondsBetween_symm]; exact h1, h2⟩
    · exact ⟨e, f, hef, by rw [bondsBetween_symm]; exact h3, by rw [bondsBetween_symm]; exact h2⟩
  have hb2 : ∀ b, (mergePair M v₁ v₂ hv₁ hne).bondsBetween p b = 2 → b ≠ v₂ := by
    intro b hb h; rw [h, bondsBetween_symm, Merge.bondsBetween_v₂] at hb; omega
  by_cases hb1 : b₁ = v₁
  · have hb2' : b₂ ≠ v₁ := fun h => hb (hb1.trans h.symm)
    rw [Merge.bondsBetween_far hp1 hp2 hb2' (hb2 b₂ e2)] at e2
    exact hpd b₂ e2
  · rw [Merge.bondsBetween_far hp1 hp2 hb1 (hb2 b₁ e1)] at e1
    exact hpd b₁ e1

end WaveTurbulence.MoleProp4
