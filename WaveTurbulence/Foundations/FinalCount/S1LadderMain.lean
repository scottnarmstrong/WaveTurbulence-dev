/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.S1LadderGap
import Mathlib.Tactic

/-!
# TARGET defdiff (L1940): all parallel rails of a ladder have the same gap up to sign
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {d : ℕ}

theorem railGap_exists {m : ℕ} {u v : Fin (m + 1) → V} (h : M.IsLadder u v) (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (j : Fin m) : ∃ r, IsRailGap M L w κ u v j r := by
  have hr := h.2.2.2.2 j
  have hu : u j.castSucc ≠ u j.succ := fun he => by
    have := h.2.1 (show Sum.elim u v (Sum.inl j.castSucc) = Sum.elim u v (Sum.inl j.succ) from he)
    simp [Fin.ext_iff] at this
  have hv : v j.castSucc ≠ v j.succ := fun he => by
    have := h.2.1 (show Sum.elim u v (Sum.inr j.castSucc) = Sum.elim u v (Sum.inr j.succ) from he)
    simp [Fin.ext_iff] at this
  obtain ⟨x, hx1, hx2⟩ := exists_dart hu (by rw [hr.1]; decide)
  obtain ⟨y, hy1, hy2⟩ := exists_dart hv (by rw [hr.2.1]; decide)
  exact ⟨_, x, y, by simp only [Molecule.ends, hx1, hx2], by simp only [Molecule.ends, hy1, hy2],
    hx1, hy1, rfl⟩

theorem railGap_dart {m : ℕ} {u v : Fin (m + 1) → V} {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)}
    {j : Fin m} {r : Mom d} (hu : u j.castSucc ≠ u j.succ) (hv : v j.castSucc ≠ v j.succ)
    (hr : IsRailGap M L w κ u v j r) :
    ∃ x y, M.atom x = u j.castSucc ∧ M.atom (M.mate x) = u j.succ ∧ M.atom y = v j.castSucc ∧
      M.atom (M.mate y) = v j.succ ∧ r = Molecule.kvec L w κ x - Molecule.kvec L w κ y := by
  obtain ⟨x, y, hx, hy, hxa, hya, rfl⟩ := hr
  have hxx := Sym2.eq_iff.mp hx
  have hyy := Sym2.eq_iff.mp hy
  change (M.atom x = u j.castSucc ∧ M.atom (M.mate x) = u j.succ) ∨
    (M.atom x = u j.succ ∧ M.atom (M.mate x) = u j.castSucc) at hxx
  change (M.atom y = v j.castSucc ∧ M.atom (M.mate y) = v j.succ) ∨
    (M.atom y = v j.succ ∧ M.atom (M.mate y) = v j.castSucc) at hyy
  refine ⟨x, y, hxa, ?_, hya, ?_, rfl⟩
  · rcases hxx with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · exact absurd (hxa.symm.trans h1) hu
  · rcases hyy with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · exact absurd (hya.symm.trans h1) hv

/-- Adjacent rails have gaps of equal norm. -/
theorem railGap_step (hM : M.IsMolecule) {m : ℕ} {u v : Fin (m + 1) → V} (h : M.IsLadder u v)
    {L : ℝ} {w : Mom d} {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hκ : M.IsDecoration L w c κ)
    (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) (j : Fin m) (hj : j.val + 1 < m)
    {r r' : Mom d} (hr : IsRailGap M L w κ u v j r)
    (hr' : IsRailGap M L w κ u v ⟨j.val + 1, hj⟩ r') : ‖r‖ = ‖r'‖ := by
  have hinj := h.2.1
  have ne_u : ∀ a b : Fin (m + 1), a ≠ b → u a ≠ u b := fun a b hab he => hab (by
    have := hinj (show Sum.elim u v (Sum.inl a) = Sum.elim u v (Sum.inl b) from he)
    simpa using this)
  have ne_v : ∀ a b : Fin (m + 1), a ≠ b → v a ≠ v b := fun a b hab he => hab (by
    have := hinj (show Sum.elim u v (Sum.inr a) = Sum.elim u v (Sum.inr b) from he)
    simpa using this)
  have ne_uv : ∀ a b : Fin (m + 1), u a ≠ v b := fun a b he => by
    have := hinj (show Sum.elim u v (Sum.inl a) = Sum.elim u v (Sum.inr b) from he)
    simp at this
  set a : Fin (m + 1) := j.castSucc with ha
  set b : Fin (m + 1) := j.succ with hb
  set c' : Fin (m + 1) := (⟨j.val + 1, hj⟩ : Fin m).succ with hc'
  have hab : a ≠ b := by simp [ha, hb, Fin.ext_iff]
  have hbc : b ≠ c' := by simp [hb, hc', Fin.ext_iff]
  have hac : a ≠ c' := by simp [ha, hc', Fin.ext_iff]; omega
  have hb' : (⟨j.val + 1, hj⟩ : Fin m).castSucc = b := by simp [hb, Fin.ext_iff]
  have hrr := h.2.2.2.2 j
  have hrr' := h.2.2.2.2 ⟨j.val + 1, hj⟩
  rw [hb'] at hrr'
  -- the dart data of the two rails
  obtain ⟨X, Y, hX1, hX2, hY1, hY2, hrX⟩ := railGap_dart (ne_u a b hab) (ne_v a b hab) hr
  obtain ⟨X', Y', hX1', hX2', hY1', hY2', hrX'⟩ :=
    railGap_dart (hb' ▸ ne_u b c' hbc) (hb' ▸ ne_v b c' hbc) hr'
  rw [hb'] at hX1' hY1'
  -- conservation at the interior rung
  have hbat : u b ∈ M.atoms := (h.2.2.1 b).1
  have hbat' : v b ∈ M.atoms := (h.2.2.1 b).2
  have hpq := h.2.2.2.1 b
  have sym1 : M.bondsBetween (u b) (u a) = 1 := by rw [Mole.bondsBetween_symm M]; exact hrr.1
  have sym2 : M.bondsBetween (v b) (v a) = 1 := by rw [Mole.bondsBetween_symm M]; exact hrr.2.1
  have hpq' : M.bondsBetween (v b) (u b) = 2 := by rw [Mole.bondsBetween_symm M]; exact hpq
  have hdp : M.deg (u b) = 4 := deg_eq_four_of_counts hM hbat hpq sym1 hrr'.1 (ne_uv a b).symm
    (ne_uv c' b).symm (ne_u a c' hac) (ne_uv b b) (ne_u b a hab.symm) (ne_u b c' hbc)
  have hdq : M.deg (v b) = 4 := deg_eq_four_of_counts hM hbat' hpq' sym2 hrr'.2.1 (ne_uv b a)
    (ne_uv b c') (ne_v a c' hac) (ne_uv b b).symm (ne_v b a hab.symm) (ne_v b c' hbc)
  have hcp : ∑ x ∈ M.dartsAt (u b), M.dartSign x • Molecule.kvec L w κ x = 0 :=
    (hκ.2 _ hbat).trans (hc _ hbat hdp)
  have hcq : ∑ x ∈ M.dartsAt (v b), M.dartSign x • Molecule.kvec L w κ x = 0 :=
    (hκ.2 _ hbat').trans (hc _ hbat' hdq)
  have hk (x : D) : Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x := by
    simp only [Molecule.kvec, hκ.1 x]
  obtain ⟨x1, x2, y1, y2, ax1, bx1, ax2, bx2, ay1, by1, ay2, by2, hsum⟩ :=
    rung_conservation (M := M) hk hpq sym1 hrr'.1 sym2 hrr'.2.1 (ne_uv a b).symm (ne_uv c' b).symm
      (ne_u a c' hac) (ne_uv b a) (ne_uv b c') (ne_v a c' hac) (ne_uv b b) (ne_u b a hab.symm)
      (ne_u b c' hbc) (ne_v b a hab.symm) (ne_v b c' hbc) hdp hdq hcp hcq
  -- identify the rail darts
  have eX : X = M.mate x1 := uniq_dart (ne_u a b hab) hrr.1 hX1 hX2 bx1 (by rw [M.mate_mate]; exact ax1)
  have eY : Y = M.mate y1 := uniq_dart (ne_v a b hab) hrr.2.1 hY1 hY2 by1 (by rw [M.mate_mate]; exact ay1)
  have eX' : X' = x2 := uniq_dart (ne_u b c' hbc) hrr'.1 hX1' hX2' ax2 bx2
  have eY' : Y' = y2 := uniq_dart (ne_v b c' hbc) hrr'.2.1 hY1' hY2' ay2 by2
  have hr1 : r = Molecule.kvec L w κ x1 - Molecule.kvec L w κ y1 := by
    rw [hrX, eX, eY, hk, hk]
  have hr2 : r' = Molecule.kvec L w κ x2 - Molecule.kvec L w κ y2 := by
    rw [hrX', eX', eY']
  -- directions of the two rails
  have dir : ∀ (a b : V) (z : D), a ≠ b → M.bondsBetween a b = 1 → M.atom z = a →
      M.atom (M.mate z) = b → (M.Directed a b ↔ M.out z = true) := by
    intro a b z hab h1 hz hz'
    constructor
    · rintro ⟨x, hxo, hxa, hxb⟩
      have := uniq_dart hab h1 hxa hxb hz hz'
      rw [← this]; exact hxo
    · intro ho; exact ⟨z, ho, hz, hz'⟩
  have d1 := hrr.2.2
  have d2 := hrr'.2.2
  rw [dir _ _ (M.mate x1) (ne_u a b hab) hrr.1 bx1 (by rw [M.mate_mate]; exact ax1),
    dir _ _ y1 (ne_v b a hab.symm) sym2 ay1 by1] at d1
  rw [dir _ _ x2 (ne_u b c' hbc) hrr'.1 ax2 bx2,
    dir _ _ (M.mate y2) (ne_v c' b hbc.symm)
      (by rw [Mole.bondsBetween_symm M]; exact hrr'.2.1) by2
      (by rw [M.mate_mate]; exact ay2)] at d2
  rw [M.out_mate] at d1 d2
  have hs1 : M.dartSign y1 = - M.dartSign x1 := by
    unfold Molecule.dartSign
    cases hx : M.out x1 <;> cases hy : M.out y1 <;> simp_all
  have hs2 : M.dartSign y2 = - M.dartSign x2 := by
    unfold Molecule.dartSign
    cases hx : M.out x2 <;> cases hy : M.out y2 <;> simp_all
  have habs : ∀ x : D, M.dartSign x = 1 ∨ M.dartSign x = -1 := by
    intro x; unfold Molecule.dartSign; split_ifs <;> simp
  rw [hs1, hs2] at hsum
  have key : M.dartSign x1 • r + M.dartSign x2 • r' = 0 := by
    rw [hr1, hr2, smul_sub, smul_sub]
    rw [neg_smul, neg_smul] at hsum
    rw [← hsum]; abel
  have hn : ‖M.dartSign x1 • r‖ = ‖M.dartSign x2 • r'‖ := by
    rw [eq_neg_of_add_eq_zero_left key, norm_neg]
  have e1 : ‖M.dartSign x1 • r‖ = ‖r‖ := by
    rcases habs x1 with h | h <;> simp [h]
  have e2 : ‖M.dartSign x2 • r'‖ = ‖r'‖ := by
    rcases habs x2 with h | h <;> simp [h]
  rw [← e1, ← e2]; exact hn

/-- **TARGET L1940.** All pairs of parallel single bonds of a ladder have the same gap up to sign:
the gaps of any two rails of a ladder of length `m ≥ 1` have equal norm, hence the same kind. -/
theorem railGap_norm_eq (hM : M.IsMolecule) {m : ℕ} {u v : Fin (m + 1) → V} (h : M.IsLadder u v)
    {L : ℝ} {w : Mom d} {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hκ : M.IsDecoration L w c κ)
    (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) {j j' : Fin m} {r r' : Mom d}
    (hr : IsRailGap M L w κ u v j r) (hr' : IsRailGap M L w κ u v j' r') : ‖r‖ = ‖r'‖ := by
  have key : ∀ (n : ℕ) (i : ℕ) (hi : i + n < m) {r r' : Mom d},
      IsRailGap M L w κ u v ⟨i, by omega⟩ r → IsRailGap M L w κ u v ⟨i + n, hi⟩ r' → ‖r‖ = ‖r'‖ := by
    intro n
    induction n with
    | zero =>
      intro i hi r r' h1 h2
      have hne : ∀ x y : Fin (m + 1), x ≠ y → u x ≠ u y := fun x y hxy he => hxy (by
        have := h.2.1 (show Sum.elim u v (Sum.inl x) = Sum.elim u v (Sum.inl y) from he)
        simpa using this)
      have hnev : ∀ x y : Fin (m + 1), x ≠ y → v x ≠ v y := fun x y hxy he => hxy (by
        have := h.2.1 (show Sum.elim u v (Sum.inr x) = Sum.elim u v (Sum.inr y) from he)
        simpa using this)
      have hjj : (⟨i, by omega⟩ : Fin m) = ⟨i + 0, hi⟩ := rfl
      have hu : u (⟨i, by omega⟩ : Fin m).castSucc ≠ u (⟨i, by omega⟩ : Fin m).succ :=
        hne _ _ (by simp [Fin.ext_iff])
      have hv : v (⟨i, by omega⟩ : Fin m).castSucc ≠ v (⟨i, by omega⟩ : Fin m).succ :=
        hnev _ _ (by simp [Fin.ext_iff])
      obtain ⟨x, y, a1, a2, b1, b2, rfl⟩ := railGap_dart hu hv h1
      obtain ⟨x', y', a1', a2', b1', b2', rfl⟩ := railGap_dart hu hv h2
      have hr1 := h.2.2.2.2 ⟨i, by omega⟩
      have e1 := uniq_dart hu hr1.1 a1 a2 a1' a2'
      have e2 := uniq_dart hv hr1.2.1 b1 b2 b1' b2'
      rw [e1, e2]
    | succ n ih =>
      intro i hi r r' h1 h2
      obtain ⟨r'', h3⟩ := railGap_exists h L w κ (⟨i + n, by omega⟩ : Fin m)
      have step := railGap_step hM h hκ hc ⟨i + n, by omega⟩ (by simp only; omega) h3
        (by convert h2 using 2)
      exact (ih i (by omega) h1 h3).trans step
  rcases le_total j.val j'.val with hle | hle
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hle
    exact key n j.val (by omega) (by simpa using hr) (by
      have : j' = ⟨j.val + n, by omega⟩ := Fin.ext hn
      rw [← this]; exact hr')
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hle
    exact (key n j'.val (by omega) (by simpa using hr') (by
      have : j = ⟨j'.val + n, by omega⟩ := Fin.ext hn
      rw [← this]; exact hr)).symm

/-- The pinned first-rail gap `IsLadderGap` of the ladder is the gap of rail `0`. -/
theorem isLadderGap_iff_railGap {m : ℕ} {u v : Fin (m + 1) → V} (hm : 1 ≤ m) {L : ℝ} {w : Mom d}
    {κ : D → (Fin d → ℤ)} {r : Mom d} :
    M.IsLadderGap L w κ u v hm r ↔ IsRailGap M L w κ u v ⟨0, hm⟩ r := Iff.rfl

end WaveTurbulence.Stage1
