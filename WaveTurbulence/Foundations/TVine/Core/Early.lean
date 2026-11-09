/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Y2

/-!
# Lemma E: early reduction of a triple bond (M4 §5.2; REF-M4 claim 4)

**Lemma E** (`y2Path_early`). Let `Q = {a, b}` be a (Y2) pair of `H` (externals `c ≠ d`) and `H →* T'` along
`ps` with `T'` a doubled triangle. Then `Q` occurs exactly once in `ps`, and `H/Q →* T'` along `ps` with that
occurrence removed.

Infrastructure:
* `IsY2Pair.mult_a`, `.mult_b`: the bonds at the atoms of a (Y2) pair, normalised;
* `Stuck G a b n d` (`n ∈ {3, 4}`): a triple pair whose two externals coincide (`n = 3`), or a quadruple pair
  with no further bonds (`n = 4`); it survives every move (`Stuck.y2Move`), so no path from it reaches a doubled
  triangle (`Stuck.not_y2Path`);
* `y2Move_y2Move_mult`: the normal form of two successive moves (used for commutations).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

/-! ## Basic facts -/

section Accessors
variable {G : UMultigraph V} {a b c d : V} (h : IsY2Pair G a b c d)
include h
theorem IsY2Pair.ne : a ≠ b := h.1
theorem IsY2Pair.ext_ne : c ≠ d := h.2.1
theorem IsY2Pair.c_ne_a : c ≠ a := h.2.2.1
theorem IsY2Pair.c_ne_b : c ≠ b := h.2.2.2.1
theorem IsY2Pair.d_ne_a : d ≠ a := h.2.2.2.2.1
theorem IsY2Pair.d_ne_b : d ≠ b := h.2.2.2.2.2.1
theorem IsY2Pair.mult_ab : G.mult s(a, b) = 3 := h.2.2.2.2.2.2.1
theorem IsY2Pair.mult_ac : G.mult s(a, c) = 1 := h.2.2.2.2.2.2.2.1
theorem IsY2Pair.mult_bd : G.mult s(b, d) = 1 := h.2.2.2.2.2.2.2.2.1
theorem IsY2Pair.a_other : ∀ x, x ≠ b → x ≠ c → G.mult s(a, x) = 0 := h.2.2.2.2.2.2.2.2.2.1
theorem IsY2Pair.b_other : ∀ x, x ≠ a → x ≠ d → G.mult s(b, x) = 0 := h.2.2.2.2.2.2.2.2.2.2
end Accessors

theorem doubledTriangle_mult_le {G : UMultigraph V} (h : IsDoubledTriangle G) (e : Sym2 V) : G.mult e ≤ 2 := by
  obtain ⟨a, b, c, -, -, -, -, hm⟩ := h
  rw [hm e]; split_ifs <;> omega

theorem IsY2Pair.mult_a {G : UMultigraph V} {a b c d : V} (h : IsY2Pair G a b c d) (x : V) :
    G.mult s(a, x) = if x = b then 3 else if x = c then 1 else 0 := by
  obtain ⟨-, -, -, -, -, -, h3, hc, -, hax, -⟩ := h
  split_ifs with h1 h2
  · subst h1; exact h3
  · subst h2; exact hc
  · exact hax x h1 h2

theorem IsY2Pair.mult_b {G : UMultigraph V} {a b c d : V} (h : IsY2Pair G a b c d) (x : V) :
    G.mult s(b, x) = if x = a then 3 else if x = d then 1 else 0 := h.swap.mult_a x

theorem IsY2Pair.of_mult {G : UMultigraph V} {a b c d : V} (hab : a ≠ b) (hcd : c ≠ d) (hca : c ≠ a)
    (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (ha : ∀ x, G.mult s(a, x) = if x = b then 3 else if x = c then 1 else 0)
    (hb : ∀ x, G.mult s(b, x) = if x = a then 3 else if x = d then 1 else 0) : IsY2Pair G a b c d := by
  refine ⟨hab, hcd, hca, hcb, hda, hdb, ?_, ?_, ?_, fun x h1 h2 => ?_, fun x h1 h2 => ?_⟩
  · rw [ha]; simp
  · rw [ha]; simp [hcb]
  · rw [hb]; simp [hda]
  · rw [ha]; simp [h1, h2]
  · rw [hb]; simp [h1, h2]

/-- The externals of a (Y2) pair are determined by the pair. -/
theorem IsY2Pair.ext_eq {G : UMultigraph V} {a b c d c' d' : V} (h : IsY2Pair G a b c d)
    (h' : IsY2Pair G a b c' d') : c' = c ∧ d' = d := by
  have h1 := h.mult_a c'
  have h2 := h.mult_b d'
  rw [h'.mult_ac] at h1
  rw [h'.mult_bd] at h2
  constructor
  · by_contra hc; simp [h'.c_ne_b, hc] at h1
  · by_contra hd; simp [h'.d_ne_a, hd] at h2

/-- Two (Y2) pairs are equal or disjoint. -/
theorem IsY2Pair.disj {G : UMultigraph V} {a b c d p q p' q' : V} (hQ : IsY2Pair G a b c d)
    (hP : IsY2Pair G p q p' q') (hne : s(p, q) ≠ s(a, b)) : p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b := by
  have hpq := hP.mult_ab
  have hqp : G.mult s(q, p) = 3 := by rw [Sym2.eq_swap]; exact hpq
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
  · rw [hQ.mult_a] at hpq
    split_ifs at hpq with h1 <;> first | omega | exact hne (by rw [h1])
  · rw [hQ.mult_b] at hpq
    split_ifs at hpq with h1 <;> first | omega | exact hne (by rw [h1, Sym2.eq_swap])
  · rw [hQ.mult_a] at hqp
    split_ifs at hqp with h1 <;> first | omega | exact hne (by rw [h1, Sym2.eq_swap])
  · rw [hQ.mult_b] at hqp
    split_ifs at hqp with h1 <;> first | omega | exact hne (by rw [h1])

/-- Every pair of a path consists of atoms of its start. -/
theorem Y2Path.mem_verts {G G' : UMultigraph V} {ps : List (Sym2 V)} (h : Y2Path G ps G') :
    ∀ z ∈ ps, ∀ x ∈ z, x ∈ G.verts := by
  induction h with
  | nil => intro z hz; simp at hz
  | @cons G G' a b c d ps hp _ ih =>
    intro z hz x hx
    rcases List.mem_cons.mp hz with rfl | hz
    · rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact hp.a_mem
      · exact hp.b_mem
    · have := ih z hz x hx
      rw [y2Move_verts hp] at this
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase this)

theorem y2Move_verts_sub {G : UMultigraph V} {a b c d x : V} (hx : x ∈ (y2Move G a b c d).verts) :
    x ≠ a ∧ x ≠ b := by
  have hx' : x ∈ ((G.verts ∪ _).erase a).erase b := hx
  rw [Finset.mem_erase, Finset.mem_erase] at hx'
  exact ⟨hx'.2.1, hx'.1⟩

/-! ## Normal form of two moves -/

/-- **Two successive moves**: the second's added bond avoids the first pair. -/
theorem y2Move_y2Move_mult {H : UMultigraph V} {p q p' q' a b c d : V}
    (h : IsY2Pair (y2Move H p q p' q') a b c d) (e : Sym2 V) :
    (y2Move (y2Move H p q p' q') a b c d).mult e =
      if a ∈ e ∨ b ∈ e ∨ p ∈ e ∨ q ∈ e then 0 else
        H.mult e + (if e = s(p', q') then 1 else 0) + (if e = s(c, d) then 1 else 0) := by
  have hc := y2Move_verts_sub h.c_mem
  have hd := y2Move_verts_sub h.d_mem
  rw [y2Move_mult, y2Move_mult]
  by_cases hab : a ∈ e ∨ b ∈ e
  · have h4 : a ∈ e ∨ b ∈ e ∨ p ∈ e ∨ q ∈ e := by tauto
    rw [if_pos hab, if_pos h4]
  · by_cases hpq : p ∈ e ∨ q ∈ e
    · have : e ≠ s(c, d) := by
        rintro rfl
        rcases hpq with h' | h' <;> rcases Sym2.mem_iff.mp h' with h'' | h'' <;>
          first | exact hc.1 h''.symm | exact hc.2 h''.symm | exact hd.1 h''.symm | exact hd.2 h''.symm
      have h4 : a ∈ e ∨ b ∈ e ∨ p ∈ e ∨ q ∈ e := by tauto
      rw [if_neg hab, if_pos hpq, if_pos h4, if_neg this]
    · have : ¬ (a ∈ e ∨ b ∈ e ∨ p ∈ e ∨ q ∈ e) := by tauto
      rw [if_neg hab, if_neg hpq, if_neg this]

/-! ## Stuck pairs -/

/-- **A stuck pair** `{a, b}` with `n ∈ {3, 4}` bonds: every further bond of `a` and of `b` goes to `d`, with
multiplicity `4 - n` (so for `n = 3` the two externals coincide, for `n = 4` there are none). -/
def Stuck (G : UMultigraph V) (a b : V) (n : ℕ) (d : V) : Prop :=
  a ≠ b ∧ d ≠ a ∧ d ≠ b ∧ 3 ≤ n ∧ n ≤ 4 ∧
    (∀ x, G.mult s(a, x) = if x = b then n else if x = d then 4 - n else 0) ∧
    (∀ x, G.mult s(b, x) = if x = a then n else if x = d then 4 - n else 0)

theorem Stuck.swap {G : UMultigraph V} {a b d : V} {n : ℕ} (h : Stuck G a b n d) : Stuck G b a n d :=
  ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2, h.2.2.2.2.2.1⟩

/-- No atom of a stuck pair lies in a (Y2) pair. -/
theorem Stuck.not_mem_a {G : UMultigraph V} {a b d : V} {n : ℕ} (h : Stuck G a b n d) {p q p' q' : V}
    (hP : IsY2Pair G p q p' q') : p ≠ a := by
  obtain ⟨hab, hda, hdb, hn3, hn4, ha, hb⟩ := h
  intro hpa
  have h3 : G.mult s(a, q) = 3 := hpa ▸ hP.mult_ab
  rw [ha] at h3
  by_cases hqb : q = b
  · -- the pair is `{a, b}` with `n = 3`; its externals would both be `d`
    have hn : n = 3 := by simpa [hqb] using h3
    have hc : G.mult s(a, p') = 1 := hpa ▸ hP.mult_ac
    have hd : G.mult s(b, q') = 1 := hqb ▸ hP.mult_bd
    rw [ha] at hc
    rw [hb] at hd
    have hp'b : p' ≠ b := hqb ▸ hP.c_ne_b
    have hq'a : q' ≠ a := hpa ▸ hP.d_ne_a
    have hp'd : p' = d := by by_contra hne; simp [hp'b, hne] at hc
    have hq'd : q' = d := by by_contra hne; simp [hq'a, hne] at hd
    exact hP.ext_ne (hp'd.trans hq'd.symm)
  · by_cases hqd : q = d
    · rw [if_neg hqb, if_pos hqd] at h3; omega
    · simp [hqb, hqd] at h3

theorem Stuck.not_mem {G : UMultigraph V} {a b d : V} {n : ℕ} (h : Stuck G a b n d) {p q p' q' : V}
    (hP : IsY2Pair G p q p' q') : p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b :=
  ⟨h.not_mem_a hP, h.swap.not_mem_a hP, h.not_mem_a hP.swap, h.swap.not_mem_a hP.swap⟩

/-- For `n = 3`, the common external `d` of a stuck pair lies in no (Y2) pair either. -/
theorem Stuck.not_mem_d {G : UMultigraph V} {a b d : V} (h : Stuck G a b 3 d) {p q p' q' : V}
    (hP : IsY2Pair G p q p' q') : p ≠ d := by
  obtain ⟨hab, hda, hdb, -, -, ha, hb⟩ := h
  intro hpd
  have hpa : G.mult s(p, a) = 1 := by rw [Sym2.eq_swap, ha, hpd]; simp [hdb]
  have hpb : G.mult s(p, b) = 1 := by rw [Sym2.eq_swap, hb, hpd]; simp [hda]
  have hpq := hP.mult_ab
  have hqa : q ≠ a := by rintro rfl; omega
  have hqb : q ≠ b := by rintro rfl; omega
  by_cases hpa' : a = p'
  · have := hP.a_other b (Ne.symm hqb) (by rw [← hpa']; exact hab.symm); omega
  · have := hP.a_other a (Ne.symm hqa) hpa'; omega

/-- A stuck pair survives every move. -/
theorem Stuck.y2Move {G : UMultigraph V} {a b d : V} {n : ℕ} (h : Stuck G a b n d) {p q p' q' : V}
    (hP : IsY2Pair G p q p' q') : Stuck (y2Move G p q p' q') a b n d := by
  obtain ⟨hpa, hpb, hqa, hqb⟩ := h.not_mem hP
  obtain ⟨hab, hda, hdb, hn3, hn4, ha, hb⟩ := h
  -- the externals of the move are not `a`, `b`
  have hext : ∀ x, x ≠ a → x ≠ b → G.mult s(x, a) = 0 ∨ x = d := by
    intro x hxa hxb
    rw [Sym2.eq_swap, ha]
    by_cases hxd : x = d
    · exact Or.inr hxd
    · left; simp [hxb, hxd]
  have hp'a : p' ≠ a := by
    intro h'
    have h1 := hP.mult_ac
    rw [h'] at h1
    rcases hext p hpa hpb with h2 | h2
    · omega
    · subst h2
      rw [Sym2.eq_swap, ha] at h1
      simp only [hdb, ite_false, ite_true] at h1
      have : n = 3 := by omega
      subst this
      exact (Stuck.not_mem_d ⟨hab, hda, hdb, le_refl 3, by omega, ha, hb⟩ hP) rfl
  have hq'a : q' ≠ a := by
    intro h'
    have h1 := hP.mult_bd
    rw [h'] at h1
    rcases hext q hqa hqb with h2 | h2
    · omega
    · subst h2
      rw [Sym2.eq_swap, ha] at h1
      simp only [hdb, ite_false, ite_true] at h1
      have : n = 3 := by omega
      subst this
      exact (Stuck.not_mem_d ⟨hab, hda, hdb, le_refl 3, by omega, ha, hb⟩ hP.swap) rfl
  have hext' : ∀ x, x ≠ a → x ≠ b → G.mult s(x, b) = 0 ∨ x = d := by
    intro x hxa hxb
    rw [Sym2.eq_swap, hb]
    by_cases hxd : x = d
    · exact Or.inr hxd
    · left; simp [hxa, hxd]
  have hp'b : p' ≠ b := by
    intro h'
    have h1 := hP.mult_ac
    rw [h'] at h1
    rcases hext' p hpa hpb with h2 | h2
    · omega
    · subst h2
      rw [Sym2.eq_swap, hb] at h1
      simp only [hda, ite_false, ite_true] at h1
      have : n = 3 := by omega
      subst this
      exact (Stuck.not_mem_d ⟨hab, hda, hdb, le_refl 3, by omega, ha, hb⟩ hP) rfl
  have hq'b : q' ≠ b := by
    intro h'
    have h1 := hP.mult_bd
    rw [h'] at h1
    rcases hext' q hqa hqb with h2 | h2
    · omega
    · subst h2
      rw [Sym2.eq_swap, hb] at h1
      simp only [hda, ite_false, ite_true] at h1
      have : n = 3 := by omega
      subst this
      exact (Stuck.not_mem_d ⟨hab, hda, hdb, le_refl 3, by omega, ha, hb⟩ hP.swap) rfl
  refine ⟨hab, hda, hdb, hn3, hn4, fun x => ?_, fun x => ?_⟩
  · rw [y2Move_mult]
    by_cases hx : p ∈ s(a, x) ∨ q ∈ s(a, x)
    · simp only [hx, ite_true]
      have hxpq : x = p ∨ x = q := by
        rcases hx with h' | h' <;> rcases Sym2.mem_iff.mp h' with h'' | h'' <;> tauto
      have hxb : x ≠ b := by rintro rfl; rcases hxpq with h' | h' <;> tauto
      by_cases hxd : x = d
      · subst hxd
        by_cases hn : n = 4
        · simp [hxb, hn]
        · have : n = 3 := by omega
          subst this
          rcases hxpq with h' | h'
          · exact absurd h'.symm (Stuck.not_mem_d ⟨hab, hda, hdb, le_refl 3, by omega, ha, hb⟩ hP)
          · exact absurd h'.symm (Stuck.not_mem_d ⟨hab, hda, hdb, le_refl 3, by omega, ha, hb⟩ hP.swap)
      · simp [hxb, hxd]
    · have hne : s(a, x) ≠ s(p', q') := by
        intro h'
        have : a ∈ s(p', q') := h' ▸ Sym2.mem_mk_left a x
        rcases Sym2.mem_iff.mp this with h'' | h'' <;> tauto
      simp only [hx, ite_false, hne, add_zero]
      exact ha x
  · rw [y2Move_mult]
    by_cases hx : p ∈ s(b, x) ∨ q ∈ s(b, x)
    · simp only [hx, ite_true]
      have hxpq : x = p ∨ x = q := by
        rcases hx with h' | h' <;> rcases Sym2.mem_iff.mp h' with h'' | h'' <;> tauto
      have hxa : x ≠ a := by rintro rfl; rcases hxpq with h' | h' <;> tauto
      by_cases hxd : x = d
      · subst hxd
        by_cases hn : n = 4
        · simp [hxa, hn]
        · have : n = 3 := by omega
          subst this
          rcases hxpq with h' | h'
          · exact absurd h'.symm (Stuck.not_mem_d ⟨hab, hda, hdb, le_refl 3, by omega, ha, hb⟩ hP)
          · exact absurd h'.symm (Stuck.not_mem_d ⟨hab, hda, hdb, le_refl 3, by omega, ha, hb⟩ hP.swap)
      · simp [hxa, hxd]
    · have hne : s(b, x) ≠ s(p', q') := by
        intro h'
        have : b ∈ s(p', q') := h' ▸ Sym2.mem_mk_left b x
        rcases Sym2.mem_iff.mp this with h'' | h'' <;> tauto
      simp only [hx, ite_false, hne, add_zero]
      exact hb x

/-- No path from a graph with a stuck pair reaches a doubled triangle. -/
theorem Stuck.not_y2Path {G T' : UMultigraph V} {a b d : V} {n : ℕ} (h : Stuck G a b n d)
    {ps : List (Sym2 V)} (hp : Y2Path G ps T') (hT : IsDoubledTriangle T') : False := by
  induction hp with
  | nil G =>
    have := doubledTriangle_mult_le hT s(a, b)
    rw [h.2.2.2.2.2.1] at this
    simp only [ite_true] at this
    have := h.2.2.2.1
    omega
  | cons hP _ ih => exact ih (h.y2Move hP) hT

/-- A (Y2) pair is not present in a doubled triangle. -/
theorem IsY2Pair.not_doubledTriangle {G : UMultigraph V} {a b c d : V} (h : IsY2Pair G a b c d)
    (hT : IsDoubledTriangle G) : False := by
  have := doubledTriangle_mult_le hT s(a, b); rw [h.mult_ab] at this; omega

end WaveTurbulence.TVine.Core
