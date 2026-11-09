/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Early

/-!
# Lemma E (M4 §5.2): early reduction of a triple bond, path-wise

`y2Path_early`: if `Q = {a, b}` is a (Y2) pair of `H` and `H →* T'` along `ps` (`T'` a doubled triangle), then
`Q` occurs exactly once in `ps` and `H/Q →* T'` along `ps.erase Q`. The proof follows M4 §5.2 (E0)–(E2) and REF-M4
§2.3: induction on the path; the first move `P₁` is `Q`, or disjoint from `Q` with
* (α) no bond between `P₁` and `Q`: the moves commute;
* (β) one bond: the externals are redirected (if they coincide, `Q` is `Stuck`);
* (γ) two bonds: `Q` becomes a stuck quadruple pair.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

/-! ## Multiplicities after a move, at a given atom -/

theorem mem_pair_iff {a b v x : V} (hva : v ≠ a) (hvb : v ≠ b) :
    (a ∈ s(v, x) ∨ b ∈ s(v, x)) ↔ (x = a ∨ x = b) := by
  simp only [Sym2.mem_iff]
  constructor
  · rintro ((h | h) | (h | h))
    · exact absurd h.symm hva
    · exact Or.inl h.symm
    · exact absurd h.symm hvb
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact Or.inl (Or.inr h.symm)
    · exact Or.inr (Or.inr h.symm)

/-- After a move at `{a, b}` (externals `c, d`), the bonds at an atom `v ∉ {a, b, c, d}`. -/
theorem y2Move_mult_far {H : UMultigraph V} {a b c d v : V} (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hvd : v ≠ d) (x : V) :
    (y2Move H a b c d).mult s(v, x) = if x = a ∨ x = b then 0 else H.mult s(v, x) := by
  rw [y2Move_mult]
  have hne : s(v, x) ≠ s(c, d) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
    exacts [hvc h1, hvd h1]
  by_cases hx : x = a ∨ x = b
  · rw [if_pos ((mem_pair_iff hva hvb).mpr hx), if_pos hx]
  · rw [if_neg (mt (mem_pair_iff hva hvb).mp hx), if_neg hx, if_neg hne, add_zero]

/-- After a move at `{a, b}` (externals `c, d`), the bonds at the external `c`. -/
theorem y2Move_mult_ext {H : UMultigraph V} {a b c d : V} (hca : c ≠ a) (hcb : c ≠ b) (x : V) :
    (y2Move H a b c d).mult s(c, x) =
      if x = a ∨ x = b then 0 else H.mult s(c, x) + if x = d then 1 else 0 := by
  rw [y2Move_mult]
  by_cases hx : x = a ∨ x = b
  · rw [if_pos ((mem_pair_iff hca hcb).mpr hx), if_pos hx]
  · rw [if_neg (mt (mem_pair_iff hca hcb).mp hx), if_neg hx]
    congr 1
    by_cases hxd : x = d
    · subst hxd; simp
    · rw [if_neg hxd, if_neg]; rw [Sym2.congr_right]; exact hxd

/-- After a move at `{a, b}` (externals `c, d`), the bonds at the external `d`. -/
theorem y2Move_mult_ext' {H : UMultigraph V} {a b c d : V} (hda : d ≠ a) (hdb : d ≠ b) (x : V) :
    (y2Move H a b c d).mult s(d, x) =
      if x = a ∨ x = b then 0 else H.mult s(d, x) + if x = c then 1 else 0 := by
  rw [← y2Move_swap, y2Move_mult_ext hdb hda]
  simp only [or_comm]

/-! ## The three cases -/

/-- Case (α): no bond joins the two pairs; the moves commute. -/
theorem early_alpha {H : UMultigraph V} {a b c d p q p' q' : V} (hQ : IsY2Pair H a b c d)
    (hP : IsY2Pair H p q p' q') (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b)
    (hp'a : p' ≠ a) (hp'b : p' ≠ b) (hq'a : q' ≠ a) (hq'b : q' ≠ b) :
    IsY2Pair (y2Move H p q p' q') a b c d ∧ IsY2Pair (y2Move H a b c d) p q p' q' ∧
      y2Move (y2Move H a b c d) p q p' q' = y2Move (y2Move H p q p' q') a b c d := by
  -- the externals of `Q` avoid `P` and vice versa
  have hcp : c ≠ p := by
    intro h; have h1 := hQ.mult_ac; rw [h, Sym2.eq_swap, hP.a_other a (Ne.symm hqa) (Ne.symm hp'a)] at h1
    omega
  have hcq : c ≠ q := by
    intro h; have h1 := hQ.mult_ac; rw [h, Sym2.eq_swap, hP.b_other a (Ne.symm hpa) (Ne.symm hq'a)] at h1
    omega
  have hdp : d ≠ p := by
    intro h; have h1 := hQ.mult_bd; rw [h, Sym2.eq_swap, hP.a_other b (Ne.symm hqb) (Ne.symm hp'b)] at h1
    omega
  have hdq : d ≠ q := by
    intro h; have h1 := hQ.mult_bd; rw [h, Sym2.eq_swap, hP.b_other b (Ne.symm hpb) (Ne.symm hq'b)] at h1
    omega
  have h1 : IsY2Pair (y2Move H p q p' q') a b c d := by
    refine IsY2Pair.of_mult hQ.ne hQ.ext_ne hQ.c_ne_a hQ.c_ne_b hQ.d_ne_a hQ.d_ne_b (fun x => ?_) (fun x => ?_)
    · rw [y2Move_mult_far (Ne.symm hpa) (Ne.symm hqa) (Ne.symm hp'a) (Ne.symm hq'a), hQ.mult_a]
      by_cases hx : x = p ∨ x = q
      · rw [if_pos hx]
        rcases hx with rfl | rfl <;> simp [*, Ne.symm hpb, Ne.symm hqb, Ne.symm hcp, Ne.symm hcq]
      · rw [if_neg hx]
    · rw [y2Move_mult_far (Ne.symm hpb) (Ne.symm hqb) (Ne.symm hp'b) (Ne.symm hq'b), hQ.mult_b]
      by_cases hx : x = p ∨ x = q
      · rw [if_pos hx]
        rcases hx with rfl | rfl <;> simp [*, Ne.symm hdp, Ne.symm hdq]
      · rw [if_neg hx]
  have h2 : IsY2Pair (y2Move H a b c d) p q p' q' := by
    refine IsY2Pair.of_mult hP.ne hP.ext_ne hP.c_ne_a hP.c_ne_b hP.d_ne_a hP.d_ne_b (fun x => ?_) (fun x => ?_)
    · rw [y2Move_mult_far hpa hpb (Ne.symm hcp) (Ne.symm hdp), hP.mult_a]
      by_cases hx : x = a ∨ x = b
      · rw [if_pos hx]
        rcases hx with rfl | rfl <;> simp [*, Ne.symm hqa, Ne.symm hqb, Ne.symm hp'a, Ne.symm hp'b]
      · rw [if_neg hx]
    · rw [y2Move_mult_far hqa hqb (Ne.symm hcq) (Ne.symm hdq), hP.mult_b]
      by_cases hx : x = a ∨ x = b
      · rw [if_pos hx]
        rcases hx with rfl | rfl <;> simp [*, Ne.symm hq'a, Ne.symm hq'b, Ne.symm hpa, Ne.symm hpb]
      · rw [if_neg hx]
  refine ⟨h1, h2, ext ?_ fun e => ?_⟩
  · rw [y2Move_verts h2, y2Move_verts hQ, y2Move_verts h1, y2Move_verts hP]
    ext x; simp only [Finset.mem_erase]; tauto
  · rw [y2Move_y2Move_mult h2, y2Move_y2Move_mult h1]
    by_cases h : a ∈ e ∨ b ∈ e ∨ p ∈ e ∨ q ∈ e
    · rw [if_pos (by tauto), if_pos h]
    · rw [if_neg (by tauto), if_neg h]; ring

/-- Case (β): exactly one bond `p–a` joins the pairs (`c = p`, `p' = a`); `q' ≠ d` gives the commutation,
`q' = d` makes `Q` stuck. -/
theorem early_beta {H : UMultigraph V} {a b d p q q' : V} (hQ : IsY2Pair H a b p d)
    (hP : IsY2Pair H p q a q') (hq'b : q' ≠ b) :
    (q' = d → Stuck (y2Move H p q a q') a b 3 d) ∧
    (q' ≠ d → IsY2Pair (y2Move H p q a q') a b q' d ∧ IsY2Pair (y2Move H a b p d) p q d q' ∧
      y2Move (y2Move H a b p d) p q d q' = y2Move (y2Move H p q a q') a b q' d) := by
  have hpa : p ≠ a := hQ.c_ne_a
  have hpb : p ≠ b := hQ.c_ne_b
  have hpd : p ≠ d := hQ.ext_ne
  have hq'a : q' ≠ a := hP.ext_ne.symm
  have hqa : q ≠ a := by
    intro h; have h1 := hP.mult_ab; rw [h, Sym2.eq_swap, hQ.mult_ac] at h1; omega
  have hqb : q ≠ b := by
    intro h; have h1 := hP.mult_ab; rw [h, Sym2.eq_swap, hQ.mult_b] at h1
    simp [hpa, hpd] at h1
  have hdq : d ≠ q := by
    intro h; have h1 := hQ.mult_bd; rw [h, Sym2.eq_swap, hP.b_other b (Ne.symm hpb) (Ne.symm hq'b)] at h1
    omega
  have hq'p : q' ≠ p := hP.d_ne_a
  have hq'q : q' ≠ q := hP.d_ne_b
  -- bonds at `a` and `b` after the move at `P`
  have ha : ∀ x, (y2Move H p q a q').mult s(a, x) = if x = b then 3 else if x = q' then 1 else 0 := by
    intro x
    rw [y2Move_mult_ext (Ne.symm hpa) (Ne.symm hqa), hQ.mult_a]
    by_cases hx : x = p ∨ x = q
    · rw [if_pos hx]
      rcases hx with rfl | rfl <;> simp [hpb, hqb, hq'p, hq'q, Ne.symm hpb, Ne.symm hqb, Ne.symm hq'p, Ne.symm hq'q]
    · rw [if_neg hx]
      have hxp : x ≠ p := fun h => hx (Or.inl h)
      by_cases hxb : x = b
      · subst hxb; simp [Ne.symm hq'b]
      · by_cases hxq' : x = q'
        · subst hxq'; simp [hxb, hxp]
        · simp [hxb, hxp, hxq']
  have hb : ∀ x, (y2Move H p q a q').mult s(b, x) = if x = a then 3 else if x = d then 1 else 0 := by
    intro x
    have hbq' : b ≠ q' := Ne.symm hq'b
    rw [y2Move_mult_far (Ne.symm hpb) (Ne.symm hqb) hQ.ne.symm hbq', hQ.mult_b]
    by_cases hx : x = p ∨ x = q
    · rw [if_pos hx]
      rcases hx with rfl | rfl <;> simp [hpa, hpd, hqa, Ne.symm hdq]
    · rw [if_neg hx]
  refine ⟨fun hq'd => ?_, fun hq'd => ?_⟩
  · subst hq'd
    refine ⟨hQ.ne, hQ.d_ne_a, hQ.d_ne_b, le_refl 3, by omega, fun x => ?_, fun x => ?_⟩
    · rw [ha x]
    · rw [hb x]
  have h1 : IsY2Pair (y2Move H p q a q') a b q' d :=
    IsY2Pair.of_mult hQ.ne hq'd hq'a hq'b hQ.d_ne_a hQ.d_ne_b ha hb
  have h2 : IsY2Pair (y2Move H a b p d) p q d q' := by
    refine IsY2Pair.of_mult hP.ne (Ne.symm hq'd) (Ne.symm hpd) hdq hq'p hq'q ?_ ?_
    · intro x
      rw [y2Move_mult_ext hpa hpb, hP.mult_a]
      by_cases hx : x = a ∨ x = b
      · rw [if_pos hx]
        rcases hx with rfl | rfl <;> simp [hqa, hqb, Ne.symm hqa, Ne.symm hqb, hQ.d_ne_a, hQ.d_ne_b,
          hQ.d_ne_a.symm, hQ.d_ne_b.symm, hQ.ne]
      · rw [if_neg hx]
        have hxa : x ≠ a := fun h => hx (Or.inl h)
        by_cases hxq : x = q
        · subst hxq; simp [hxa, hdq.symm]
        · by_cases hxd : x = d
          · subst hxd; simp [hxq, hxa]
          · simp [hxq, hxa, hxd]
    · intro x
      rw [y2Move_mult_far hqa hqb hP.ne.symm hdq.symm, hP.mult_b]
      by_cases hx : x = a ∨ x = b
      · rw [if_pos hx]
        rcases hx with rfl | rfl <;> simp [hpa, hpb, hq'a.symm, hq'b.symm, Ne.symm hpa, Ne.symm hpb]
      · rw [if_neg hx]
  refine ⟨h1, h2, ext ?_ fun e => ?_⟩
  · rw [y2Move_verts h2, y2Move_verts hQ, y2Move_verts h1, y2Move_verts hP]
    ext x; simp only [Finset.mem_erase]; tauto
  · rw [y2Move_y2Move_mult h2, y2Move_y2Move_mult h1]
    by_cases h : a ∈ e ∨ b ∈ e ∨ p ∈ e ∨ q ∈ e
    · rw [if_pos (by tauto), if_pos h]
    · rw [if_neg (by tauto), if_neg h]
      have hep : e ≠ s(p, d) := fun h' => h (Or.inr (Or.inr (Or.inl (h' ▸ Sym2.mem_mk_left p d))))
      have hea : e ≠ s(a, q') := fun h' => h (Or.inl (h' ▸ Sym2.mem_mk_left a q'))
      rw [if_neg hep, if_neg hea, Sym2.eq_swap (a := d)]

/-- Case (γ): two bonds join the pairs (`p' = a`, `q' = b`); `Q` becomes a stuck quadruple pair. -/
theorem early_gamma {H : UMultigraph V} {a b c d p q : V} (hQ : IsY2Pair H a b c d)
    (hP : IsY2Pair H p q a b) : Stuck (y2Move H p q a b) a b 4 c := by
  have hpc : p = c := by
    have h1 := hQ.mult_a p
    rw [Sym2.eq_swap, hP.mult_ac] at h1
    by_contra hpc
    by_cases hpb : p = b
    · rw [if_pos hpb] at h1; omega
    · rw [if_neg hpb, if_neg hpc] at h1; omega
  have hqd : q = d := by
    have h1 := hQ.mult_b q
    rw [Sym2.eq_swap, hP.mult_bd] at h1
    by_contra hqd
    by_cases hqa : q = a
    · rw [if_pos hqa] at h1; omega
    · rw [if_neg hqa, if_neg hqd] at h1; omega
  subst hpc; subst hqd
  refine ⟨hQ.ne, hQ.c_ne_a, hQ.c_ne_b, by omega, le_refl 4, fun x => ?_, fun x => ?_⟩
  · rw [y2Move_mult_ext hP.c_ne_a hP.c_ne_b, hQ.mult_a]
    by_cases hx : x = p ∨ x = q
    · rw [if_pos hx]
      rcases hx with rfl | rfl <;> simp [hQ.c_ne_b, hQ.d_ne_b]
    · rw [if_neg hx]
      have hxp : x ≠ p := fun h => hx (Or.inl h)
      by_cases hxb : x = b
      · subst hxb; simp
      · simp [hxb, hxp]
  · rw [y2Move_mult_ext' hP.d_ne_a hP.d_ne_b, hQ.mult_b]
    by_cases hx : x = p ∨ x = q
    · rw [if_pos hx]
      rcases hx with rfl | rfl <;> simp [hQ.c_ne_a, hQ.d_ne_a, hQ.ext_ne]
    · rw [if_neg hx]
      have hxq : x ≠ q := fun h => hx (Or.inr h)
      by_cases hxa : x = a
      · subst hxa; simp
      · simp [hxa, hxq]

/-! ## Lemma E -/

/-- Assembly of the inductive step when the first move `P` is not `Q`. -/
private theorem early_cons {H H₁ T' : UMultigraph V} {a b c d p q p₁ q₁ c₁ d₁ : V} {rest : List (Sym2 V)}
    (hne : s(p, q) ≠ s(a, b)) (hP' : IsY2Pair (y2Move H a b c d) p q p₁ q₁)
    (hcomm : y2Move (y2Move H a b c d) p q p₁ q₁ = y2Move H₁ a b c₁ d₁)
    (ih : rest.count s(a, b) = 1 ∧ Y2Path (y2Move H₁ a b c₁ d₁) (rest.erase s(a, b)) T') :
    (s(p, q) :: rest).count s(a, b) = 1 ∧
      Y2Path (y2Move H a b c d) ((s(p, q) :: rest).erase s(a, b)) T' := by
  refine ⟨?_, ?_⟩
  · rw [List.count_cons, ih.1]; simp [hne]
  · rw [List.erase_cons_tail (by simpa using hne)]
    exact .cons hP' (hcomm ▸ ih.2)

/-- The inductive step for a first move `P` disjoint from `Q`, with `q' ∉ Q` and `p' = a` or `p' ∉ Q`. -/
private theorem early_step {H T' : UMultigraph V} {a b c d p q p' q' : V} {rest : List (Sym2 V)}
    (hT : IsDoubledTriangle T') (hQ : IsY2Pair H a b c d) (hP : IsY2Pair H p q p' q')
    (hpq : s(p, q) ≠ s(a, b)) (hq'a : q' ≠ a) (hq'b : q' ≠ b) (hp' : p' = a ∨ (p' ≠ a ∧ p' ≠ b))
    (hrest : Y2Path (y2Move H p q p' q') rest T')
    (ih : ∀ {a' b' c' d' : V}, IsY2Pair (y2Move H p q p' q') a' b' c' d' →
      rest.count s(a', b') = 1 ∧
        Y2Path (y2Move (y2Move H p q p' q') a' b' c' d') (rest.erase s(a', b')) T') :
    (s(p, q) :: rest).count s(a, b) = 1 ∧
      Y2Path (y2Move H a b c d) ((s(p, q) :: rest).erase s(a, b)) T' := by
  obtain ⟨hpa, hpb, hqa, hqb⟩ := hQ.disj hP hpq
  rcases hp' with hp'a | ⟨hp'a, hp'b⟩
  · -- (β): one bond `p–a`, so `c = p`
    subst p'
    have hcp : c = p := by
      have h1 := hQ.mult_a p
      rw [Sym2.eq_swap, hP.mult_ac] at h1
      by_contra hcp
      rw [if_neg hpb, if_neg (Ne.symm hcp)] at h1
      omega
    subst c
    by_cases hq'd : q' = d
    · exact (((early_beta hQ hP hq'b).1 hq'd).not_y2Path hrest hT).elim
    · obtain ⟨h1, h2, hcomm⟩ := (early_beta hQ hP hq'b).2 hq'd
      exact early_cons hpq h2 hcomm (ih h1)
  · -- (α): no bond between the pairs
    obtain ⟨h1, h2, hcomm⟩ := early_alpha hQ hP hpa hpb hqa hqb hp'a hp'b hq'a hq'b
    exact early_cons hpq h2 hcomm (ih h1)

/-- **Lemma E** (M4 §5.2, REF-M4 claim 4): a (Y2) pair `Q = {a, b}` of `H` occurs exactly once on every (Y2)-path
from `H` to a doubled triangle, and deleting that move gives a (Y2)-path from `H/Q`. -/
theorem y2Path_early {H T' : UMultigraph V} {ps : List (Sym2 V)} (hp : Y2Path H ps T')
    (hT : IsDoubledTriangle T') {a b c d : V} (hQ : IsY2Pair H a b c d) :
    ps.count s(a, b) = 1 ∧ Y2Path (y2Move H a b c d) (ps.erase s(a, b)) T' := by
  induction hp generalizing a b c d with
  | nil G => exact (hQ.not_doubledTriangle hT).elim
  | @cons H T' p q p' q' rest hP hrest ih =>
    replace ih := @ih hT
    by_cases hpq : s(p, q) = s(a, b)
    · -- the first move is `Q` itself
      have hmove : y2Move H p q p' q' = y2Move H a b c d := by
        rcases Sym2.eq_iff.mp hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · obtain ⟨h1, h2⟩ := hQ.ext_eq hP; rw [h1, h2]
        · obtain ⟨h1, h2⟩ := hQ.ext_eq hP.swap; rw [← y2Move_swap, h1, h2]
      have hnot : s(a, b) ∉ rest := by
        intro hm
        have hav := hrest.mem_verts _ hm a (Sym2.mem_mk_left a b)
        have ha : a ∈ s(p, q) := by rw [hpq]; exact Sym2.mem_mk_left a b
        obtain ⟨h1, h2⟩ := y2Move_verts_sub hav
        rcases Sym2.mem_iff.mp ha with h | h
        exacts [h1 h, h2 h]
      refine ⟨by rw [hpq, List.count_cons_self, List.count_eq_zero.mpr hnot], ?_⟩
      rw [hpq, List.erase_cons_head]
      exact hmove ▸ hrest
    · obtain ⟨hpa, hpb, hqa, hqb⟩ := hQ.disj hP hpq
      by_cases hq'Q : q' = a ∨ q' = b
      · by_cases hp'Q : p' = a ∨ p' = b
        · -- (γ): two bonds join the pairs
          exfalso
          rcases hp'Q with h | h
          · have hq' : q' = b := hq'Q.resolve_left fun h' => hP.ext_ne (h.trans h'.symm)
            subst h; subst hq'
            exact (early_gamma hQ hP).not_y2Path hrest hT
          · have hq' : q' = a := hq'Q.resolve_right fun h' => hP.ext_ne (h.trans h'.symm)
            subst h; subst hq'
            exact (early_gamma hQ.swap hP).not_y2Path hrest hT
        · -- one bond, at `q`: read `P` the other way round
          replace hp'Q : p' ≠ a ∧ p' ≠ b := not_or.mp hp'Q
          have hP' := hP.swap
          have hrest' : Y2Path (y2Move H q p q' p') rest T' := by rw [y2Move_swap H p q p' q']; exact hrest
          have ih' : ∀ {a' b' c' d' : V}, IsY2Pair (y2Move H q p q' p') a' b' c' d' →
              rest.count s(a', b') = 1 ∧
                Y2Path (y2Move (y2Move H q p q' p') a' b' c' d') (rest.erase s(a', b')) T' := by
            intro a' b' c' d' hh
            rw [y2Move_swap H p q p' q'] at hh ⊢
            exact ih hh
          have hqp : s(q, p) ≠ s(a, b) := fun h => hpq (Sym2.eq_swap.trans h)
          have hsw : s(q, p) = s(p, q) := Sym2.eq_swap
          rcases hq'Q with hq'a | hq'b
          · have := early_step hT hQ hP' hqp hp'Q.1 hp'Q.2 (Or.inl hq'a) hrest' ih'
            rwa [hsw] at this
          · have := early_step hT hQ.swap hP' (fun h => hqp (h.trans Sym2.eq_swap)) hp'Q.2 hp'Q.1
              (Or.inl hq'b) hrest' ih'
            rw [hsw, show s(b, a) = s(a, b) from Sym2.eq_swap, y2Move_swap H a b c d] at this
            exact this
      · replace hq'Q : q' ≠ a ∧ q' ≠ b := not_or.mp hq'Q
        by_cases hp'b : p' = b
        · have := early_step hT hQ.swap hP (fun h => hpq (h.trans Sym2.eq_swap)) hq'Q.2 hq'Q.1
            (Or.inl hp'b) hrest ih
          rw [show s(b, a) = s(a, b) from Sym2.eq_swap, y2Move_swap H a b c d] at this
          exact this
        · by_cases hp'a : p' = a
          · exact early_step hT hQ hP hpq hq'Q.1 hq'Q.2 (Or.inl hp'a) hrest ih
          · exact early_step hT hQ hP hpq hq'Q.1 hq'Q.2 (Or.inr ⟨hp'a, hp'b⟩) hrest ih

end WaveTurbulence.TVine.Core
