/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Lemma5Del

/-!
# Lemma 5″: rung insertion as path surgery (M4 §5.3; REF-M4 claim 6 with repair R3)

`y2Path_insertRung`: if `R = {a, b}` carries rung data in `C` and `C/[μ]R →* T'` (a doubled triangle) along `ps`,
then `C →* T'` along `ps` with the move `R` inserted at some position `j` (right after the collapse).

The proof follows REF-M4 R3: every triple pair of `C/[μ]R` lies in one pole; a move with no cross-bond external is
mirrored verbatim (case (i)); one with one cross-bond external is valid in `C` with external `a` (case (ii)); one with
both externals cross bonds is the collapse `P = {xm, ym}`, after which `R` is a (Y2) pair (case (iii)).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

/-- The cross bonds at the rail end `xm` (when `xm ≠ ym`): one, to the partner of `xm`. -/
theorem rungAdds_count_xm {xm xp ym yp : V} (hm : xm ≠ ym) (hxp : xm ≠ xp) (hyp : xm ≠ yp) (μ : Bool) (x : V) :
    (rungAdds xm xp ym yp μ).count s(xm, x) = if x = (if μ then yp else xp) then 1 else 0 := by
  cases μ
  · simp only [rungAdds, Bool.false_eq_true, if_false, count_pair, Sym2.congr_right]
    have : s(xm, x) ≠ s(ym, yp) := by
      intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
      exacts [hm h1, hyp h1]
    rw [if_neg this, add_zero]
  · simp only [rungAdds, if_true, count_pair, Sym2.congr_right]
    have : s(xm, x) ≠ s(xp, ym) := by
      intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
      exacts [hxp h1, hm h1]
    rw [if_neg this, add_zero]

/-- The cross bonds at `xm = ym`: one to each of `xp`, `yp`. -/
theorem rungAdds_count_xm_eq {xm xp yp : V} (hxp : xm ≠ xp) (hyp : xm ≠ yp) (μ : Bool) (x : V) :
    (rungAdds xm xp xm yp μ).count s(xm, x) = (if x = yp then 1 else 0) + (if x = xp then 1 else 0) := by
  cases μ
  · simp only [rungAdds, Bool.false_eq_true, if_false, count_pair, Sym2.congr_right]; ring
  · simp only [rungAdds, if_true, count_pair, Sym2.congr_right, Sym2.eq_swap (a := xp) (b := xm)]

/-- The conclusion of Lemma 5″: `R` inserted at some position. -/
def InsConcl (C T' : UMultigraph V) (a b : V) (ps : List (Sym2 V)) : Prop :=
  ∃ j ≤ ps.length, Y2Path C (ps.take j ++ s(a, b) :: ps.drop j) T'

theorem InsConcl.swap {C T' : UMultigraph V} {a b : V} {ps : List (Sym2 V)} (h : InsConcl C T' b a ps) :
    InsConcl C T' a b ps := by
  rwa [InsConcl, show s(b, a) = s(a, b) from Sym2.eq_swap] at h

theorem InsConcl.cons {C C₁ T' : UMultigraph V} {a b p q p' q' : V} {rest : List (Sym2 V)}
    (hP : IsY2Pair C p q p' q') (hC₁ : y2Move C p q p' q' = C₁) (h : InsConcl C₁ T' a b rest) :
    InsConcl C T' a b (s(p, q) :: rest) := by
  obtain ⟨j, hj, hpath⟩ := h
  refine ⟨j + 1, by simp; omega, ?_⟩
  simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
  exact .cons hP (hC₁ ▸ hpath)

/-- The induction hypothesis of Lemma 5″ at the graph `D₁` after the first move. -/
def InsIH (D₁ T' : UMultigraph V) (rest : List (Sym2 V)) : Prop :=
  ∀ {C : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V} {μ : Bool},
    RungCore C a b xm xp ym yp Km Kp → rungDel C a b xm xp ym yp μ = D₁ → InsConcl C T' a b rest

section Main

variable {C T' : UMultigraph V} {a b xm xp ym yp p q p' q' : V} {Km Kp : Finset V} {rest : List (Sym2 V)}
  {μ : Bool}

/-- The atoms of the deleted graph are the poles. -/
theorem RungCore.mem_poles_of_rungDel (hR : RungCore C a b xm xp ym yp Km Kp) {x : V}
    (hx : x ∈ (rungDel C a b xm xp ym yp μ).verts) : x ∈ Km ∨ x ∈ Kp := by
  rw [hR.verts_rungDel, ← hR.union] at hx
  exact Finset.mem_union.mp hx

/-- Between the poles, the deleted graph has only the added bonds. -/
theorem RungCore.rungDel_mult_cross (hR : RungCore C a b xm xp ym yp Km Kp) {u w : V} (hu : u ∈ Km)
    (hw : w ∈ Kp) : (rungDel C a b xm xp ym yp μ).mult s(u, w) = (rungAdds xm xp ym yp μ).count s(u, w) := by
  obtain ⟨hua, hub⟩ := hR.ne_of_mem (Or.inl hu)
  obtain ⟨hwa, hwb⟩ := hR.ne_of_mem (Or.inr hw)
  rw [rungDel, splice_mult_at _ _ hua hub, if_neg (by tauto), hR.noBond u hu w hw, zero_add]

/-- The rail end `p = xm` of a (Y2) pair of `C/[μ]R`: `xm ≠ ym`, the external of `p` is its partner, and the bonds
of `p` in `C` are `q` (triple) and `a`. -/
theorem ins_rail (hR : RungCore C a b p xp ym yp Km Kp) (hP : IsY2Pair (rungDel C a b p xp ym yp μ) p q p' q')
    (hq : q ∈ Km) :
    ym ≠ p ∧ p' = (if μ then yp else xp) ∧
      ∀ x, C.mult s(p, x) = if x = q then 3 else if x = a then 1 else 0 := by
  have hp := hR.xm_mem
  have hpP : p ∉ Kp := fun h => hR.not_mem_both hp h
  have hqP : q ∉ Kp := fun h => hR.not_mem_both hq h
  have hpxp : p ≠ xp := fun h => hpP (h ▸ hR.xp_mem)
  have hpyp : p ≠ yp := fun h => hpP (h ▸ hR.yp_mem)
  obtain ⟨hpa, hpb⟩ := hR.ne_of_mem (Or.inl hp)
  -- `D`-bonds at `p` towards `Kp` are the added bonds
  have hcross : ∀ w ∈ Kp, (rungDel C a b p xp ym yp μ).mult s(p, w) =
      (rungAdds p xp ym yp μ).count s(p, w) := fun w hw => hR.rungDel_mult_cross hp hw
  have hother : ∀ w, w ≠ q → w ≠ p' → (rungDel C a b p xp ym yp μ).mult s(p, w) = 0 := hP.a_other
  have hymp : ym ≠ p := by
    intro hym
    subst hym
    have h1 := hcross yp hR.yp_mem
    have h2 := hcross xp hR.xp_mem
    rw [rungAdds_count_xm_eq hpxp hpyp] at h1 h2
    have hyq : yp ≠ q := fun h => hqP (h ▸ hR.yp_mem)
    have hxq : xp ≠ q := fun h => hqP (h ▸ hR.xp_mem)
    by_cases hy : yp = p'
    · by_cases hx : xp = p'
      · have h3 := hP.mult_ac
        rw [← hx] at h3
        rw [h3] at h2
        simp [hx, hy] at h2
      · rw [hother xp hxq hx, if_pos (rfl : xp = xp)] at h2; omega
    · rw [hother yp hyq hy, if_pos (rfl : yp = yp)] at h1; omega
  have hcnt := rungAdds_count_xm (Ne.symm hymp) hpxp hpyp μ
  set z := if μ then yp else xp with hz
  have hzK : z ∈ Kp := by cases μ <;> simp [hz, hR.xp_mem, hR.yp_mem]
  have hzq : z ≠ q := fun h => hqP (h ▸ hzK)
  have hp'z : p' = z := by
    by_contra hne
    have h1 := hcross z hzK
    rw [hother z hzq (Ne.symm hne), hcnt] at h1
    simp at h1
  obtain ⟨hqa, hqb⟩ := hR.ne_of_mem (Or.inl hq)
  refine ⟨hymp, hp'z, fun x => ?_⟩
  by_cases hxa : x = a
  · rw [hxa, Sym2.eq_swap, hR.mult_a]; simp [hpb, Ne.symm hqa]
  by_cases hxb : x = b
  · rw [hxb, Sym2.eq_swap, hR.mult_b]; simp [hpa, Ne.symm hR.ne, Ne.symm hymp, hpyp, Ne.symm hqb]
  have hD := hP.mult_a x
  rw [rungDel, splice_mult_at _ _ hpa hpb, if_neg (by tauto), hcnt, hp'z] at hD
  rw [if_neg hxa]
  by_cases hxq : x = q
  · subst hxq; simp [hzq.symm] at hD; simp [hD]
  · by_cases hxz : x = z
    · subst hxz; simp [hxq] at hD; simp [hxq, hD]
    · simp [hxq, hxz] at hD; simp [hxq, hD]

end Main

/-- Distinct atoms of a doubled triangle are joined by a double bond. -/
theorem doubledTriangle_mult_of_ne {G : UMultigraph V} (hT : IsDoubledTriangle G) {x y : V} (hx : x ∈ G.verts)
    (hy : y ∈ G.verts) (hxy : x ≠ y) : G.mult s(x, y) = 2 := by
  obtain ⟨u, v, w, huv, huw, hvw, hV, hm⟩ := hT
  rw [hV] at hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rw [hm]
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first | exact absurd rfl hxy | simp [Sym2.eq_swap]

/-- A doubled triangle has a third atom besides any two. -/
theorem doubledTriangle_third {G : UMultigraph V} (hT : IsDoubledTriangle G) (x y : V) :
    ∃ t ∈ G.verts, t ≠ x ∧ t ≠ y := by
  obtain ⟨u, v, w, huv, huw, hvw, hV, -⟩ := hT
  rw [hV]
  by_cases h1 : u ≠ x ∧ u ≠ y
  · exact ⟨u, by simp, h1⟩
  by_cases h2 : v ≠ x ∧ v ≠ y
  · exact ⟨v, by simp, h2⟩
  have h1' : u = x ∨ u = y := by tauto
  have h2' : v = x ∨ v = y := by tauto
  refine ⟨w, by simp, fun h => ?_, fun h => ?_⟩ <;>
    rcases h1' with h3 | h3 <;> rcases h2' with h4 | h4 <;>
    first
    | exact huw (h3.trans h.symm) | exact hvw (h4.trans h.symm) | exact huv (h3.trans h4.symm)

/-- A graph with rung data deleted is not a doubled triangle: its two poles are joined by only two bond copies. -/
theorem RungCore.rungDel_not_doubledTriangle {C : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}
    (hR : RungCore C a b xm xp ym yp Km Kp) (μ : Bool) : ¬ IsDoubledTriangle (rungDel C a b xm xp ym yp μ) := by
  intro hT
  set D := rungDel C a b xm xp ym yp μ
  have hV : ∀ x, x ∈ D.verts ↔ x ∈ Km ∨ x ∈ Kp := by
    intro x; show x ∈ (rungDel C a b xm xp ym yp μ).verts ↔ _
    rw [hR.verts_rungDel, ← hR.union, Finset.mem_union]
  have hxm : xm ∈ D.verts := (hV xm).mpr (Or.inl hR.xm_mem)
  have hxp : xp ∈ D.verts := (hV xp).mpr (Or.inr hR.xp_mem)
  have hne : xm ≠ xp := hR.xm_ne_xp
  have h2 := doubledTriangle_mult_of_ne hT hxm hxp hne
  rw [show D = rungDel C a b xm xp ym yp μ from rfl, hR.rungDel_mult_cross hR.xm_mem hR.xp_mem] at h2
  have hcard : Multiset.card (rungAdds xm xp ym yp μ) = 2 := by cases μ <;> rfl
  have hall : ∀ f ∈ rungAdds xm xp ym yp μ, s(xm, xp) = f :=
    Multiset.count_eq_card.mp (h2.trans hcard.symm)
  obtain ⟨t, ht, htm, htp⟩ := doubledTriangle_third hT xm xp
  rcases (hV t).mp ht with htK | htK
  · have h3 := doubledTriangle_mult_of_ne hT ht hxp htp
    rw [show D = rungDel C a b xm xp ym yp μ from rfl, hR.rungDel_mult_cross htK hR.xp_mem,
      Multiset.count_eq_zero.mpr] at h3
    · omega
    · intro hm; have := hall _ hm
      rcases Sym2.eq_iff.mp this with ⟨h, _⟩ | ⟨h, _⟩
      · exact htm h.symm
      · exact hR.not_mem_both hR.xm_mem (h ▸ hR.xp_mem)
  · have h3 := doubledTriangle_mult_of_ne hT hxm ht (Ne.symm htm)
    rw [show D = rungDel C a b xm xp ym yp μ from rfl, hR.rungDel_mult_cross hR.xm_mem htK,
      Multiset.count_eq_zero.mpr] at h3
    · omega
    · intro hm; have := hall _ hm
      rcases Sym2.eq_iff.mp this with ⟨_, h⟩ | ⟨h, _⟩
      · exact htp h.symm
      · exact hR.not_mem_both hR.xm_mem (h ▸ htK)

section Steps

variable {C T' : UMultigraph V} {a b xm xp ym yp p q p' q' : V} {Km Kp : Finset V} {rest : List (Sym2 V)}
  {μ : Bool}

/-- The three normalised cases of the inductive step of Lemma 5″, for a first move inside `Km`. -/
private theorem insert_core (hR : RungCore C a b xm xp ym yp Km Kp)
    (hP : IsY2Pair (rungDel C a b xm xp ym yp μ) p q p' q') (hp : p ∈ Km) (hq : q ∈ Km)
    (hcase : (p ≠ xm ∧ p ≠ ym ∧ q ≠ xm ∧ q ≠ ym) ∨ (p = xm ∧ q ≠ xm ∧ q ≠ ym) ∨ (p = xm ∧ q = ym))
    (hrest : Y2Path (y2Move (rungDel C a b xm xp ym yp μ) p q p' q') rest T')
    (ih : InsIH (y2Move (rungDel C a b xm xp ym yp μ) p q p' q') T' rest) :
    InsConcl C T' a b (s(p, q) :: rest) := by
  have hpP : p ∉ Kp := fun h => hR.not_mem_both hp h
  have hqP : q ∉ Kp := fun h => hR.not_mem_both hq h
  have hpxp : p ≠ xp := fun h => hpP (h ▸ hR.xp_mem)
  have hpyp : p ≠ yp := fun h => hpP (h ▸ hR.yp_mem)
  have hqxp : q ≠ xp := fun h => hqP (h ▸ hR.xp_mem)
  have hqyp : q ≠ yp := fun h => hqP (h ▸ hR.yp_mem)
  obtain ⟨hpa, hpb⟩ := hR.ne_of_mem (Or.inl hp)
  obtain ⟨hqa, hqb⟩ := hR.ne_of_mem (Or.inl hq)
  have hq'V := hR.mem_poles_of_rungDel hP.d_mem
  obtain ⟨hq'a, hq'b⟩ := hR.ne_of_mem hq'V
  rcases hcase with ⟨hpm, hpm', hqm, hqm'⟩ | ⟨hpm, hqm, hqm'⟩ | ⟨hpm, hqm'⟩
  · -- (i): no cross-bond external
    have hPC : IsY2Pair C p q p' q' :=
      hP.congr (fun x => (hR.rungDel_mult_inner hpa hpb hpm hpxp hpm' hpyp μ x).symm)
        (fun x => (hR.rungDel_mult_inner hqa hqb hqm hqxp hqm' hqyp μ x).symm)
    have hp'V := hR.mem_poles_of_rungDel hP.c_mem
    obtain ⟨hp'a, hp'b⟩ := hR.ne_of_mem hp'V
    have hp' : p' ∈ Km := hR.mem_Km_of_mult hp (by rw [hPC.mult_ac]; omega) hp'a hp'b
    have hq' : q' ∈ Km := hR.mem_Km_of_mult hq (by rw [hPC.mult_bd]; omega) hq'a hq'b
    obtain ⟨h1, -, h3⟩ := rung_case_i hR hPC hp hq hp' hq' hpm hpm' hqm hqm' μ
    exact InsConcl.cons hPC rfl (ih h1 h3.symm)
  · -- (ii): `p = xm`, one cross-bond external
    subst hpm
    obtain ⟨hymp, hp'z, hCp⟩ := ins_rail hR hP hq
    have hymq : ym ≠ q := fun h => hqm' h.symm
    have hCq : ∀ x, C.mult s(q, x) = if x = p then 3 else if x = q' then 1 else 0 := fun x =>
      (hR.rungDel_mult_inner hqa hqb hqm hqxp hqm' hqyp μ x).symm.trans (hP.mult_b x)
    have hPC : IsY2Pair C p q a q' :=
      IsY2Pair.of_mult hP.ne (Ne.symm hq'a) (Ne.symm hpa) (Ne.symm hqa) hP.d_ne_a hP.d_ne_b hCp hCq
    have hq' : q' ∈ Km := hR.mem_Km_of_mult hq (by rw [hPC.mult_bd]; omega) hq'a hq'b
    obtain ⟨h1, -, h3⟩ := rung_case_ii hR hPC hq hq' hymp hymq μ
    rw [← hp'z] at h3
    exact InsConcl.cons hPC rfl (ih h1 h3.symm)
  · -- (iii): `P = {xm, ym}`, the collapse
    subst hpm; subst hqm'
    obtain ⟨hqp, hp'z, hCp⟩ := ins_rail hR hP hq
    have hP' : IsY2Pair (rungDel C b a q yp p xp μ) q p q' p' := by
      rw [← rungDel_swapAB]; exact hP.swap
    obtain ⟨-, hq'z, hCq⟩ := ins_rail hR.swapAB hP' hp
    have hPC : IsY2Pair C p q a b :=
      IsY2Pair.of_mult hP.ne hR.ne (Ne.symm hpa) (Ne.symm hqa) (Ne.symm hpb) (Ne.symm hqb) hCp hCq
    have hxy : xp ≠ yp := by
      intro h
      apply hP.ext_ne
      rw [hp'z, hq'z, h]
    obtain ⟨h1, h2⟩ := (rung_case_iii hR hPC).2 hxy
    obtain ⟨-, h4⟩ := h2 μ
    rw [← hp'z, ← hq'z] at h4
    refine ⟨1, by simp, ?_⟩
    simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.singleton_append]
    exact .cons hPC (.cons h1 (h4 ▸ hrest))

/-- A first move inside `Km` with `p` a rail end or `q` not: normalise `a ↔ b`. -/
private theorem insert_km1 (hR : RungCore C a b xm xp ym yp Km Kp)
    (hP : IsY2Pair (rungDel C a b xm xp ym yp μ) p q p' q') (hp : p ∈ Km) (hq : q ∈ Km)
    (hpre : (p = xm ∨ p = ym) ∨ (q ≠ xm ∧ q ≠ ym))
    (hrest : Y2Path (y2Move (rungDel C a b xm xp ym yp μ) p q p' q') rest T')
    (ih : InsIH (y2Move (rungDel C a b xm xp ym yp μ) p q p' q') T' rest) :
    InsConcl C T' a b (s(p, q) :: rest) := by
  have hpq := hP.ne
  by_cases hpm : p = xm
  · by_cases hqm' : q = ym
    · exact insert_core hR hP hp hq (Or.inr (Or.inr ⟨hpm, hqm'⟩)) hrest ih
    · exact insert_core hR hP hp hq (Or.inr (Or.inl ⟨hpm, fun h => hpq (hpm.trans h.symm), hqm'⟩)) hrest ih
  by_cases hpm' : p = ym
  · -- swap `a ↔ b`
    rw [rungDel_swapAB] at hP hrest ih
    refine InsConcl.swap ?_
    by_cases hqm : q = xm
    · exact insert_core hR.swapAB hP hp hq (Or.inr (Or.inr ⟨hpm', hqm⟩)) hrest ih
    · exact insert_core hR.swapAB hP hp hq
        (Or.inr (Or.inl ⟨hpm', fun h => hpq (hpm'.trans h.symm), hqm⟩)) hrest ih
  · have hq' : q ≠ xm ∧ q ≠ ym := by tauto
    exact insert_core hR hP hp hq (Or.inl ⟨hpm, hpm', hq'⟩) hrest ih

/-- A first move inside `Km`: normalise the orientation of `P`. -/
private theorem insert_km (hR : RungCore C a b xm xp ym yp Km Kp)
    (hP : IsY2Pair (rungDel C a b xm xp ym yp μ) p q p' q') (hp : p ∈ Km) (hq : q ∈ Km)
    (hrest : Y2Path (y2Move (rungDel C a b xm xp ym yp μ) p q p' q') rest T')
    (ih : InsIH (y2Move (rungDel C a b xm xp ym yp μ) p q p' q') T' rest) :
    InsConcl C T' a b (s(p, q) :: rest) := by
  by_cases hsw : (p ≠ xm ∧ p ≠ ym) ∧ (q = xm ∨ q = ym)
  · rw [← y2Move_swap _ p q p' q'] at hrest ih
    have := insert_km1 hR hP.swap hq hp (Or.inl hsw.2) hrest ih
    rwa [show s(q, p) = s(p, q) from Sym2.eq_swap] at this
  · exact insert_km1 hR hP hp hq (by tauto) hrest ih

end Steps

/-- **Lemma 5″** (M4 §5.3; REF-M4 claim 6, repair R3): rung insertion as path surgery. If `R = {a, b}` carries rung
data in `C` and `C/[μ]R →* T'` (a doubled triangle) along `ps`, then `C →* T'` along `ps` with the move `R` inserted
at some position. -/
theorem y2Path_insertRung {D T' : UMultigraph V} {ps : List (Sym2 V)} (hp : Y2Path D ps T')
    (hT : IsDoubledTriangle T') : InsIH D T' ps := by
  induction hp with
  | nil G =>
    intro C a b xm xp ym yp Km Kp μ hR hD
    exact ((hR.rungDel_not_doubledTriangle μ) (hD ▸ hT)).elim
  | @cons D T' p q p' q' rest hP hrest ih =>
    replace ih : InsIH (y2Move D p q p' q') T' rest := ih hT
    intro C a b xm xp ym yp Km Kp μ hR hD
    subst hD
    obtain ⟨hpa, hpb⟩ := hR.ne_of_mem (hR.mem_poles_of_rungDel hP.a_mem)
    obtain ⟨hqa, hqb⟩ := hR.ne_of_mem (hR.mem_poles_of_rungDel hP.b_mem)
    have hcard : Multiset.card (rungAdds xm xp ym yp μ) = 2 := by cases μ <;> rfl
    rcases hR.mem_poles_of_rungDel hP.a_mem with hp | hp
    · have hq : q ∈ Km := by
        rcases hR.mem_poles_of_rungDel hP.b_mem with hq | hq
        · exact hq
        · have h1 := hP.mult_ab
          rw [hR.rungDel_mult_cross hp hq] at h1
          have := Multiset.count_le_card s(p, q) (rungAdds xm xp ym yp μ)
          omega
      exact insert_km hR hP hp hq hrest ih
    · have hq : q ∈ Kp := by
        rcases hR.mem_poles_of_rungDel hP.b_mem with hq | hq
        · have h1 := hP.mult_ab
          rw [Sym2.eq_swap, hR.rungDel_mult_cross hq hp] at h1
          have := Multiset.count_le_card s(q, p) (rungAdds xm xp ym yp μ)
          omega
        · exact hq
      rw [rungDel_swapPoles] at hP hrest ih
      exact insert_km hR.swapPoles hP hp hq hrest ih

end WaveTurbulence.TVine.Core
