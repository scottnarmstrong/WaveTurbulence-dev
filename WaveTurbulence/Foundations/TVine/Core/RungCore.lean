/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.LemmaE
public import WaveTurbulence.Foundations.TVine.Core.Rung

/-!
# Rung data along (Y2)-paths (M4 §5.3)

`RungCore G a b xm xp ym yp Km Kp` is the part of `IsRungAt` that survives the moves of a (Y2)-path inside a pole:
the bonds at `a, b` (normalised), and a partition of the other atoms into two poles with no bond between them. Pole
connectivity is not needed for path surgery.

* `IsRungAt.toCore`, symmetries `RungCore.swapPoles`, `RungCore.swapAB`, `rungDel_swapPoles`, `rungDel_swapAB`;
* `splice_mult_at`, `splice_splice_mult` (normal form of two splices), `splice_swap`;
* `RungCore.rungDel_mult_inner`: away from the rung and its rails, deletion changes nothing.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

/-! ## Splices -/

theorem splice_swap (G : UMultigraph V) (a b : V) (A : Multiset (Sym2 V)) : splice G b a A = splice G a b A := by
  apply ext
  · exact Finset.erase_right_comm
  · intro e; rw [splice_mult, splice_mult]; exact if_congr or_comm rfl rfl

theorem splice_congr_adds (G : UMultigraph V) (a b : V) {A B : Multiset (Sym2 V)} (h : A = B) :
    splice G a b A = splice G a b B := h ▸ rfl

/-- After a splice at `{a, b}`, the bonds at an atom `v ∉ {a, b}`. -/
theorem splice_mult_at (G : UMultigraph V) {a b v : V} (A : Multiset (Sym2 V)) (hva : v ≠ a) (hvb : v ≠ b)
    (x : V) : (splice G a b A).mult s(v, x) = if x = a ∨ x = b then 0 else G.mult s(v, x) + A.count s(v, x) := by
  rw [splice_mult]
  by_cases hx : x = a ∨ x = b
  · rw [if_pos ((mem_pair_iff hva hvb).mpr hx), if_pos hx]
  · rw [if_neg (mt (mem_pair_iff hva hvb).mp hx), if_neg hx]

/-- **Normal form of two splices**, when the second's bonds avoid the first pair. -/
theorem splice_splice_mult (H : UMultigraph V) {p q a b : V} (A B : Multiset (Sym2 V))
    (hB : ∀ f ∈ B, p ∉ f ∧ q ∉ f) (e : Sym2 V) :
    (splice (splice H p q A) a b B).mult e =
      if a ∈ e ∨ b ∈ e ∨ p ∈ e ∨ q ∈ e then 0 else H.mult e + A.count e + B.count e := by
  rw [splice_mult, splice_mult]
  by_cases hab : a ∈ e ∨ b ∈ e
  · have h4 : a ∈ e ∨ b ∈ e ∨ p ∈ e ∨ q ∈ e := by tauto
    rw [if_pos hab, if_pos h4]
  · by_cases hpq : p ∈ e ∨ q ∈ e
    · have h4 : a ∈ e ∨ b ∈ e ∨ p ∈ e ∨ q ∈ e := by tauto
      have : B.count e = 0 := by
        rw [Multiset.count_eq_zero]; intro he
        rcases hpq with h | h
        · exact (hB e he).1 h
        · exact (hB e he).2 h
      rw [if_neg hab, if_pos hpq, if_pos h4, this]
    · have h4 : ¬ (a ∈ e ∨ b ∈ e ∨ p ∈ e ∨ q ∈ e) := by tauto
      rw [if_neg hab, if_neg hpq, if_neg h4]

theorem y2Move_eq_splice (G : UMultigraph V) (a b c d : V) : y2Move G a b c d = splice G a b {s(c, d)} := rfl

/-! ## Rung data along paths -/

/-- **Rung data along a path**: `a ≠ b`, the bonds at `a` are `a = b` (double) and the rails `a–xm`, `a–xp`; those
at `b` are `b = a` and `b–ym`, `b–yp`; the other atoms split into poles `Km ∋ xm, ym` and `Kp ∋ xp, yp` with no
bond between them. -/
structure RungCore (G : UMultigraph V) (a b xm xp ym yp : V) (Km Kp : Finset V) : Prop where
  ne : a ≠ b
  mult_a : ∀ x, G.mult s(a, x) = if x = b then 2 else if x = xm ∨ x = xp then 1 else 0
  mult_b : ∀ x, G.mult s(b, x) = if x = a then 2 else if x = ym ∨ x = yp then 1 else 0
  disj : Disjoint Km Kp
  union : Km ∪ Kp = (G.verts.erase a).erase b
  noBond : ∀ u ∈ Km, ∀ w ∈ Kp, G.mult s(u, w) = 0
  xm_mem : xm ∈ Km
  xp_mem : xp ∈ Kp
  ym_mem : ym ∈ Km
  yp_mem : yp ∈ Kp

namespace RungCore

variable {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}

theorem mem_verts (h : RungCore G a b xm xp ym yp Km Kp) {x : V} (hx : x ∈ Km ∨ x ∈ Kp) :
    x ∈ G.verts ∧ x ≠ a ∧ x ≠ b := by
  have : x ∈ Km ∪ Kp := Finset.mem_union.mpr hx
  rw [h.union, Finset.mem_erase, Finset.mem_erase] at this
  exact ⟨this.2.2, this.2.1, this.1⟩

theorem mem_poles (h : RungCore G a b xm xp ym yp Km Kp) {x : V} (hx : x ∈ G.verts) (hxa : x ≠ a)
    (hxb : x ≠ b) : x ∈ Km ∨ x ∈ Kp := by
  have : x ∈ (G.verts.erase a).erase b := by simp [hx, hxa, hxb]
  rw [← h.union] at this
  exact Finset.mem_union.mp this

theorem not_mem_both (h : RungCore G a b xm xp ym yp Km Kp) {x : V} (hm : x ∈ Km) (hp : x ∈ Kp) : False :=
  Finset.disjoint_left.mp h.disj hm hp

theorem xm_ne_xp (h : RungCore G a b xm xp ym yp Km Kp) : xm ≠ xp :=
  fun e => h.not_mem_both h.xm_mem (e ▸ h.xp_mem)

theorem ym_ne_yp (h : RungCore G a b xm xp ym yp Km Kp) : ym ≠ yp :=
  fun e => h.not_mem_both h.ym_mem (e ▸ h.yp_mem)

theorem a_verts (h : RungCore G a b xm xp ym yp Km Kp) : a ∈ G.verts :=
  G.supp _ (by rw [h.mult_a]; simp) a (Sym2.mem_mk_left a b)

theorem b_verts (h : RungCore G a b xm xp ym yp Km Kp) : b ∈ G.verts :=
  G.supp _ (by rw [h.mult_a]; simp) b (Sym2.mem_mk_right a b)

theorem swapPoles (h : RungCore G a b xm xp ym yp Km Kp) : RungCore G a b xp xm yp ym Kp Km where
  ne := h.ne
  mult_a x := by rw [h.mult_a]; exact if_congr Iff.rfl rfl (if_congr or_comm rfl rfl)
  mult_b x := by rw [h.mult_b]; exact if_congr Iff.rfl rfl (if_congr or_comm rfl rfl)
  disj := h.disj.symm
  union := by rw [Finset.union_comm]; exact h.union
  noBond u hu w hw := by rw [Sym2.eq_swap]; exact h.noBond w hw u hu
  xm_mem := h.xp_mem
  xp_mem := h.xm_mem
  ym_mem := h.yp_mem
  yp_mem := h.ym_mem

theorem swapAB (h : RungCore G a b xm xp ym yp Km Kp) : RungCore G b a ym yp xm xp Km Kp where
  ne := h.ne.symm
  mult_a := h.mult_b
  mult_b := h.mult_a
  disj := h.disj
  union := by rw [h.union]; exact Finset.erase_right_comm
  noBond := h.noBond
  xm_mem := h.ym_mem
  xp_mem := h.yp_mem
  ym_mem := h.xm_mem
  yp_mem := h.xp_mem

/-- The double bond is not a doubled triangle's: a doubled triangle has no single bond. -/
theorem not_doubledTriangle (h : RungCore G a b xm xp ym yp Km Kp) (hT : IsDoubledTriangle G) : False := by
  obtain ⟨u, v, w, -, -, -, -, hm⟩ := hT
  have h1 := h.mult_a xm
  rw [hm] at h1
  have hxb : xm ≠ b := (h.mem_verts (Or.inl h.xm_mem)).2.2
  simp only [hxb, true_or, if_false, if_true] at h1
  split_ifs at h1 <;> omega

end RungCore

theorem IsRungAt.toCore {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}
    (h : IsRungAt G a b xm xp ym yp Km Kp) : RungCore G a b xm xp ym yp Km Kp := by
  have hK : ∀ x, x ∈ Km ∨ x ∈ Kp → x ≠ a ∧ x ≠ b := by
    intro x hx
    have : x ∈ Km ∪ Kp := Finset.mem_union.mpr hx
    rw [h.union, Finset.mem_erase, Finset.mem_erase] at this
    exact ⟨this.2.1, this.1⟩
  refine ⟨h.ne, fun x => ?_, fun x => ?_, h.disj, h.union, h.noBond, h.xm_mem, h.xp_mem, h.ym_mem, h.yp_mem⟩
  · by_cases hxb : x = b
    · subst hxb; simp [h.mult_ab]
    · by_cases hxm : x = xm
      · subst hxm; simp [hxb, h.a_xm]
      · by_cases hxp : x = xp
        · subst hxp; simp [hxb, h.a_xp]
        · simp [hxb, hxm, hxp, h.a_other x hxb hxm hxp]
  · by_cases hxa : x = a
    · subst hxa; rw [Sym2.eq_swap]; simp [h.mult_ab]
    · by_cases hym : x = ym
      · subst hym; simp [hxa, h.b_ym]
      · by_cases hyp : x = yp
        · subst hyp; simp [hxa, h.b_yp]
        · simp [hxa, hym, hyp, h.b_other x hxa hym hyp]

/-! ## Deletion symmetries -/

theorem rungAdds_swapPoles (xm xp ym yp : V) (μ : Bool) :
    rungAdds xm xp ym yp μ = rungAdds xp xm yp ym μ := by
  cases μ
  · simp only [rungAdds, Bool.false_eq_true, if_false, Sym2.eq_swap (a := xm), Sym2.eq_swap (a := ym)]
  · simp only [rungAdds, if_true]; exact Multiset.pair_comm _ _

theorem rungAdds_swapAB (xm xp ym yp : V) (μ : Bool) :
    rungAdds xm xp ym yp μ = rungAdds ym yp xm xp μ := by
  cases μ
  · simp only [rungAdds, Bool.false_eq_true, if_false]; exact Multiset.pair_comm _ _
  · show ({s(xm, yp), s(xp, ym)} : Multiset (Sym2 V)) = {s(ym, xp), s(yp, xm)}
    rw [Sym2.eq_swap (a := ym) (b := xp), Sym2.eq_swap (a := yp) (b := xm)]
    exact Multiset.pair_comm _ _

theorem rungDel_swapPoles (G : UMultigraph V) (a b xm xp ym yp : V) (μ : Bool) :
    rungDel G a b xm xp ym yp μ = rungDel G a b xp xm yp ym μ := by
  unfold rungDel; rw [rungAdds_swapPoles]

theorem rungDel_swapAB (G : UMultigraph V) (a b xm xp ym yp : V) (μ : Bool) :
    rungDel G a b xm xp ym yp μ = rungDel G b a ym yp xm xp μ := by
  unfold rungDel; rw [rungAdds_swapAB, splice_swap]

theorem RungCore.verts_rungDel {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}
    (h : RungCore G a b xm xp ym yp Km Kp) (μ : Bool) :
    (rungDel G a b xm xp ym yp μ).verts = (G.verts.erase a).erase b := by
  apply splice_verts_of_subset
  have h1 := (h.mem_verts (Or.inl h.xm_mem)).1
  have h2 := (h.mem_verts (Or.inr h.xp_mem)).1
  have h3 := (h.mem_verts (Or.inl h.ym_mem)).1
  have h4 := (h.mem_verts (Or.inr h.yp_mem)).1
  intro e he x hx
  cases μ <;> simp only [rungAdds, Bool.false_eq_true, if_false, if_true, Multiset.insert_eq_cons,
    Multiset.mem_cons, Multiset.mem_singleton] at he <;>
    rcases he with rfl | rfl <;> rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption

/-- The added bonds of a deletion avoid every atom off the rails. -/
theorem rungAdds_not_mem {xm xp ym yp v : V} (hm : v ≠ xm) (hp : v ≠ xp) (hm' : v ≠ ym) (hp' : v ≠ yp)
    (μ : Bool) : ∀ f ∈ rungAdds xm xp ym yp μ, v ∉ f := by
  intro f hf hv
  cases μ <;> simp only [rungAdds, Bool.false_eq_true, if_false, if_true, Multiset.insert_eq_cons,
    Multiset.mem_cons, Multiset.mem_singleton] at hf <;>
    rcases hf with rfl | rfl <;> rcases Sym2.mem_iff.mp hv with rfl | rfl <;> contradiction

/-- Away from the rung and its rails, deleting the rung changes no bond. -/
theorem RungCore.rungDel_mult_inner {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}
    (h : RungCore G a b xm xp ym yp Km Kp) {v : V} (hva : v ≠ a) (hvb : v ≠ b) (hm : v ≠ xm) (hp : v ≠ xp)
    (hm' : v ≠ ym) (hp' : v ≠ yp) (μ : Bool) (x : V) :
    (rungDel G a b xm xp ym yp μ).mult s(v, x) = G.mult s(v, x) := by
  rw [rungDel, splice_mult_at _ _ hva hvb]
  have hc : (rungAdds xm xp ym yp μ).count s(v, x) = 0 :=
    Multiset.count_eq_zero.mpr fun hf => rungAdds_not_mem hm hp hm' hp' μ _ hf (Sym2.mem_mk_left v x)
  by_cases hx : x = a ∨ x = b
  · rw [if_pos hx]
    rcases hx with rfl | rfl
    · rw [Sym2.eq_swap, h.mult_a]; simp [hvb, hm, hp]
    · rw [Sym2.eq_swap, h.mult_b]; simp [hva, hm', hp']
  · rw [if_neg hx, hc, add_zero]

end WaveTurbulence.TVine.Core
