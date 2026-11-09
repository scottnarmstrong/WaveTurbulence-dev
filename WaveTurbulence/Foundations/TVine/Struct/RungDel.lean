/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Rung
public import WaveTurbulence.Foundations.TVine.Struct.Thm6Layer
import Mathlib.Tactic

/-!
# Cuts under rung deletion (packet L3; for N2 Prop 1.17(a))

For a 2-cut rung `R = {a, b}` of `G` (L1's `IsRungAt`, poles `Km`, `Kp`, rails `a–xm, a–xp, b–ym, b–yp`) and the
straight deletion `G' = rungDel G a b xm xp ym yp true` (new bonds `xm–yp`, `xp–ym`):

* weights of `G'`: inside a pole as in `G` (`eW_del_same`), between the poles only the new bonds (`eW_del_cross`);
* the rail count of a pole subset (`eW_rails`), cuts of pole subsets in `G` (`cut_pole_sub`);
* `sep_drop`: a side of `G` with cut `≤ 2` contains both or neither rung atom, and dropping them does not increase
  its cut in `G'`;
* `sep_lift`: a side of `G'` with cut `≤ 2` separating `u` from `w` gives a side of `G` with cut `≤ 2` separating them
  (N2 Prop 1.17(a) proof, by the pole-splitting cases and parity).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core CutAlg

variable {V : Type*} [DecidableEq V]

/-- The indicator of a decidable proposition. -/
def ind (p : Prop) [Decidable p] : ℕ := if p then 1 else 0

section rung

variable {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}

theorem sum_ind_eq {A : Finset V} (c : V) : ∑ u ∈ A, ind (u = c) = ind (c ∈ A) := by
  unfold ind; rw [Finset.sum_ite_eq']

theorem sum_ind_and {A B : Finset V} (c d : V) :
    ∑ u ∈ A, ∑ w ∈ B, ind (u = c ∧ w = d) = ind (c ∈ A ∧ d ∈ B) := by
  unfold ind
  simp only [ite_and]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq']
  by_cases hc : c ∈ A <;> by_cases hd : d ∈ B <;> simp [hc, hd]

namespace RungFacts

variable (hR : IsRungAt G a b xm xp ym yp Km Kp)
include hR

theorem not_mem_both {x : V} (hm : x ∈ Km) (hp : x ∈ Kp) : False := Finset.disjoint_left.mp hR.disj hm hp

theorem pole_mem {x : V} (hx : x ∈ Km ∨ x ∈ Kp) : x ∈ G.verts ∧ x ≠ a ∧ x ≠ b := by
  have : x ∈ Km ∪ Kp := Finset.mem_union.mpr hx
  rw [hR.union] at this
  simp only [Finset.mem_erase] at this
  exact ⟨this.2.2, this.2.1, this.1⟩

theorem a_not_pole : a ∉ Km ∧ a ∉ Kp :=
  ⟨fun h => ((pole_mem hR) (Or.inl h)).2.1 rfl, fun h => ((pole_mem hR) (Or.inr h)).2.1 rfl⟩

theorem b_not_pole : b ∉ Km ∧ b ∉ Kp :=
  ⟨fun h => ((pole_mem hR) (Or.inl h)).2.2 rfl, fun h => ((pole_mem hR) (Or.inr h)).2.2 rfl⟩

theorem verts_del : (rungDel G a b xm xp ym yp true).verts = Km ∪ Kp := by
  rw [hR.verts_rungDel true, ← hR.union]

theorem verts_eq : G.verts = Km ∪ Kp ∪ {a, b} := by
  ext x
  constructor
  · intro hx
    by_cases ha : x = a
    · simp [ha]
    by_cases hb : x = b
    · simp [hb]
    have : x ∈ (G.verts.erase a).erase b := by simp [hx, ha, hb]
    rw [← hR.union] at this
    exact Finset.mem_union_left _ this
  · intro hx
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with (h | h) | rfl | rfl
    · exact ((pole_mem hR) (Or.inl h)).1
    · exact ((pole_mem hR) (Or.inr h)).1
    · exact hR.a_mem
    · exact hR.b_mem

/-- The multiplicity of `a` towards a pole atom. -/
theorem mult_a {x : V} (hx : x ∈ Km ∨ x ∈ Kp) : G.mult s(a, x) = ind (x = xm) + ind (x = xp) := by
  have hxb := ((pole_mem hR) hx).2.2
  have hne : xm ≠ xp := fun h => (not_mem_both hR) hR.xm_mem (h ▸ hR.xp_mem)
  unfold ind
  by_cases h1 : x = xm
  · subst h1; simp [hR.a_xm, hne]
  by_cases h2 : x = xp
  · subst h2; simp [hR.a_xp, Ne.symm hne]
  simp [h1, h2, hR.a_other x hxb h1 h2]

theorem mult_b {x : V} (hx : x ∈ Km ∨ x ∈ Kp) : G.mult s(b, x) = ind (x = ym) + ind (x = yp) := by
  have hxa := ((pole_mem hR) hx).2.1
  have hne : ym ≠ yp := fun h => (not_mem_both hR) hR.ym_mem (h ▸ hR.yp_mem)
  unfold ind
  by_cases h1 : x = ym
  · subst h1; simp [hR.b_ym, hne]
  by_cases h2 : x = yp
  · subst h2; simp [hR.b_yp, Ne.symm hne]
  simp [h1, h2, hR.b_other x hxa h1 h2]

/-- The multiplicity of `G'` between pole atoms. -/
theorem mult_del {u w : V} (hu : u ∈ Km ∨ u ∈ Kp) (hw : w ∈ Km ∨ w ∈ Kp) :
    (rungDel G a b xm xp ym yp true).mult s(u, w) =
      G.mult s(u, w) + ({s(xm, yp), s(xp, ym)} : Multiset (Sym2 V)).count s(u, w) := by
  rw [rungDel_mult]
  have hu' := (pole_mem hR) hu
  have hw' := (pole_mem hR) hw
  have : ¬ (a ∈ s(u, w) ∨ b ∈ s(u, w)) := by
    simp only [Sym2.mem_iff, not_or]
    exact ⟨⟨fun h => hu'.2.1 h.symm, fun h => hw'.2.1 h.symm⟩, fun h => hu'.2.2 h.symm, fun h => hw'.2.2 h.symm⟩
  rw [if_neg this]
  rfl

/-- The new bonds do not join two atoms of one pole. -/
theorem adds_count_same {u w : V} (h : (u ∈ Km ∧ w ∈ Km) ∨ (u ∈ Kp ∧ w ∈ Kp)) :
    ({s(xm, yp), s(xp, ym)} : Multiset (Sym2 V)).count s(u, w) = 0 := by
  rw [Multiset.count_eq_zero]
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, Sym2.eq_iff, not_or, not_and]
  have hxm := hR.xm_mem; have hxp := hR.xp_mem; have hym := hR.ym_mem; have hyp := hR.yp_mem
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> intro h1 h2 <;> subst h1 <;> subst h2 <;>
    rcases h with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    first
    | exact not_mem_both hR h3 (by assumption) | exact not_mem_both hR h4 (by assumption)
    | exact not_mem_both hR (by assumption) h3 | exact not_mem_both hR (by assumption) h4

/-- The new bonds between a `Km`-atom and a `Kp`-atom. -/
theorem adds_count_cross {u w : V} (hu : u ∈ Km) (hw : w ∈ Kp) :
    ({s(xm, yp), s(xp, ym)} : Multiset (Sym2 V)).count s(u, w) = ind (u = xm ∧ w = yp) + ind (u = ym ∧ w = xp) := by
  rw [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  unfold ind
  have hxm := hR.xm_mem; have hxp := hR.xp_mem; have hym := hR.ym_mem; have hyp := hR.yp_mem
  have e1 : (s(u, w) = s(xm, yp)) ↔ (u = xm ∧ w = yp) := by
    rw [Sym2.eq_iff]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact h
      · subst h1; exact absurd hu (fun h => (not_mem_both hR) h hyp)
    · exact Or.inl
  have e2 : (s(u, w) = s(xp, ym)) ↔ (u = ym ∧ w = xp) := by
    rw [Sym2.eq_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · subst h1; exact absurd hu (fun h => (not_mem_both hR) h hxp)
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact Or.inr ⟨h1, h2⟩
  rw [show (if s(u, w) = s(xp, ym) then 1 else 0) = (if u = ym ∧ w = xp then 1 else 0) from if_congr e2 rfl rfl,
    show (if s(u, w) = s(xm, yp) then 1 else 0) = (if u = xm ∧ w = yp then 1 else 0) from if_congr e1 rfl rfl]
  ring

/-- **Weights of `G'` inside a pole are those of `G`.** -/
theorem eW_del_same {A B : Finset V} (h : (A ⊆ Km ∧ B ⊆ Km) ∨ (A ⊆ Kp ∧ B ⊆ Kp)) :
    eW (wG (rungDel G a b xm xp ym yp true)) A B = eW (wG G) A B := by
  unfold eW
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun w hw => ?_
  simp only [wG]
  rcases h with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · rw [(mult_del hR) (Or.inl (hA hu)) (Or.inl (hB hw)), (adds_count_same hR) (Or.inl ⟨hA hu, hB hw⟩), add_zero]
  · rw [(mult_del hR) (Or.inr (hA hu)) (Or.inr (hB hw)), (adds_count_same hR) (Or.inr ⟨hA hu, hB hw⟩), add_zero]

/-- **Weights of `G'` between the poles are the new bonds.** -/
theorem eW_del_cross {A B : Finset V} (hA : A ⊆ Km) (hB : B ⊆ Kp) :
    eW (wG (rungDel G a b xm xp ym yp true)) A B = ind (xm ∈ A ∧ yp ∈ B) + ind (ym ∈ A ∧ xp ∈ B) := by
  unfold eW
  have : ∀ u ∈ A, ∀ w ∈ B, wG (rungDel G a b xm xp ym yp true) u w = ind (u = xm ∧ w = yp) + ind (u = ym ∧ w = xp) := by
    intro u hu w hw
    simp only [wG]
    rw [(mult_del hR) (Or.inl (hA hu)) (Or.inr (hB hw)), hR.noBond u (hA hu) w (hB hw), zero_add,
      (adds_count_cross hR) (hA hu) (hB hw)]
  rw [Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun w hw => this u hu w hw]
  simp only [Finset.sum_add_distrib]
  rw [sum_ind_and, sum_ind_and]

/-- The rails from a subset of `Km`. -/
theorem eW_rails_m {A : Finset V} (hA : A ⊆ Km) : eW (wG G) A {a, b} = ind (xm ∈ A) + ind (ym ∈ A) := by
  unfold eW
  have hab := hR.ne
  rw [Finset.sum_congr rfl fun u hu => Finset.sum_pair (f := fun w => wG G u w) hab]
  simp only [wG]
  rw [Finset.sum_congr rfl fun u hu => by
    rw [Sym2.eq_swap, (mult_a hR) (Or.inl (hA hu)), Sym2.eq_swap, (mult_b hR) (Or.inl (hA hu))]]
  have hxp : xp ∉ A := fun h => (not_mem_both hR) (hA h) hR.xp_mem
  have hyp : yp ∉ A := fun h => (not_mem_both hR) (hA h) hR.yp_mem
  simp only [Finset.sum_add_distrib, sum_ind_eq]
  unfold ind; simp [hxp, hyp]; try ring

theorem eW_rails_p {A : Finset V} (hA : A ⊆ Kp) : eW (wG G) A {a, b} = ind (xp ∈ A) + ind (yp ∈ A) := by
  unfold eW
  have hab := hR.ne
  rw [Finset.sum_congr rfl fun u hu => Finset.sum_pair (f := fun w => wG G u w) hab]
  simp only [wG]
  rw [Finset.sum_congr rfl fun u hu => by
    rw [Sym2.eq_swap, (mult_a hR) (Or.inr (hA hu)), Sym2.eq_swap, (mult_b hR) (Or.inr (hA hu))]]
  have hxm : xm ∉ A := fun h => (not_mem_both hR) hR.xm_mem (hA h)
  have hym : ym ∉ A := fun h => (not_mem_both hR) hR.ym_mem (hA h)
  simp only [Finset.sum_add_distrib, sum_ind_eq]
  unfold ind; simp [hxm, hym]; try ring

theorem eW_zero_cross {A B : Finset V} (hA : A ⊆ Km) (hB : B ⊆ Kp) : eW (wG G) A B = 0 := by
  unfold eW
  exact Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun w hw => hR.noBond u (hA hu) w (hB hw)

/-- **The cut in `G` of a subset of `Km`.** -/
theorem cut_sub_m {A : Finset V} (hA : A ⊆ Km) :
    cut G A = eW (wG G) A (Km \ A) + ind (xm ∈ A) + ind (ym ∈ A) := by
  rw [cut_eq_eW]
  have hset : G.verts \ A = (Km \ A) ∪ (Kp ∪ {a, b}) := by
    rw [(verts_eq hR)]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨(h | h) | h, hx⟩ <;> tauto
    · rintro (⟨h, hx⟩ | h | h)
      · exact ⟨Or.inl (Or.inl h), hx⟩
      · exact ⟨Or.inl (Or.inr h), fun h' => (not_mem_both hR) (hA h') h⟩
      · refine ⟨Or.inr h, fun h' => ?_⟩
        rcases h with rfl | rfl
        · exact (a_not_pole hR).1 (hA h')
        · exact (b_not_pole hR).1 (hA h')
  have hd1 : Disjoint (Km \ A) (Kp ∪ {a, b}) := by
    rw [Finset.disjoint_left]; intro x hx h
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
    have hx' := (Finset.mem_sdiff.mp hx).1
    rcases h with h | rfl | rfl
    · exact (not_mem_both hR) hx' h
    · exact (a_not_pole hR).1 hx'
    · exact (b_not_pole hR).1 hx'
  have hd2 : Disjoint Kp {a, b} := by
    rw [Finset.disjoint_left]; intro x hx h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · exact (a_not_pole hR).2 hx
    · exact (b_not_pole hR).2 hx
  rw [hset, eW_union_right _ hd1, eW_union_right _ hd2, (eW_zero_cross hR) hA subset_rfl, (eW_rails_m hR) hA]
  ring

theorem cut_sub_p {A : Finset V} (hA : A ⊆ Kp) :
    cut G A = eW (wG G) A (Kp \ A) + ind (xp ∈ A) + ind (yp ∈ A) := by
  rw [cut_eq_eW]
  have hset : G.verts \ A = (Kp \ A) ∪ (Km ∪ {a, b}) := by
    rw [(verts_eq hR)]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨(h | h) | h, hx⟩ <;> tauto
    · rintro (⟨h, hx⟩ | h | h)
      · exact ⟨Or.inl (Or.inr h), hx⟩
      · exact ⟨Or.inl (Or.inl h), fun h' => (not_mem_both hR) h (hA h')⟩
      · refine ⟨Or.inr h, fun h' => ?_⟩
        rcases h with rfl | rfl
        · exact (a_not_pole hR).2 (hA h')
        · exact (b_not_pole hR).2 (hA h')
  have hd1 : Disjoint (Kp \ A) (Km ∪ {a, b}) := by
    rw [Finset.disjoint_left]; intro x hx h
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
    have hx' := (Finset.mem_sdiff.mp hx).1
    rcases h with h | rfl | rfl
    · exact (not_mem_both hR) h hx'
    · exact (a_not_pole hR).2 hx'
    · exact (b_not_pole hR).2 hx'
  have hd2 : Disjoint Km {a, b} := by
    rw [Finset.disjoint_left]; intro x hx h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · exact (a_not_pole hR).1 hx
    · exact (b_not_pole hR).1 hx
  rw [hset, eW_union_right _ hd1, eW_union_right _ hd2, eW_comm (symm_wG G) A Km,
    (eW_zero_cross hR) subset_rfl hA, (eW_rails_p hR) hA]
  ring

end RungFacts

end rung

end WaveTurbulence.TVine.Struct
