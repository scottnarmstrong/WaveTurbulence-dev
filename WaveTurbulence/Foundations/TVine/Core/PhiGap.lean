/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.PhiRemoval
public import WaveTurbulence.Foundations.TVine.Core.Lemma19Ins

/-!
# N2 Lemma 1.14(d): gap freeness transfers along rung deletion — cut lemmas

* (`cut_compl`, a set and its complement have the same cut, comes from `Core.Lemma19Ins`);
* `cut_ge_pairs`: any set of crossing index pairs bounds the cut from below;
* `gapCut_crossing`: for a gap cut `X ∋ k`, the only crossing bonds are the two `U°`-bonds at `k`;
* `cut_rungDel_avoid`: for `Y` avoiding the rung, `cut (G/[μ]R) Y + (rail ends in Y) = cut G Y + (added bonds
  crossing Y)`, and `adds_cross_count`: the added bonds crossing `Y` are the rail ends in `Y` when these lie in one
  pole.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

theorem cut_eq_sum_product (G : UMultigraph V) (X : Finset V) :
    cut G X = ∑ p ∈ X ×ˢ (G.verts \ X), G.mult s(p.1, p.2) := by
  rw [cut, Finset.sum_product]


theorem cut_ge_pairs (G : UMultigraph V) {X : Finset V} {P : Finset (V × V)} (hP : P ⊆ X ×ˢ (G.verts \ X)) :
    ∑ p ∈ P, G.mult s(p.1, p.2) ≤ cut G X := by
  rw [cut_eq_sum_product]
  exact Finset.sum_le_sum_of_subset_of_nonneg hP fun _ _ _ => Nat.zero_le _

/-- The structure of a gap cut: with `k ∈ X` and its two `U°`-neighbours outside, they carry the only crossing
bonds. -/
theorem gapCut_crossing {G : UMultigraph V} {X : Finset V} {k n₁ n₂ : V} (hcut : cut G X = 2) (hk : k ∈ X)
    (hn₁ : n₁ ∈ G.verts \ X) (hn₂ : n₂ ∈ G.verts \ X) (h₁ : 1 ≤ G.mult s(k, n₁)) (h₂ : 1 ≤ G.mult s(k, n₂))
    (h₁₂ : n₁ = n₂ → 2 ≤ G.mult s(k, n₁)) :
    ∀ u ∈ X, ∀ w ∈ G.verts \ X, G.mult s(u, w) ≠ 0 → u = k ∧ (w = n₁ ∨ w = n₂) := by
  intro u hu w hw hm
  by_contra hne
  have hne' : (u, w) ≠ (k, n₁) ∧ (u, w) ≠ (k, n₂) := by
    constructor <;> intro h <;> simp only [Prod.mk.injEq] at h <;> exact hne ⟨h.1, by tauto⟩
  by_cases hnn : n₁ = n₂
  · subst hnn
    have hP : ({(k, n₁), (u, w)} : Finset (V × V)) ⊆ X ×ˢ (G.verts \ X) := by
      intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> exact Finset.mem_product.mpr ⟨by assumption, by assumption⟩
    have := cut_ge_pairs G hP
    rw [Finset.sum_pair (Ne.symm hne'.1)] at this
    simp only at this
    have := h₁₂ rfl
    omega
  · have hP : ({(k, n₁), (k, n₂), (u, w)} : Finset (V × V)) ⊆ X ×ˢ (G.verts \ X) := by
      intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> exact Finset.mem_product.mpr ⟨by assumption, by assumption⟩
    have := cut_ge_pairs G hP
    have hnot : (k, n₁) ∉ ({(k, n₂), (u, w)} : Finset (V × V)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
      exact ⟨fun h => hnn h.2, fun h => hne'.1 (by rw [h.1, h.2])⟩
    rw [Finset.sum_insert hnot, Finset.sum_pair (Ne.symm hne'.2)] at this
    simp only at this
    omega

section Del

variable {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V} {μ : Bool}

/-- The cut of a set avoiding the rung, after deletion. -/
theorem cut_rungDel_avoid (hR : RungCore G a b xm xp ym yp Km Kp) {Y : Finset V} (hYV : Y ⊆ G.verts)
    (haY : a ∉ Y) (hbY : b ∉ Y) :
    cut (rungDel G a b xm xp ym yp μ) Y + ((if xm ∈ Y then 1 else 0) + (if xp ∈ Y then 1 else 0) +
      (if ym ∈ Y then 1 else 0) + (if yp ∈ Y then 1 else 0)) =
    cut G Y + ∑ u ∈ Y, ∑ w ∈ (rungDel G a b xm xp ym yp μ).verts \ Y,
      (rungAdds xm xp ym yp μ).count s(u, w) := by
  set W := (rungDel G a b xm xp ym yp μ).verts \ Y with hW
  have hDV : (rungDel G a b xm xp ym yp μ).verts = (G.verts.erase a).erase b := hR.verts_rungDel μ
  have haW : a ∉ W := by simp [hW, hDV]
  have hbW : b ∉ W := by simp [hW, hDV]
  have hsd : G.verts \ Y = insert a (insert b W) := by
    ext x; simp only [hW, hDV, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hx, hxY⟩
      by_cases hxa : x = a
      · exact Or.inl hxa
      · by_cases hxb : x = b
        · exact Or.inr (Or.inl hxb)
        · exact Or.inr (Or.inr ⟨⟨hxb, hxa, hx⟩, hxY⟩)
    · rintro (rfl | rfl | ⟨⟨_, _, hx⟩, hxY⟩)
      · exact ⟨hR.a_verts, haY⟩
      · exact ⟨hR.b_verts, hbY⟩
      · exact ⟨hx, hxY⟩
  have hYab : ∀ u ∈ Y, u ≠ a ∧ u ≠ b := fun u hu => ⟨fun h => haY (h ▸ hu), fun h => hbY (h ▸ hu)⟩
  have hDm : ∀ u ∈ Y, ∀ w ∈ W, (rungDel G a b xm xp ym yp μ).mult s(u, w) =
      G.mult s(u, w) + (rungAdds xm xp ym yp μ).count s(u, w) := by
    intro u hu w hw
    have hw' : w ≠ a ∧ w ≠ b := ⟨fun h => haW (h ▸ hw), fun h => hbW (h ▸ hw)⟩
    rw [rungDel_mult, if_neg (by
      rintro (h | h) <;> rcases Sym2.mem_iff.mp h with h | h
      exacts [(hYab u hu).1 h.symm, hw'.1 h.symm, (hYab u hu).2 h.symm, hw'.2 h.symm])]
  have hrowa : ∑ u ∈ Y, G.mult s(u, a) = (if xm ∈ Y then 1 else 0) + (if xp ∈ Y then 1 else 0) := by
    have hxx := hR.xm_ne_xp
    have h : ∀ u ∈ Y, G.mult s(u, a) = (if u = xm then 1 else 0) + (if u = xp then 1 else 0) := by
      intro u hu
      rw [Sym2.eq_swap, hR.mult_a, if_neg (hYab u hu).2]
      by_cases h1 : u = xm
      · subst h1; simp [hxx]
      · by_cases h2 : u = xp
        · subst h2; simp [h1]
        · simp [h1, h2]
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  have hrowb : ∑ u ∈ Y, G.mult s(u, b) = (if ym ∈ Y then 1 else 0) + (if yp ∈ Y then 1 else 0) := by
    have hyy := hR.ym_ne_yp
    have h : ∀ u ∈ Y, G.mult s(u, b) = (if u = ym then 1 else 0) + (if u = yp then 1 else 0) := by
      intro u hu
      rw [Sym2.eq_swap, hR.mult_b, if_neg (hYab u hu).1]
      by_cases h1 : u = ym
      · subst h1; simp [hyy]
      · by_cases h2 : u = yp
        · subst h2; simp [h1]
        · simp [h1, h2]
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  have hGcut : cut G Y = ∑ u ∈ Y, ∑ w ∈ W, G.mult s(u, w) + ((if xm ∈ Y then 1 else 0) +
      (if xp ∈ Y then 1 else 0) + ((if ym ∈ Y then 1 else 0) + (if yp ∈ Y then 1 else 0))) := by
    unfold cut
    rw [hsd, ← hrowa, ← hrowb, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.sum_insert (by simp [hR.ne, haW]), Finset.sum_insert hbW]
    ring
  have hDcut : cut (rungDel G a b xm xp ym yp μ) Y = ∑ u ∈ Y, ∑ w ∈ W, G.mult s(u, w) +
      ∑ u ∈ Y, ∑ w ∈ W, (rungAdds xm xp ym yp μ).count s(u, w) := by
    unfold cut
    rw [← hW, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro u hu
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w hw => hDm u hu w hw
  rw [hDcut, hGcut]
  ring

end Del

end WaveTurbulence.TVine.Core
