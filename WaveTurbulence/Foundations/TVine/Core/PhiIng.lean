/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.PhiQ2

/-!
# N2 Lemma 1.14(c′): the ingredient step, by kind

* `IsVineXU.card_I`, `IsVineXU.verts_I`: a vine of type (I) is the double bond on its two joints, so it carries no
  rung;
* `ingConcl_of`: the ingredient step `IngConcl` for every kind, from the (II) ladder step and the T-vine cap step
  (the non-cap T step is `isTVineU_rungDel_of_noncap`).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

theorem IsVineXU.card_I {X : UMultigraph V} {p q : V} (h : IsVineXU .I X p q) : X.verts.card = 2 := by
  obtain ⟨-, k, hk, f, hinj, himg, -, -⟩ := h
  have : k = [] := List.eq_nil_of_length_eq_zero (by simpa [VineType.template] using hk)
  subst this
  rw [← Finset.card_image_of_injOn hinj, himg, Finset.card_range]
  rfl

theorem IsVineXU.verts_I {X : UMultigraph V} {p q : V} (h : IsVineXU .I X p q) : X.verts = {p, q} := by
  have hB := h.1
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    exacts [hB.1, hB.2.1]
  · rw [h.card_I, Finset.card_pair hB.2.2.1]

/-- **The ingredient step for every kind**, from the (II) step and the T-vine cap step. -/
theorem ingConcl_of
    (hII : ∀ (X : UMultigraph V) (p q a b xm xp ym yp : V) (Km Kp : Finset V) (μ : Bool),
      IsVineXU .II X p q → RungCore X a b xm xp ym yp Km Kp → a ≠ p → a ≠ q → b ≠ p → b ≠ q →
      IsVineXU .II (rungDel X a b xm xp ym yp μ) p q ∨
        (X.verts = {p, a, b, q} ∧ IsVineXU .I (rungDel X a b xm xp ym yp μ) p q ∧
          ((Km = {p} ∧ Kp = {q}) ∨ (Km = {q} ∧ Kp = {p}))))
    (hcap : ∀ (X : UMultigraph V) (p q a b xm xp ym yp : V) (Km Kp : Finset V) (μ : Bool),
      IsTVineU X p q → RungCore X a b xm xp ym yp Km Kp → a ≠ p → a ≠ q → b ≠ p → b ≠ q →
      IsCapAt p q Km Kp → IsTVineU (rungDel X a b xm xp ym yp μ) p q)
    (k : EnlKind) (X : UMultigraph V) (p q a b xm xp ym yp : V) (Km Kp : Finset V) (μ : Bool)
    (hv : IsVineKindU k X p q) (hR : RungCore X a b xm xp ym yp Km Kp) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q) : IngConcl k X p q a b xm xp ym yp μ := by
  cases k with
  | I =>
    exfalso
    have ha := hR.a_verts
    rw [IsVineXU.verts_I (X := X) hv] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with h | h
    exacts [hap h, haq h]
  | II =>
    rcases hII X p q a b xm xp ym yp Km Kp μ hv hR hap haq hbp hbq with h | ⟨hverts, hI, hpoles⟩
    · exact Or.inl h
    · refine Or.inr ⟨rfl, hI, hverts, ?_⟩
      have hxm := hR.xm_mem
      have hym := hR.ym_mem
      have hxp := hR.xp_mem
      have hyp := hR.yp_mem
      rcases hpoles with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, Finset.mem_singleton] at hxm hym
        rw [h2, Finset.mem_singleton] at hxp hyp
        exact Or.inl ⟨hxm, hym, hxp, hyp⟩
      · rw [h1, Finset.mem_singleton] at hxm hym
        rw [h2, Finset.mem_singleton] at hxp hyp
        exact Or.inr ⟨hxm, hym, hxp, hyp⟩
  | T =>
    left
    by_cases hc : IsCapAt p q Km Kp
    · exact hcap X p q a b xm xp ym yp Km Kp μ hv hR hap haq hbp hbq hc
    · exact isTVineU_rungDel_of_noncap hv hR hap haq hbp hbq hc μ

end WaveTurbulence.TVine.Core
