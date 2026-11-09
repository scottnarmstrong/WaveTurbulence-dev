/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Phi

/-!
# N2 Lemma 1.14(b): `Φ(U)` is a sub-object of `G/[μ]R` of the same kind

* `IsBlockU.rungDel_of_rungCore`: deleting a rung (rung data, joints off the rung) inside a block keeps a block; the
  connectivity uses parity: a closed set of the deleted graph meets each pole in a set with an even number of rails;
* `RungCore.induce`, `RungCore.eraseBond`, `induce_rungDel`, `eraseBond_rungDel`: the deletion commutes with taking
  `E(S)` and with removing the adjoint bond;
* `phiSubObj_holds : PhiSubObjStatement`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

section Block

variable {H : UMultigraph V} {k₁ k₂ a b xm xp ym yp : V} {Km Kp : Finset V}

/-- Deleting a rung inside a block (rung atoms not joints) keeps it a block. -/
theorem IsBlockU.rungDel_of_rungCore (hH : IsBlockU H k₁ k₂) (hR : RungCore H a b xm xp ym yp Km Kp)
    (h1a : k₁ ≠ a) (h1b : k₁ ≠ b) (h2a : k₂ ≠ a) (h2b : k₂ ≠ b) (μ : Bool) :
    IsBlockU (rungDel H a b xm xp ym yp μ) k₁ k₂ := by
  classical
  obtain ⟨hk₁V, hk₂V, hk, hd₁, hd₂, hd, hconn⟩ := hH
  have hV : (rungDel H a b xm xp ym yp μ).verts = (H.verts.erase a).erase b := hR.verts_rungDel μ
  refine ⟨by rw [hV]; simp [h1a, h1b, hk₁V], by rw [hV]; simp [h2a, h2b, hk₂V], hk,
    by rw [hR.deg_rungDel μ h1a h1b]; exact hd₁, by rw [hR.deg_rungDel μ h2a h2b]; exact hd₂, ?_, ?_⟩
  · intro v hv hv1 hv2
    rw [hV] at hv; simp only [Finset.mem_erase] at hv
    rw [hR.deg_rungDel μ hv.2.1 hv.1]; exact hd v hv.2.2 hv1 hv2
  -- connectivity
  apply connected_of_closed
  intro X hX hne hcl
  rw [hV] at hX hcl ⊢
  set H' := rungDel H a b xm xp ym yp μ
  have hXab : ∀ x ∈ X, x ≠ a ∧ x ≠ b ∧ x ∈ H.verts := fun x hx => by
    have := hX hx; simp only [Finset.mem_erase] at this; exact ⟨this.2.1, this.1, this.2.2⟩
  have hpole : ∀ x ∈ X, x ∈ Km ∨ x ∈ Kp := fun x hx =>
    hR.mem_poles (hXab x hx).2.2 (hXab x hx).1 (hXab x hx).2.1
  have hmemV : ∀ {x}, (x ∈ Km ∨ x ∈ Kp) → x ∈ (H.verts.erase a).erase b := fun hx => by
    obtain ⟨h1, h2, h3⟩ := hR.mem_verts hx; simp [h1, h2, h3]
  -- old bonds inside a pole are bonds of `H'`
  have hold : ∀ u ∈ X, ∀ w, ((u ∈ Km ∧ w ∈ Km) ∨ (u ∈ Kp ∧ w ∈ Kp)) → H.mult s(u, w) ≠ 0 → w ∈ X := by
    intro u hu w hw hm
    refine hcl u hu w (hmemV (by tauto)) ?_
    rw [show H' = rungDel H a b xm xp ym yp μ from rfl, hR.rungDel_mult_same μ hw]; exact hm
  -- new bonds
  have hnew : ∀ u v, s(u, v) ∈ rungAdds xm xp ym yp μ → (u ∈ X ↔ v ∈ X) := by
    intro u v hm
    have huv : ((u ∈ Km ∧ v ∈ Kp) ∨ (u ∈ Kp ∧ v ∈ Km)) := by
      cases μ <;> simp only [rungAdds, Bool.false_eq_true, if_false, if_true, Multiset.insert_eq_cons,
        Multiset.mem_cons, Multiset.mem_singleton] at hm <;>
        rcases hm with hm | hm <;> rcases Sym2.eq_iff.mp hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals first
        | exact Or.inl ⟨hR.xm_mem, hR.xp_mem⟩ | exact Or.inl ⟨hR.ym_mem, hR.yp_mem⟩
        | exact Or.inr ⟨hR.xp_mem, hR.xm_mem⟩ | exact Or.inr ⟨hR.yp_mem, hR.ym_mem⟩
        | exact Or.inl ⟨hR.xm_mem, hR.yp_mem⟩ | exact Or.inl ⟨hR.ym_mem, hR.xp_mem⟩
        | exact Or.inr ⟨hR.yp_mem, hR.xm_mem⟩ | exact Or.inr ⟨hR.xp_mem, hR.ym_mem⟩
    have hm' : H'.mult s(u, v) ≠ 0 := by
      rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · rw [show H' = rungDel H a b xm xp ym yp μ from rfl, hR.rungDel_mult_cross hu hv]
        exact Multiset.count_ne_zero.mpr hm
      · rw [show H' = rungDel H a b xm xp ym yp μ from rfl, Sym2.eq_swap, hR.rungDel_mult_cross hv hu]
        rw [Sym2.eq_swap] at hm; exact Multiset.count_ne_zero.mpr hm
    constructor
    · intro hu; exact hcl u hu v (hmemV (by tauto)) hm'
    · intro hv; exact hcl v hv u (hmemV (by tauto)) (by rw [Sym2.eq_swap]; exact hm')
  -- parity on each pole: a pole meets `X` in an even number of rails
  have hparity : ∀ {K L : Finset V} {x y : V}, (K = Km ∧ L = Kp ∧ x = xm ∧ y = ym ∨
      K = Kp ∧ L = Km ∧ x = xp ∧ y = yp) → (x ∈ X ↔ y ∈ X) := by
    intro K L x y hKL
    have hev := IsBlockU.even_cut ⟨hk₁V, hk₂V, hk, hd₁, hd₂, hd, hconn⟩ (Y := X.filter (· ∈ K))
      (fun z hz => (hXab z (Finset.mem_filter.mp hz).1).2.2)
    have hcut : cut H (X.filter (· ∈ K)) = (if x ∈ X then 1 else 0) + (if y ∈ X then 1 else 0) := by
      have hrow : ∀ z ∈ X.filter (· ∈ K), ∑ w ∈ H.verts \ X.filter (· ∈ K), H.mult s(z, w) =
          (if z = x then 1 else 0) + (if z = y then 1 else 0) := by
        intro z hz
        obtain ⟨hzX, hzK⟩ := Finset.mem_filter.mp hz
        obtain ⟨hza, hzb, hzV⟩ := hXab z hzX
        have haS : a ∈ H.verts \ X.filter (· ∈ K) := Finset.mem_sdiff.mpr ⟨hR.a_verts, fun h =>
          (hXab a (Finset.mem_filter.mp h).1).1 rfl⟩
        have hbS : b ∈ H.verts \ X.filter (· ∈ K) := Finset.mem_sdiff.mpr ⟨hR.b_verts, fun h =>
          (hXab b (Finset.mem_filter.mp h).1).2.1 rfl⟩
        have hab : a ≠ b := hR.ne
        have hzero : ∀ w ∈ ((H.verts \ X.filter (· ∈ K)).erase a).erase b, H.mult s(z, w) = 0 := by
          intro w hw
          simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_filter, not_and] at hw
          obtain ⟨hwb, hwa, hwV, hwX⟩ := hw
          by_contra hm
          rcases hR.mem_poles hwV hwa hwb with hwK | hwK
          · rcases hKL with ⟨rfl, rfl, -, -⟩ | ⟨rfl, rfl, -, -⟩
            · exact hwX (hold z hzX w (Or.inl ⟨hzK, hwK⟩) hm) hwK
            · exact hm (by rw [Sym2.eq_swap]; exact hR.noBond w hwK z hzK)
          · rcases hKL with ⟨rfl, rfl, -, -⟩ | ⟨rfl, rfl, -, -⟩
            · exact hm (hR.noBond z hzK w hwK)
            · exact hwX (hold z hzX w (Or.inr ⟨hzK, hwK⟩) hm) hwK
        rw [← Finset.add_sum_erase _ _ haS, ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hab.symm, hbS⟩),
          Finset.sum_eq_zero hzero, add_zero, Sym2.eq_swap, hR.mult_a z, Sym2.eq_swap, hR.mult_b z,
          if_neg hzb, if_neg hza]
        rcases hKL with ⟨hK, -, hx, hy⟩ | ⟨hK, -, hx, hy⟩
        · rw [hK] at hzK
          have hzp : z ≠ xp := fun h => hR.not_mem_both hzK (h ▸ hR.xp_mem)
          have hzq : z ≠ yp := fun h => hR.not_mem_both hzK (h ▸ hR.yp_mem)
          rw [hx, hy]
          simp only [hzp, hzq, or_false]
        · rw [hK] at hzK
          have hzp : z ≠ xm := fun h => hR.not_mem_both (h ▸ hR.xm_mem) hzK
          have hzq : z ≠ ym := fun h => hR.not_mem_both (h ▸ hR.ym_mem) hzK
          rw [hx, hy]
          simp only [hzp, hzq, false_or]
      unfold cut
      rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      have hxK : x ∈ K := by rcases hKL with ⟨rfl, -, rfl, -⟩ | ⟨rfl, -, rfl, -⟩; exacts [hR.xm_mem, hR.xp_mem]
      have hyK : y ∈ K := by rcases hKL with ⟨rfl, -, -, rfl⟩ | ⟨rfl, -, -, rfl⟩; exacts [hR.ym_mem, hR.yp_mem]
      simp [Finset.mem_filter, hxK, hyK]
    rw [hcut] at hev
    by_cases h1 : x ∈ X <;> by_cases h2 : y ∈ X <;> simp [h1, h2] at hev ⊢ <;> exact absurd hev (by decide)
  have hm := hparity (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  have hp := hparity (Or.inr ⟨rfl, rfl, rfl, rfl⟩)
  -- the matching links the two poles
  have hlink : xm ∈ X ↔ xp ∈ X := by
    cases μ
    · exact hnew xm xp (by simp [rungAdds])
    · exact (hnew xm yp (by simp [rungAdds])).trans hp.symm
  -- either all rail ends are in `X` or none
  by_cases hall : xm ∈ X
  · set Y := insert a (insert b X) with hY
    have hYV : Y ⊆ H.verts := by
      intro z hz; simp only [hY, Finset.mem_insert] at hz
      rcases hz with rfl | rfl | hz
      · exact hR.a_verts
      · exact hR.b_verts
      · exact (hXab z hz).2.2
    have hYc : ∀ u ∈ Y, ∀ w ∈ H.verts, H.mult s(u, w) ≠ 0 → w ∈ Y := by
      intro u hu w hw hmw
      simp only [hY, Finset.mem_insert] at hu ⊢
      rcases hu with rfl | rfl | hu
      · rw [hR.mult_a] at hmw
        by_cases h1 : w = b
        · exact Or.inr (Or.inl h1)
        · rw [if_neg h1] at hmw
          by_cases h2 : w = xm ∨ w = xp
          · rcases h2 with rfl | rfl
            · exact Or.inr (Or.inr hall)
            · exact Or.inr (Or.inr (hlink.mp hall))
          · rw [if_neg h2] at hmw; exact absurd rfl hmw
      · rw [hR.mult_b] at hmw
        by_cases h1 : w = a
        · exact Or.inl h1
        · rw [if_neg h1] at hmw
          by_cases h2 : w = ym ∨ w = yp
          · rcases h2 with rfl | rfl
            · exact Or.inr (Or.inr (hm.mp hall))
            · exact Or.inr (Or.inr (hp.mp (hlink.mp hall)))
          · rw [if_neg h2] at hmw; exact absurd rfl hmw
      · by_cases hwa : w = a
        · exact Or.inl hwa
        by_cases hwb : w = b
        · exact Or.inr (Or.inl hwb)
        right; right
        rcases hpole u hu with huK | huK <;> rcases hR.mem_poles hw hwa hwb with hwK | hwK
        · exact hold u hu w (Or.inl ⟨huK, hwK⟩) hmw
        · exact absurd (hR.noBond u huK w hwK) hmw
        · exact absurd (by rw [Sym2.eq_swap]; exact hR.noBond w hwK u huK) hmw
        · exact hold u hu w (Or.inr ⟨huK, hwK⟩) hmw
    have hYall := eq_of_closed' hconn hYV ⟨a, by simp [hY]⟩ hYc
    apply Finset.Subset.antisymm hX
    intro z hz
    simp only [Finset.mem_erase] at hz
    have : z ∈ Y := by rw [hYall]; exact hz.2.2
    simp only [hY, Finset.mem_insert] at this
    rcases this with h | h | h
    · exact absurd h hz.2.1
    · exact absurd h hz.1
    · exact h
  · -- no rail end in `X`: `X` is closed in `H`, absurd
    exfalso
    have hxp : xp ∉ X := fun h => hall (hlink.mpr h)
    have hym : ym ∉ X := fun h => hall (hm.mpr h)
    have hyp : yp ∉ X := fun h => hxp (hp.mpr h)
    have hXc : ∀ u ∈ X, ∀ w ∈ H.verts, H.mult s(u, w) ≠ 0 → w ∈ X := by
      intro u hu w hw hmw
      obtain ⟨hua, hub, -⟩ := hXab u hu
      by_cases hwa : w = a
      · subst hwa
        rw [Sym2.eq_swap, hR.mult_a, if_neg hub] at hmw
        by_cases h2 : u = xm ∨ u = xp
        · rcases h2 with rfl | rfl
          · exact absurd hu hall
          · exact absurd hu hxp
        · rw [if_neg h2] at hmw; exact absurd rfl hmw
      by_cases hwb : w = b
      · subst hwb
        rw [Sym2.eq_swap, hR.mult_b, if_neg hua] at hmw
        by_cases h2 : u = ym ∨ u = yp
        · rcases h2 with rfl | rfl
          · exact absurd hu hym
          · exact absurd hu hyp
        · rw [if_neg h2] at hmw; exact absurd rfl hmw
      rcases hpole u hu with huK | huK <;> rcases hR.mem_poles hw hwa hwb with hwK | hwK
      · exact hold u hu w (Or.inl ⟨huK, hwK⟩) hmw
      · exact absurd (hR.noBond u huK w hwK) hmw
      · exact absurd (by rw [Sym2.eq_swap]; exact hR.noBond w hwK u huK) hmw
      · exact hold u hu w (Or.inr ⟨huK, hwK⟩) hmw
    have hXall := eq_of_closed' hconn (fun x hx => (hXab x hx).2.2) hne hXc
    have : a ∈ X := by rw [hXall]; exact hR.a_verts
    exact (hXab a this).1 rfl

end Block

section Commute

variable {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}

/-- Rung data restricted to an atom set containing the rung and its rails. -/
theorem RungCore.restrict (hR : RungCore G a b xm xp ym yp Km Kp) {S : Finset V} (hSV : S ⊆ G.verts)
    (haS : a ∈ S) (hbS : b ∈ S) (hxm : xm ∈ S) (hxp : xp ∈ S) (hym : ym ∈ S) (hyp : yp ∈ S) :
    RungCore (induce G S) a b xm xp ym yp (Km ∩ S) (Kp ∩ S) where
  ne := hR.ne
  mult_a x := by
    by_cases hx : x ∈ S
    · rw [induce_mult_of_mem G haS hx, hR.mult_a]
    · have hxb : x ≠ b := fun h => hx (h ▸ hbS)
      have hxx : ¬ (x = xm ∨ x = xp) := by
        rintro (h | h)
        · exact hx (h ▸ hxm)
        · exact hx (h ▸ hxp)
      rw [induce_mult_of_not_mem G hx, if_neg hxb, if_neg hxx]
  mult_b x := by
    by_cases hx : x ∈ S
    · rw [induce_mult_of_mem G hbS hx, hR.mult_b]
    · have hxa : x ≠ a := fun h => hx (h ▸ haS)
      have hxx : ¬ (x = ym ∨ x = yp) := by
        rintro (h | h)
        · exact hx (h ▸ hym)
        · exact hx (h ▸ hyp)
      rw [induce_mult_of_not_mem G hx, if_neg hxa, if_neg hxx]
  disj := Finset.disjoint_of_subset_left Finset.inter_subset_left
    (Finset.disjoint_of_subset_right Finset.inter_subset_left hR.disj)
  union := by
    rw [show (induce G S).verts = S from rfl]
    ext x
    have hu := Finset.ext_iff.mp hR.union x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_erase] at hu ⊢
    constructor
    · rintro (⟨h, hx⟩ | ⟨h, hx⟩)
      · exact ⟨(hu.mp (Or.inl h)).1, (hu.mp (Or.inl h)).2.1, hx⟩
      · exact ⟨(hu.mp (Or.inr h)).1, (hu.mp (Or.inr h)).2.1, hx⟩
    · rintro ⟨h1, h2, hx⟩
      rcases hu.mpr ⟨h1, h2, hSV hx⟩ with h | h
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr ⟨h, hx⟩
  noBond u hu w hw := by
    rw [induce_mult_of_mem G (Finset.mem_inter.mp hu).2 (Finset.mem_inter.mp hw).2]
    exact hR.noBond u (Finset.mem_inter.mp hu).1 w (Finset.mem_inter.mp hw).1
  xm_mem := Finset.mem_inter.mpr ⟨hR.xm_mem, hxm⟩
  xp_mem := Finset.mem_inter.mpr ⟨hR.xp_mem, hxp⟩
  ym_mem := Finset.mem_inter.mpr ⟨hR.ym_mem, hym⟩
  yp_mem := Finset.mem_inter.mpr ⟨hR.yp_mem, hyp⟩

/-- Rung data survives removing one copy of a bond avoiding the rung. -/
theorem RungCore.eraseBond (hR : RungCore G a b xm xp ym yp Km Kp) {k₁ k₂ : V} (h1a : k₁ ≠ a)
    (h1b : k₁ ≠ b) (h2a : k₂ ≠ a) (h2b : k₂ ≠ b) :
    RungCore (eraseBond G s(k₁, k₂)) a b xm xp ym yp Km Kp where
  ne := hR.ne
  mult_a x := by
    show (if s(a, x) = s(k₁, k₂) then G.mult s(a, x) - 1 else G.mult s(a, x)) = _
    rw [if_neg (fun h => by rcases Sym2.eq_iff.mp h with ⟨h', _⟩ | ⟨h', _⟩; exacts [h1a h'.symm, h2a h'.symm]),
      hR.mult_a]
  mult_b x := by
    show (if s(b, x) = s(k₁, k₂) then G.mult s(b, x) - 1 else G.mult s(b, x)) = _
    rw [if_neg (fun h => by rcases Sym2.eq_iff.mp h with ⟨h', _⟩ | ⟨h', _⟩; exacts [h1b h'.symm, h2b h'.symm]),
      hR.mult_b]
  disj := hR.disj
  union := hR.union
  noBond u hu w hw := by
    show (if s(u, w) = s(k₁, k₂) then G.mult s(u, w) - 1 else G.mult s(u, w)) = 0
    rw [hR.noBond u hu w hw]; split_ifs <;> rfl
  xm_mem := hR.xm_mem
  xp_mem := hR.xp_mem
  ym_mem := hR.ym_mem
  yp_mem := hR.yp_mem

/-- Deletion commutes with taking `E(S)` (rung and rails in `S`). -/
theorem induce_rungDel (hR : RungCore G a b xm xp ym yp Km Kp) {S : Finset V} (haS : a ∈ S) (hbS : b ∈ S)
    (hxm : xm ∈ S) (hxp : xp ∈ S) (hym : ym ∈ S) (hyp : yp ∈ S) (μ : Bool) :
    induce (rungDel G a b xm xp ym yp μ) ((S.erase a).erase b) = rungDel (induce G S) a b xm xp ym yp μ := by
  have hadds : ∀ f ∈ rungAdds xm xp ym yp μ, ∀ x ∈ f, x ∈ S := by
    intro f hf x hx
    cases μ <;> simp only [rungAdds, Bool.false_eq_true, if_false, if_true, Multiset.insert_eq_cons,
      Multiset.mem_cons, Multiset.mem_singleton] at hf <;>
      rcases hf with rfl | rfl <;> rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption
  apply ext
  · show (S.erase a).erase b = (rungDel (induce G S) a b xm xp ym yp μ).verts
    unfold rungDel
    rw [splice_verts_of_subset _ _ _ hadds]; rfl
  · intro e
    show (if e ∈ ((S.erase a).erase b).sym2 then (rungDel G a b xm xp ym yp μ).mult e else 0) =
      (rungDel (induce G S) a b xm xp ym yp μ).mult e
    rw [rungDel_mult, rungDel_mult]
    by_cases hab : a ∈ e ∨ b ∈ e
    · rw [if_pos hab, if_pos hab]; split_ifs <;> rfl
    · rw [if_neg hab, if_neg hab]
      have hiff : e ∈ ((S.erase a).erase b).sym2 ↔ e ∈ S.sym2 := by
        simp only [Finset.mem_sym2_iff, Finset.mem_erase]
        constructor
        · intro h x hx; exact (h x hx).2.2
        · intro h x hx
          refine ⟨fun h' => hab (Or.inr (h' ▸ hx)), fun h' => hab (Or.inl (h' ▸ hx)), h x hx⟩
      show _ = (if e ∈ S.sym2 then G.mult e else 0) + _
      by_cases he : e ∈ S.sym2
      · rw [if_pos (hiff.mpr he), if_pos he]
      · rw [if_neg (mt hiff.mp he), if_neg he, zero_add]
        symm; apply Multiset.count_eq_zero.mpr
        intro hf; apply he
        rw [Finset.mem_sym2_iff]; exact hadds e hf

/-- Deletion commutes with removing a copy of a bond avoiding the rung. -/
theorem eraseBond_rungDel (H : UMultigraph V) {k₁ k₂ : V} (h1a : k₁ ≠ a) (h1b : k₁ ≠ b) (h2a : k₂ ≠ a)
    (h2b : k₂ ≠ b) (hm : H.mult s(k₁, k₂) ≠ 0) (μ : Bool) :
    eraseBond (rungDel H a b xm xp ym yp μ) s(k₁, k₂) = rungDel (eraseBond H s(k₁, k₂)) a b xm xp ym yp μ := by
  apply ext
  · rfl
  · intro e
    show (if e = s(k₁, k₂) then (rungDel H a b xm xp ym yp μ).mult e - 1 else (rungDel H a b xm xp ym yp μ).mult e)
      = (rungDel (eraseBond H s(k₁, k₂)) a b xm xp ym yp μ).mult e
    rw [rungDel_mult, rungDel_mult]
    show _ = if a ∈ e ∨ b ∈ e then 0 else
      (if e = s(k₁, k₂) then H.mult e - 1 else H.mult e) + (rungAdds xm xp ym yp μ).count e
    by_cases he : e = s(k₁, k₂)
    · subst he
      have hab : ¬ (a ∈ s(k₁, k₂) ∨ b ∈ s(k₁, k₂)) := by
        rintro (h | h) <;> rcases Sym2.mem_iff.mp h with h | h
        exacts [h1a h.symm, h2a h.symm, h1b h.symm, h2b h.symm]
      rw [if_pos rfl, if_neg hab, if_neg hab, if_pos rfl]
      omega
    · rw [if_neg he, if_neg he]

end Commute

/-- A sub-object avoiding the rung lies in one pole. -/
theorem IsSubObjU.atoms_in_pole {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V} {U : SubObj V}
    (hR : RungCore G a b xm xp ym yp Km Kp) (hU : IsSubObjU G U) (ha : a ∉ U.atoms) (hb : b ∉ U.atoms) :
    U.atoms ⊆ Km ∨ U.atoms ⊆ Kp := by
  classical
  have hconn := hU.2.2.2.2.2.2.2.2
  rw [Connected, SubObj.core_verts] at hconn
  have hmcore : ∀ u w, (U.core G).mult s(u, w) ≤ G.mult s(u, w) := by
    intro u w
    unfold SubObj.core; split
    · show (if s(u, w) = s(U.k₁, U.k₂) then (induce G U.atoms).mult s(u, w) - 1
        else (induce G U.atoms).mult s(u, w)) ≤ _
      have : (induce G U.atoms).mult s(u, w) ≤ G.mult s(u, w) := by
        show (if s(u, w) ∈ U.atoms.sym2 then G.mult s(u, w) else 0) ≤ _; split_ifs <;> omega
      split_ifs <;> omega
    · show (if s(u, w) ∈ U.atoms.sym2 then G.mult s(u, w) else 0) ≤ _; split_ifs <;> omega
  have hpole : ∀ x ∈ U.atoms, x ∈ Km ∨ x ∈ Kp := fun x hx =>
    hR.mem_poles (hU.atoms_subset hx) (fun h => ha (h ▸ hx)) (fun h => hb (h ▸ hx))
  obtain ⟨x₀, hx₀⟩ : U.atoms.Nonempty := ⟨U.k₁, hU.k₁_mem⟩
  have key : ∀ K, (K = Km ∨ K = Kp) → x₀ ∈ K → U.atoms ⊆ K := by
    intro K hK hx₀K
    have hT := eq_of_closed' hconn (S := U.atoms.filter (· ∈ K)) (Finset.filter_subset _ _)
      ⟨x₀, Finset.mem_filter.mpr ⟨hx₀, hx₀K⟩⟩ (by
        intro u hu w hw hm
        obtain ⟨huS, huK⟩ := Finset.mem_filter.mp hu
        refine Finset.mem_filter.mpr ⟨hw, ?_⟩
        have hG : G.mult s(u, w) ≠ 0 := fun h => hm (Nat.le_zero.mp (h ▸ hmcore u w))
        rcases hpole w hw with hwK | hwK <;> rcases hK with rfl | rfl
        · exact hwK
        · exact absurd (by rw [Sym2.eq_swap]; exact hR.noBond w hwK u huK) hG
        · exact absurd (hR.noBond u huK w hwK) hG
        · exact hwK)
    intro x hx
    have : x ∈ U.atoms.filter (· ∈ K) := by rw [hT]; exact hx
    exact (Finset.mem_filter.mp this).2
  rcases hpole x₀ hx₀ with h | h
  · exact Or.inl (key Km (Or.inl rfl) h)
  · exact Or.inr (key Kp (Or.inr rfl) h)

/-- **N2 Lemma 1.14(b)** (`Φ(U)` is a sub-object of `G/[μ]R` of the same kind). -/
theorem phiSubObj_holds : PhiSubObjStatement.{u} := by
  intro V _ G j₁ j₂ a b xm xp ym yp Km Kp U μ hB hl hR hU h1a h1b h2a h2b
  have hU0 := hU
  have hRR := hR
  obtain ⟨hR', -, -, -, -⟩ := hR
  have hRc := hR'.toCore
  have hVR : (rungDel G a b xm xp ym yp μ).verts = (G.verts.erase a).erase b := hRc.verts_rungDel μ
  have hSV := hU.atoms_subset
  rcases phiAllInOut_holds G j₁ j₂ a b xm xp ym yp Km Kp U hB hl hRR hU h1a h1b h2a h2b with
    ⟨haI, hbI, hxm, hxp, hym, hyp⟩ | ⟨ha, hb⟩
  · -- all-in
    have haS : a ∈ U.atoms := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase haI)
    have hbS : b ∈ U.atoms := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hbI)
    have hRS := hRc.restrict hSV haS hbS hxm hxp hym hyp
    obtain ⟨hsub, hadj, hcore⟩ := hU
    refine ⟨?_, ?_, ?_⟩
    · -- proper
      rw [hVR]
      refine Finset.ssubset_iff_subset_ne.mpr ⟨fun x hx => ?_, fun h => ?_⟩
      · simp only [SubObj.phi, Finset.mem_erase] at hx ⊢; exact ⟨hx.1, hx.2.1, hSV hx.2.2⟩
      · obtain ⟨z, hzV, hzS⟩ := Finset.exists_of_ssubset hsub
        have hza : z ≠ a := fun h => hzS (h ▸ haS)
        have hzb : z ≠ b := fun h => hzS (h ▸ hbS)
        have : z ∈ (U.phi a b).atoms := by rw [h]; simp [hza, hzb, hzV]
        simp only [SubObj.phi, Finset.mem_erase] at this
        exact hzS this.2.2
    · intro hh
      have := hadj hh
      rw [rungDel_mult, if_neg (by
        rintro (h | h) <;> rcases Sym2.mem_iff.mp h with h | h
        exacts [h1a h.symm, h2a h.symm, h1b h.symm, h2b h.symm])]
      simp only [SubObj.phi]; omega
    · -- the core of `Φ(U)` is the deletion inside the core of `U`
      have hedge : (U.phi a b).edges (rungDel G a b xm xp ym yp μ) =
          rungDel (U.edges G) a b xm xp ym yp μ := induce_rungDel hRc haS hbS hxm hxp hym hyp μ
      cases hh : U.hyper
      · have hc1 : (U.phi a b).core (rungDel G a b xm xp ym yp μ) = rungDel (U.edges G) a b xm xp ym yp μ := by
          rw [← hedge]; simp [SubObj.core, SubObj.phi, hh]
        have hc0 : U.core G = U.edges G := by simp [SubObj.core, hh]
        rw [hc1]
        rw [hc0] at hcore
        exact hcore.rungDel_of_rungCore hRS h1a h1b h2a h2b μ
      · have hmE : (U.edges G).mult s(U.k₁, U.k₂) ≠ 0 := by
          rw [SubObj.edges, induce_mult_of_mem G hU0.k₁_mem hU0.k₂_mem]; exact hadj hh
        have hc1 : (U.phi a b).core (rungDel G a b xm xp ym yp μ) =
            rungDel (eraseBond (U.edges G) s(U.k₁, U.k₂)) a b xm xp ym yp μ := by
          rw [← eraseBond_rungDel _ h1a h1b h2a h2b hmE, ← hedge]; simp [SubObj.core, SubObj.phi, hh]
        have hc0 : U.core G = eraseBond (U.edges G) s(U.k₁, U.k₂) := by simp [SubObj.core, hh]
        rw [hc1]
        rw [hc0] at hcore
        exact hcore.rungDel_of_rungCore (hRS.eraseBond h1a h1b h2a h2b) h1a h1b h2a h2b μ
  · -- all-out
    have hphi : U.phi a b = U := by
      simp only [SubObj.phi, Finset.erase_eq_of_notMem ha, Finset.erase_eq_of_notMem hb]
    rw [hphi]
    have hpole := hU.atoms_in_pole hRc ha hb
    have hsame : ∀ u ∈ U.atoms, ∀ w ∈ U.atoms,
        (rungDel G a b xm xp ym yp μ).mult s(u, w) = G.mult s(u, w) := by
      intro u hu w hw
      by_cases huw : u = w
      · subst huw
        rw [rungDel_mult, if_neg (by
          rintro (h | h) <;> rcases Sym2.mem_iff.mp h with h | h <;>
          first | exact ha (h ▸ hu) | exact hb (h ▸ hu)), hRc.rungAdds_count_diag, add_zero]
      · rcases hpole with h | h
        · exact hRc.rungDel_mult_same μ (Or.inl ⟨h hu, h hw⟩)
        · exact hRc.rungDel_mult_same μ (Or.inr ⟨h hu, h hw⟩)
    have hedge : U.edges (rungDel G a b xm xp ym yp μ) = U.edges G := by
      apply ext
      · rfl
      · intro e
        show (if e ∈ U.atoms.sym2 then (rungDel G a b xm xp ym yp μ).mult e else 0) =
          (if e ∈ U.atoms.sym2 then G.mult e else 0)
        split_ifs with he
        · induction e using Sym2.ind with
          | h u w =>
            rw [Finset.mem_sym2_iff] at he
            exact hsame u (he u (Sym2.mem_mk_left u w)) w (he w (Sym2.mem_mk_right u w))
        · rfl
    obtain ⟨hsub, hadj, hcore⟩ := hU
    refine ⟨?_, ?_, ?_⟩
    · rw [hVR]
      refine Finset.ssubset_iff_subset_ne.mpr ⟨fun x hx => ?_, fun h => ?_⟩
      · simp only [Finset.mem_erase]
        exact ⟨fun h' => hb (h' ▸ hx), fun h' => ha (h' ▸ hx), hSV hx⟩
      · -- both poles are nonempty, `U` lies in one
        rcases hpole with hK | hK
        · have : xp ∈ U.atoms := by
            rw [h]; obtain ⟨h1, h2, h3⟩ := hRc.mem_verts (Or.inr hRc.xp_mem); simp [h1, h2, h3]
          exact hRc.not_mem_both (hK this) hRc.xp_mem
        · have : xm ∈ U.atoms := by
            rw [h]; obtain ⟨h1, h2, h3⟩ := hRc.mem_verts (Or.inl hRc.xm_mem); simp [h1, h2, h3]
          exact hRc.not_mem_both hRc.xm_mem (hK this)
    · intro hh
      rw [hsame U.k₁ (SubObj.core_verts G U ▸ hcore.1) U.k₂ (SubObj.core_verts G U ▸ hcore.2.1)]
      exact hadj hh
    · have : U.core (rungDel G a b xm xp ym yp μ) = U.core G := by
        unfold SubObj.core; rw [hedge]
      rw [this]; exact hcore

end WaveTurbulence.TVine.Core
