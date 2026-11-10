/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.PhiType

/-!
# Deleting a cap rung of a T-vine (N3 §2.1 (ii), second bullet): preliminaries

* `IsClosureU.swap`, `IsTVineU.swap`: exchanging the joints;
* `rungDel_block_of_tvine`: deleting any rung (given by rung data) of a T-vine gives a block with multiplicities
  at most `2`;
* indicator / pair bookkeeping (`sym2_ne_of`, `not_mem_sym2`, `forall_mem_pair`, `ind_left`, `ind_right`,
  `pair_ne_of_count`, `eq_of_pair_eq_pair`);
* `nbrs_eq_of_two`, `nbrs_splice_of`: neighbour multisets of a degree-`2` atom, and after a splice;
* `not_reducesToT_of_stuck`, `y2Pair_of_reducesToT`: a triple pair of a graph reducing to `T` is a (Y2) pair;
* `closure_mult_a`, `rail_closed*`: the bonds at a rung atom in a closure;
* `isClosureU_y2Move`: **assembly** — the (Y2) move of the old closure is a closure of the deleted graph;
* `rungAdds_capA`: when one joint carries both rails of a pole, both matchings add the same bonds.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

/-! ## Joint swap -/

theorem IsClosureU.swap {G C : UMultigraph V} {j₁ j₂ : V} (h : IsClosureU G j₁ j₂ C) : IsClosureU G j₂ j₁ C := by
  obtain ⟨hσ, hV, hl, added, hdata, hm⟩ := h
  have hs : G.mult s(j₂, j₁) = G.mult s(j₁, j₂) := by rw [Sym2.eq_swap]
  refine ⟨by rw [hs]; exact hσ, by rw [hV]; exact Finset.erase_right_comm, hl, added, ?_, fun e => ?_⟩
  · rcases hdata with ⟨h0, a, b, c, d, h1, h2, rfl⟩ | ⟨h1', x, y, h1, h2, rfl⟩
    · exact Or.inl ⟨by rw [hs]; exact h0, c, d, a, b, h2, h1, Multiset.pair_comm _ _⟩
    · exact Or.inr ⟨by rw [hs]; exact h1', y, x, h2, h1, by rw [Sym2.eq_swap]⟩
  · rw [hm e]; congr 1; exact if_congr or_comm rfl rfl

theorem IsTVineU.swap {G : UMultigraph V} {j₁ j₂ : V} (h : IsTVineU G j₁ j₂) : IsTVineU G j₂ j₁ := by
  obtain ⟨hB, hm, C, hC, hRT⟩ := h
  exact ⟨hB.swap, hm, C, hC.swap, hRT⟩

/-! ## The block part -/

/-- Deleting a rung (rung atoms not joints) of a T-vine gives a block with multiplicities at most `2`. -/
theorem rungDel_block_of_tvine {X : UMultigraph V} {p q a b xm xp ym yp : V} {Km Kp : Finset V}
    (hT : IsTVineU X p q) (hR : RungCore X a b xm xp ym yp Km Kp) (hap : a ≠ p) (haq : a ≠ q) (hbp : b ≠ p)
    (hbq : b ≠ q) (μ : Bool) :
    IsBlockU (rungDel X a b xm xp ym yp μ) p q ∧
      ∀ u ∈ (rungDel X a b xm xp ym yp μ).verts, ∀ v ∈ (rungDel X a b xm xp ym yp μ).verts, u ≠ v →
        (rungDel X a b xm xp ym yp μ).mult s(u, v) ≤ 2 := by
  obtain ⟨hB, hm2, -⟩ := hT
  have hR' := hB.isRungAt_of_rungCore hR
  obtain ⟨hpV, hqV, hpq, hdp, hdq, hd, -⟩ := hB
  have hVR : ∀ v, v ∈ (rungDel X a b xm xp ym yp μ).verts ↔ v ∈ X.verts ∧ v ≠ a ∧ v ≠ b := by
    intro v; rw [hR.verts_rungDel]; simp only [Finset.mem_erase]; tauto
  refine ⟨⟨(hVR p).mpr ⟨hpV, Ne.symm hap, Ne.symm hbp⟩, (hVR q).mpr ⟨hqV, Ne.symm haq, Ne.symm hbq⟩, hpq,
    by rw [hR.deg_rungDel μ (Ne.symm hap) (Ne.symm hbp)]; exact hdp,
    by rw [hR.deg_rungDel μ (Ne.symm haq) (Ne.symm hbq)]; exact hdq, ?_, hR'.connected_rungDel μ⟩, ?_⟩
  · intro v hv hv1 hv2
    obtain ⟨hvV, hva, hvb⟩ := (hVR v).mp hv
    rw [hR.deg_rungDel μ hva hvb]; exact hd v hvV hv1 hv2
  · intro u hu v hv huv
    obtain ⟨huV, hua, hub⟩ := (hVR u).mp hu
    obtain ⟨hvV, hva, hvb⟩ := (hVR v).mp hv
    rcases hR.mem_poles huV hua hub with hu' | hu' <;> rcases hR.mem_poles hvV hva hvb with hv' | hv'
    · rw [hR.rungDel_mult_same μ (Or.inl ⟨hu', hv'⟩)]; exact hm2 u huV v hvV huv
    · exact hR.rungDel_mult_le μ hu' hv'
    · rw [Sym2.eq_swap]; exact hR.rungDel_mult_le μ hv' hu'
    · rw [hR.rungDel_mult_same μ (Or.inr ⟨hu', hv'⟩)]; exact hm2 u huV v hvV huv

/-! ## Indicators -/

theorem sym2_ne_of {u x y z : V} (hy : u ≠ y) (hz : u ≠ z) : s(u, x) ≠ s(y, z) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
  exacts [hy h1, hz h1]

theorem not_mem_sym2 {v x y : V} (hx : v ≠ x) (hy : v ≠ y) : v ∉ s(x, y) := by
  rw [Sym2.mem_iff]; rintro (h | h); exacts [hx h, hy h]

theorem forall_mem_pair {α : Type*} {P : α → Prop} {x y : α} (hx : P x) (hy : P y) :
    ∀ z ∈ ({x, y} : Multiset α), P z := by
  intro z hz
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
  rcases hz with rfl | rfl
  exacts [hx, hy]

theorem forall_mem_single {α : Type*} {P : α → Prop} {x : α} (hx : P x) : ∀ z ∈ ({x} : Multiset α), P z := by
  intro z hz
  rw [Multiset.mem_singleton] at hz
  rw [hz]; exact hx

theorem ind_left (a b x : V) : (if s(a, x) = s(a, b) then 1 else 0) = if x = b then 1 else 0 :=
  if_congr Sym2.congr_right rfl rfl

theorem ind_right (a b x : V) : (if s(b, x) = s(a, b) then 1 else 0) = if x = a then 1 else 0 := by
  rw [Sym2.eq_swap (a := a) (b := b)]; exact if_congr Sym2.congr_right rfl rfl

theorem pair_ne_of_count {x y z : V} (h : ({x, y} : Multiset V).count z = 0) : x ≠ z ∧ y ≠ z := by
  rw [count_pair_v] at h
  refine ⟨fun h' => ?_, fun h' => ?_⟩
  · rw [if_pos h'.symm] at h; omega
  · rw [if_pos h'.symm] at h; omega

theorem eq_of_pair_eq_pair {u x y : V} (h : ({u, x} : Multiset V) = {y, u}) : x = y := by
  rw [Multiset.pair_comm y u, Multiset.insert_eq_cons, Multiset.insert_eq_cons, Multiset.cons_inj_right,
    Multiset.singleton_inj] at h
  exact h

/-! ## Neighbours -/

theorem mult_eq_zero_of_not_mem_verts {G : UMultigraph V} {v : V} (hv : v ∉ G.verts) {e : Sym2 V} (he : v ∈ e) :
    G.mult e = 0 := by
  by_contra h; exact hv (G.supp e h v he)

/-- A degree-`2` atom adjacent to two distinct atoms has exactly these neighbours. -/
theorem nbrs_eq_of_two {G : UMultigraph V} {v x y : V} (hd : deg G v = 2) (hx : x ∈ nbrs G v)
    (hy : y ∈ nbrs G v) (hxy : x ≠ y) : nbrs G v = {x, y} := by
  obtain ⟨u, w, huw⟩ := Multiset.card_eq_two.mp (show Multiset.card (nbrs G v) = 2 by rw [card_nbrs]; exact hd)
  rw [huw] at hx hy ⊢
  obtain ⟨t, ht⟩ := pair_eq_of_mem hx
  rw [ht] at hy ⊢
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hy
  rcases hy with h | h
  · exact absurd h.symm hxy
  · rw [h]

/-- The neighbours of an atom `v ∉ {a, b}` after a splice at `{a, b}`. -/
theorem nbrs_splice_of {X : UMultigraph V} {a b v : V} {A : Multiset (Sym2 V)} {N M : Multiset V}
    (hva : v ≠ a) (hvb : v ≠ b) (hN : nbrs X v = N) (hl : X.mult s(v, v) = 0) (hAl : A.count s(v, v) = 0)
    (hV : (splice X a b A).verts = (X.verts.erase a).erase b)
    (hM : ∀ x ∈ M, x ∈ X.verts ∧ x ≠ a ∧ x ≠ b ∧ x ≠ v)
    (hcount : ∀ x, x ≠ v → x ≠ a → x ≠ b → N.count x + A.count s(v, x) = M.count x) :
    nbrs (splice X a b A) v = M := by
  apply nbrs_eq_of_mult M
  · rw [splice_mult_at _ _ hva hvb, if_neg (by tauto), hl, hAl]
  · intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := hM x hx
    rw [hV]
    exact ⟨Finset.mem_erase.mpr ⟨h3, Finset.mem_erase.mpr ⟨h2, h1⟩⟩, h4⟩
  · intro x hxv
    rw [splice_mult_at _ _ hva hvb]
    split_ifs with hx
    · symm; apply Multiset.count_eq_zero.mpr; intro hxM
      obtain ⟨-, h2, h3, -⟩ := hM x hxM
      rcases hx with h | h
      exacts [h2 h, h3 h]
    · rw [mult_of_nbrs_eq hN hxv]
      exact hcount x hxv (fun h => hx (Or.inl h)) (fun h => hx (Or.inr h))

/-! ## Stuck pairs and (Y2) pairs of a closure -/

theorem not_reducesToT_of_stuck {C : UMultigraph V} {a b d : V} {n : ℕ} (h : Stuck C a b n d) : ¬ ReducesToT C := by
  intro hRT
  obtain ⟨ps, T', hp, hT⟩ := reducesToT_iff.mp hRT
  exact h.not_y2Path hp hT

/-- A triple pair with one further bond at each atom is a (Y2) pair, if the graph reduces to `T`. -/
theorem y2Pair_of_reducesToT {C : UMultigraph V} {a b c d : V} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hda : d ≠ a) (hdb : d ≠ b) (ha : ∀ x, C.mult s(a, x) = if x = b then 3 else if x = c then 1 else 0)
    (hb : ∀ x, C.mult s(b, x) = if x = a then 3 else if x = d then 1 else 0) (hRT : ReducesToT C) :
    IsY2Pair C a b c d := by
  by_cases hcd : c = d
  · subst hcd
    exact absurd hRT (not_reducesToT_of_stuck (n := 3) ⟨hab, hca, hcb, le_refl _, by norm_num, ha, hb⟩)
  · exact IsY2Pair.of_mult hab hcd hca hcb hda hdb ha hb

/-- The bonds at a rung atom in a closure. -/
theorem closure_mult_a {C X : UMultigraph V} {p q a b xm xp : V} {added : Multiset (Sym2 V)} (hpa : p ≠ a)
    (hqa : q ≠ a) (hCm : ∀ e, C.mult e = (if p ∈ e ∨ q ∈ e then 0 else X.mult e) + added.count e)
    (hXa : ∀ x, X.mult s(a, x) = if x = b then 2 else if x = xm ∨ x = xp then 1 else 0) (x : V) :
    C.mult s(a, x) = (if x = p ∨ x = q then 0 else if x = b then 2 else if x = xm ∨ x = xp then 1 else 0) +
      added.count s(a, x) := by
  have hiff : (p ∈ s(a, x) ∨ q ∈ s(a, x)) ↔ (x = p ∨ x = q) := by
    rw [Sym2.mem_iff, Sym2.mem_iff]
    constructor
    · rintro ((h | h) | (h | h))
      exacts [absurd h hpa, Or.inl h.symm, absurd h hqa, Or.inr h.symm]
    · rintro (h | h)
      exacts [Or.inl (Or.inr h.symm), Or.inr (Or.inr h.symm)]
  rw [hCm, hXa]
  congr 1
  exact if_congr hiff rfl rfl

theorem rail_closed {x p q b m c : V} (hm : m = p ∨ m = q) (hbp : b ≠ p) (hbq : b ≠ q) (hcp : c ≠ p)
    (hcq : c ≠ q) :
    (if x = p ∨ x = q then 0 else if x = b then 2 else if x = m ∨ x = c then 1 else 0) + (if x = b then 1 else 0) =
      if x = b then 3 else if x = c then 1 else 0 := by
  split_ifs <;> simp_all

theorem rail_closed2 {x p q b w : V} (hbp : b ≠ p) (hbq : b ≠ q) (hwp : w ≠ p) (hwq : w ≠ q) (hwb : w ≠ b) :
    (if x = p ∨ x = q then 0 else if x = b then 2 else if x = p ∨ x = q then 1 else 0) +
      ((if x = b then 1 else 0) + (if x = w then 1 else 0)) = if x = b then 3 else if x = w then 1 else 0 := by
  split_ifs <;> simp_all

theorem rail_closed4 {x p q b : V} (hbp : b ≠ p) (hbq : b ≠ q) :
    (if x = p ∨ x = q then 0 else if x = b then 2 else if x = p ∨ x = q then 1 else 0) +
      ((if x = b then 1 else 0) + (if x = b then 1 else 0)) = if x = b then 4 else if x = p then 4 - 4 else 0 := by
  split_ifs <;> simp_all

/-! ## Assembling the closure after a cap deletion -/

/-- **Assembly**: the (Y2) move of the old closure at the rung pair is a closure of the deleted graph, given the
joint data of the deleted graph and the bookkeeping of the added bonds. -/
theorem isClosureU_y2Move {X Z C : UMultigraph V} {p q a b c d : V} {A added added' : Multiset (Sym2 V)}
    (hZV : Z.verts = (X.verts.erase a).erase b)
    (hZm : ∀ e, Z.mult e = if a ∈ e ∨ b ∈ e then 0 else X.mult e + A.count e)
    (hCV : C.verts = (X.verts.erase p).erase q) (hCl : C.Loopless)
    (hCm : ∀ e, C.mult e = (if p ∈ e ∨ q ∈ e then 0 else X.mult e) + added.count e)
    (hQ : IsY2Pair C a b c d) (hA : ∀ f ∈ A, p ∈ f ∨ q ∈ f)
    (hadd : ∀ f ∈ added', p ∉ f ∧ q ∉ f ∧ a ∉ f ∧ b ∉ f)
    (hsum : ∀ e, p ∉ e → q ∉ e → a ∉ e → b ∉ e →
      added.count e + (if e = s(c, d) then 1 else 0) = added'.count e)
    (hσ : Z.mult s(p, q) < 2)
    (hdata : (Z.mult s(p, q) = 0 ∧ ∃ a b c d : V, nbrs Z p = {a, b} ∧ nbrs Z q = {c, d} ∧
          added' = {s(a, b), s(c, d)}) ∨
       (Z.mult s(p, q) = 1 ∧ ∃ x y : V, nbrs Z p = {q, x} ∧ nbrs Z q = {p, y} ∧ added' = {s(x, y)})) :
    IsClosureU Z p q (y2Move C a b c d) := by
  have hpC : p ∉ C.verts := by rw [hCV]; simp
  have hqC : q ∉ C.verts := by rw [hCV]; simp
  refine ⟨hσ, ?_, loopless_y2Move hQ hCl, added', hdata, fun e => ?_⟩
  · rw [y2Move_verts hQ, hCV, hZV]
    ext x; simp only [Finset.mem_erase]; tauto
  · have hcnt : ∀ v, (v = p ∨ v = q ∨ v = a ∨ v = b) → v ∈ e → added'.count e = 0 := by
      intro v hv hve
      apply Multiset.count_eq_zero.mpr
      intro hf
      obtain ⟨h1, h2, h3, h4⟩ := hadd e hf
      rcases hv with rfl | rfl | rfl | rfl
      exacts [h1 hve, h2 hve, h3 hve, h4 hve]
    rw [y2Move_mult]
    by_cases hpq : p ∈ e ∨ q ∈ e
    · have h0 : added'.count e = 0 := by
        rcases hpq with h | h
        exacts [hcnt p (Or.inl rfl) h, hcnt q (Or.inr (Or.inl rfl)) h]
      rw [if_pos hpq, zero_add, h0]
      by_cases hab : a ∈ e ∨ b ∈ e
      · rw [if_pos hab]
      · have hC0 : C.mult e = 0 := by
          rcases hpq with h | h
          exacts [mult_eq_zero_of_not_mem_verts hpC h, mult_eq_zero_of_not_mem_verts hqC h]
        have hcd : e ≠ s(c, d) := by
          intro he
          rw [he] at hpq
          rcases hpq with h | h <;> rcases Sym2.mem_iff.mp h with h' | h'
          · exact hpC (by rw [h']; exact hQ.c_mem)
          · exact hpC (by rw [h']; exact hQ.d_mem)
          · exact hqC (by rw [h']; exact hQ.c_mem)
          · exact hqC (by rw [h']; exact hQ.d_mem)
        rw [if_neg hab, hC0, if_neg hcd]
    · rw [if_neg hpq, hZm, hCm, if_neg hpq]
      have hA0 : A.count e = 0 := Multiset.count_eq_zero.mpr fun hf => hpq (hA e hf)
      by_cases hab : a ∈ e ∨ b ∈ e
      · rw [if_pos hab, if_pos hab, zero_add]
        rcases hab with h | h
        exacts [(hcnt a (Or.inr (Or.inr (Or.inl rfl))) h).symm, (hcnt b (Or.inr (Or.inr (Or.inr rfl))) h).symm]
      · rw [if_neg hab, if_neg hab, hA0, add_zero, add_assoc,
          hsum e (fun h => hpq (Or.inl h)) (fun h => hpq (Or.inr h)) (fun h => hab (Or.inl h))
            (fun h => hab (Or.inr h))]

/-- In the single-joint case, both matchings add the same two bonds at the joint. -/
theorem rungAdds_capA (p xp yp : V) (μ : Bool) : rungAdds p xp p yp μ = {s(p, xp), s(p, yp)} := by
  cases μ
  · rfl
  · show ({s(p, yp), s(xp, p)} : Multiset (Sym2 V)) = _
    rw [Multiset.pair_comm, Sym2.eq_swap (a := xp) (b := p)]

end WaveTurbulence.TVine.Core
