/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.IIData
import Mathlib.Tactic

/-!
# The expanded template of vine (II) (packet L3)

`T_II([k])` has the atoms `0 = J₁`, `1 = J₂`, the rungs `(ua i, va i)` for `i ≤ k` (`ua 0 = 2`, `va 0 = 3`,
`ua i = 3 + i`, `va i = 3 + k + i`), the rails `J₁ – ua 0 – ua 1 – ⋯ – ua k – J₂` and the same with `va`.

* `expandII_bonds`, `expandII_n`: the bond list and size, for every `k` (also `k = 0`);
* `tmplII`: every inner template atom has a partner (double bond), a neighbour one level down and one level up.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open TVine

/-- The `u`-rail atoms. -/
def ua (k i : ℕ) : ℕ := if i = 0 then 2 else if i ≤ k then 3 + i else 1

/-- The `v`-rail atoms. -/
def va (k i : ℕ) : ℕ := if i = 0 then 3 else if i ≤ k then 3 + k + i else 1

/-- The template level. -/
def tl (k a : ℕ) : ℕ := if a = 0 then 0 else if a = 1 then k + 2 else if a ≤ 3 then 1 else
  if a < 4 + k then a - 2 else a - k - 2

/-- The bond list of `T_II([k])`. -/
def bondsII (k : ℕ) : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (2, 3), (2, 3)] ++ railBonds 2 ((List.range k).map (4 + ·)) 1 ++
    railBonds 3 ((List.range k).map (4 + k + ·)) 1 ++
    (List.zip ((List.range k).map (4 + ·)) ((List.range k).map (4 + k + ·))).flatMap (fun p => [p, p])

theorem expandII_eq (k : ℕ) : (VineType.II.expand [k]).bonds = bondsII k ∧ (VineType.II.expand [k]).n = 4 + 2 * k := by
  simp only [VineType.expand, VineType.template, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons,
    List.foldl_nil, insertRungs]
  split_ifs with h
  · subst h; exact ⟨rfl, rfl⟩
  · refine ⟨?_, by first | (simp only; done) | (simp only; ring) | omega⟩
    simp only [bondsII]
    rfl

theorem mem_railBonds_of (z z' : ℕ) (ws : List ℕ) (i : ℕ) (hi : i ≤ ws.length) :
    ((z :: ws)[i]'(by simp; omega), (ws ++ [z'])[i]'(by simp; omega)) ∈ railBonds z ws z' := by
  unfold railBonds
  have := List.getElem_mem (l := List.zip (z :: ws) (ws ++ [z'])) (n := i) (by simp; omega)
  rwa [List.getElem_zip] at this

theorem ua_rail (k i : ℕ) (hi : i ≤ k) : (ua k i, ua k (i + 1)) ∈ railBonds 2 ((List.range k).map (4 + ·)) 1 := by
  have := mem_railBonds_of 2 1 ((List.range k).map (4 + ·)) i (by simp; omega)
  convert this using 2
  · rcases i with _ | i
    · simp [ua]
    · simp [ua, show i + 1 ≤ k from hi]; omega
  · by_cases h : i < k
    · rw [List.getElem_append_left (by simpa using h)]
      simp [ua, show i + 1 ≤ k from h]; omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp [ua, show ¬ (i + 1 ≤ k) by omega]

theorem va_rail (k i : ℕ) (hi : i ≤ k) :
    (va k i, va k (i + 1)) ∈ railBonds 3 ((List.range k).map (4 + k + ·)) 1 := by
  have := mem_railBonds_of 3 1 ((List.range k).map (4 + k + ·)) i (by simp; omega)
  convert this using 2
  · rcases i with _ | i
    · simp [va]
    · simp [va, show i + 1 ≤ k from hi]; omega
  · by_cases h : i < k
    · rw [List.getElem_append_left (by simpa using h)]
      simp [va, show i + 1 ≤ k from h]; omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp [va, show ¬ (i + 1 ≤ k) by omega]

theorem rung_sublist (k i : ℕ) (hi : i ≤ k) : List.Sublist [(ua k i, va k i), (ua k i, va k i)] (bondsII k) := by
  unfold bondsII
  rcases i with _ | i
  · simp only [ua, va, if_true]
    have h0 : List.Sublist [((2 : ℕ), (3 : ℕ)), (2, 3)] [(0, 2), (0, 3), (2, 3), (2, 3)] :=
      List.Sublist.cons _ (List.Sublist.cons _ (List.Sublist.refl _))
    exact h0.trans (((List.sublist_append_left _ _).trans (List.sublist_append_left _ _)).trans
      (List.sublist_append_left _ _))
  · have hp : (ua k (i + 1), va k (i + 1)) ∈
        List.zip ((List.range k).map (4 + ·)) ((List.range k).map (4 + k + ·)) := by
      rw [List.mem_iff_getElem]
      refine ⟨i, by simp; omega, ?_⟩
      simp [ua, va, show i + 1 ≤ k from hi]
      omega
    refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
    rw [List.flatMap_def]
    exact List.sublist_flatten_of_mem (List.mem_map_of_mem hp)

end WaveTurbulence.TVine.Struct

namespace WaveTurbulence.TVine.Struct

open TVine Core

/-- The multiplicity of `s(a, b)` in `T_II([k])`. -/
def cntII (k a b : ℕ) : ℕ := ((bondsII k).map fun p => s(p.1, p.2)).count s(a, b)

theorem tl_ua (k i : ℕ) (hi : i ≤ k + 1) : tl k (ua k i) = i + 1 := by
  unfold ua tl; split_ifs <;> omega

theorem tl_va (k i : ℕ) (hi : i ≤ k + 1) : tl k (va k i) = i + 1 := by
  unfold va tl; split_ifs <;> omega

theorem ua_lt (k i : ℕ) (hi : i ≤ k + 1) : ua k i < 4 + 2 * k := by unfold ua; split_ifs <;> omega

theorem va_lt (k i : ℕ) (hi : i ≤ k + 1) : va k i < 4 + 2 * k := by unfold va; split_ifs <;> omega

theorem ua_ne_va (k i : ℕ) (hi : i ≤ k) : ua k i ≠ va k i := by unfold ua va; split_ifs <;> omega

theorem tl_zero (k : ℕ) : tl k 0 = 0 := by simp [tl]

theorem tl_one (k : ℕ) : tl k 1 = k + 2 := by simp [tl]

theorem decompII (k a : ℕ) (h2 : 2 ≤ a) (hn : a < 4 + 2 * k) : ∃ i ≤ k, a = ua k i ∨ a = va k i := by
  by_cases ha2 : a = 2
  · exact ⟨0, Nat.zero_le _, Or.inl (by simp [ua, ha2])⟩
  by_cases ha3 : a = 3
  · exact ⟨0, Nat.zero_le _, Or.inr (by simp [va, ha3])⟩
  by_cases hak : a < 4 + k
  · exact ⟨a - 3, by omega, Or.inl (by unfold ua; split_ifs <;> omega)⟩
  · exact ⟨a - 3 - k, by omega, Or.inr (by unfold va; split_ifs <;> omega)⟩

theorem cnt_pos {k a b : ℕ} (h : (a, b) ∈ bondsII k ∨ (b, a) ∈ bondsII k) : 1 ≤ cntII k a b := by
  unfold cntII
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, List.count_pos_iff, List.mem_map]
  rcases h with h | h
  · exact ⟨_, h, rfl⟩
  · exact ⟨_, h, Sym2.eq_swap⟩

theorem cnt_rung (k i : ℕ) (hi : i ≤ k) : 2 ≤ cntII k (ua k i) (va k i) ∧ 2 ≤ cntII k (va k i) (ua k i) := by
  have h := ((rung_sublist k i hi).map fun p : ℕ × ℕ => s(p.1, p.2)).count_le s(ua k i, va k i)
  simp only [List.map_cons, List.map_nil, List.count_cons_self, List.count_nil] at h
  refine ⟨h, ?_⟩
  unfold cntII; rw [Sym2.eq_swap]; exact h

theorem mem_bondsII_of_rail_u {k i : ℕ} (hi : i ≤ k) : (ua k i, ua k (i + 1)) ∈ bondsII k := by
  unfold bondsII
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr (ua_rail k i hi)))

theorem mem_bondsII_of_rail_v {k i : ℕ} (hi : i ≤ k) : (va k i, va k (i + 1)) ∈ bondsII k := by
  unfold bondsII
  simp only [List.mem_append]
  exact Or.inl (Or.inr (va_rail k i hi))

theorem mem_bondsII_02 (k : ℕ) : ((0 : ℕ), (2 : ℕ)) ∈ bondsII k := by
  unfold bondsII; simp

theorem mem_bondsII_03 (k : ℕ) : ((0 : ℕ), (3 : ℕ)) ∈ bondsII k := by
  unfold bondsII; simp

/-- **Local structure of `T_II([k])`.** -/
theorem tmplII (k a : ℕ) (h2 : 2 ≤ a) (hn : a < 4 + 2 * k) :
    (1 ≤ tl k a ∧ tl k a < k + 2) ∧ ∃ p d w : ℕ,
      (p < 4 + 2 * k ∧ p ≠ a ∧ tl k p = tl k a ∧ 2 ≤ cntII k a p) ∧
      (d < 4 + 2 * k ∧ tl k d + 1 = tl k a ∧ 1 ≤ cntII k a d) ∧
      (w < 4 + 2 * k ∧ tl k w = tl k a + 1 ∧ 1 ≤ cntII k a w) := by
  obtain ⟨i, hi, rfl | rfl⟩ := decompII k a h2 hn
  · rw [tl_ua k i (by omega)]
    refine ⟨⟨by omega, by omega⟩, va k i, if i = 0 then 0 else ua k (i - 1), ua k (i + 1),
      ⟨va_lt k i (by omega), (ua_ne_va k i hi).symm, by rw [tl_va k i (by omega)], (cnt_rung k i hi).1⟩, ?_,
      ⟨ua_lt k (i + 1) (by omega), by rw [tl_ua k (i + 1) (by omega)], cnt_pos (Or.inl (mem_bondsII_of_rail_u hi))⟩⟩
    split_ifs with h0
    · subst h0
      exact ⟨by omega, by rw [tl_zero], cnt_pos (Or.inr (by simpa [ua] using mem_bondsII_02 k))⟩
    · have := mem_bondsII_of_rail_u (k := k) (i := i - 1) (by omega)
      rw [show i - 1 + 1 = i by omega] at this
      exact ⟨ua_lt k (i - 1) (by omega), by rw [tl_ua k (i - 1) (by omega)]; omega, cnt_pos (Or.inr this)⟩
  · rw [tl_va k i (by omega)]
    refine ⟨⟨by omega, by omega⟩, ua k i, if i = 0 then 0 else va k (i - 1), va k (i + 1),
      ⟨ua_lt k i (by omega), ua_ne_va k i hi, by rw [tl_ua k i (by omega)], (cnt_rung k i hi).2⟩, ?_,
      ⟨va_lt k (i + 1) (by omega), by rw [tl_va k (i + 1) (by omega)], cnt_pos (Or.inl (mem_bondsII_of_rail_v hi))⟩⟩
    split_ifs with h0
    · subst h0
      exact ⟨by omega, by rw [tl_zero], cnt_pos (Or.inr (by simpa [va] using mem_bondsII_03 k))⟩
    · have := mem_bondsII_of_rail_v (k := k) (i := i - 1) (by omega)
      rw [show i - 1 + 1 = i by omega] at this
      exact ⟨va_lt k (i - 1) (by omega), by rw [tl_va k (i - 1) (by omega)]; omega, cnt_pos (Or.inr this)⟩

/-! ## Transport to a multigraph isomorphic to the template -/

universe u

variable {V : Type u} [DecidableEq V]

theorem mem_verts_sym2_of_mem_bondMultiset {G : UMultigraph V} {e : Sym2 V} (he : e ∈ bondMultiset G) :
    e ∈ G.verts.sym2 := by
  unfold bondMultiset at he
  obtain ⟨e', he', hm⟩ := Multiset.mem_sum.mp he
  rw [(Multiset.mem_replicate.mp hm).2]; exact he'

/-- **Multiplicities are read off the image multiset.** -/
theorem mult_eq_count_map {G : UMultigraph V} {f : V → ℕ} (hinj : Set.InjOn f G.verts) {p q : V}
    (hp : p ∈ G.verts) (hq : q ∈ G.verts) :
    G.mult s(p, q) = ((bondMultiset G).map (Sym2.map f)).count s(f p, f q) := by
  rw [Multiset.count_map, ← count_bondMultiset, Multiset.count_eq_card_filter_eq]
  congr 1
  apply Multiset.filter_congr
  intro e he
  have hs := Finset.mem_sym2_iff.mp (mem_verts_sym2_of_mem_bondMultiset he)
  induction e using Sym2.ind with
  | _ x y =>
  have hx := hs x (Sym2.mem_mk_left x y)
  have hy := hs y (Sym2.mem_mk_right x y)
  change s(p, q) = s(x, y) ↔ s(f p, f q) = s(f x, f y)
  rw [Sym2.eq_iff, Sym2.eq_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1 ▸ rfl, h2 ▸ rfl⟩
    · exact Or.inr ⟨h1 ▸ rfl, h2 ▸ rfl⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨hinj hp hx h1, hinj hq hy h2⟩
    · exact Or.inr ⟨hinj hp hy h1, hinj hq hx h2⟩

/-- **Level data from a template isomorphism** (bottom joint `↦ 0`, top joint `↦ 1`). -/
theorem nonempty_iiData_of_tmpl {G : UMultigraph V} {jb jt : V} (k : ℕ) (f : V → ℕ)
    (hinj : Set.InjOn f G.verts) (himg : G.verts.image f = Finset.range (4 + 2 * k))
    (hjb : jb ∈ G.verts) (hjt : jt ∈ G.verts) (hfb : f jb = 0) (hft : f jt = 1)
    (hmult : ∀ p ∈ G.verts, ∀ q ∈ G.verts, G.mult s(p, q) = cntII k (f p) (f q)) :
    Nonempty (IIData G jb jt) := by
  have : Nonempty V := ⟨jb⟩
  have hlt : ∀ x ∈ G.verts, f x < 4 + 2 * k := fun x hx => by
    have : f x ∈ G.verts.image f := Finset.mem_image_of_mem f hx
    rw [himg, Finset.mem_range] at this; exact this
  have hpre : ∀ a, a < 4 + 2 * k → Function.invFunOn f G.verts a ∈ G.verts ∧
      f (Function.invFunOn f G.verts a) = a := by
    intro a ha
    have : a ∈ G.verts.image f := by rw [himg, Finset.mem_range]; exact ha
    obtain ⟨p, hp, hpa⟩ := Finset.mem_image.mp this
    exact ⟨Function.invFunOn_mem ⟨p, hp, hpa⟩, Function.invFunOn_eq ⟨p, hp, hpa⟩⟩
  set g := Function.invFunOn f G.verts
  choose! P Dn Up hPDU using fun a (h2 : 2 ≤ a) (hn : a < 4 + 2 * k) => (tmplII k a h2 hn).2
  have h2 : ∀ x ∈ G.verts, x ≠ jb → x ≠ jt → 2 ≤ f x := by
    intro x hx h1 h2
    have h0 : f x ≠ 0 := fun h => h1 (hinj hx hjb (h.trans hfb.symm))
    have h1' : f x ≠ 1 := fun h => h2 (hinj hx hjt (h.trans hft.symm))
    omega
  have hu1 : ua k (k + 1) = 1 := by simp [ua]
  obtain ⟨z2m, z2e⟩ := hpre 2 (by omega)
  obtain ⟨zkm, zke⟩ := hpre (ua k k) (ua_lt k k (by omega))
  refine ⟨⟨fun x => tl k (f x), k + 2, fun x => g (P (f x)), fun x => g (Dn (f x)), fun x => g (Up (f x)),
    hjb, hjt, by simp [hfb, tl_zero], by simp [hft, tl_one], by omega,
    ⟨g 2, z2m, by simp only [z2e]; simp [tl], by
      rw [hmult jb hjb _ z2m, hfb, z2e]; exact cnt_pos (Or.inl (mem_bondsII_02 k))⟩,
    ⟨g (ua k k), zkm, by simp only [zke]; rw [tl_ua k k (by omega)]; omega, by
      rw [hmult jt hjt _ zkm, hft, zke]
      have := mem_bondsII_of_rail_u (k := k) (i := k) le_rfl
      rw [hu1] at this
      exact cnt_pos (Or.inr this)⟩, ?_⟩⟩
  intro x hx hb ht
  have ha2 := h2 x hx hb ht
  have han := hlt x hx
  obtain ⟨hl, -⟩ := tmplII k (f x) ha2 han
  obtain ⟨⟨p1, p2, p3, p4⟩, ⟨d1, d2, d3⟩, ⟨u1, u2, u3⟩⟩ := hPDU (f x) ha2 han
  obtain ⟨gp1, gp2⟩ := hpre _ p1
  obtain ⟨gd1, gd2⟩ := hpre _ d1
  obtain ⟨gu1, gu2⟩ := hpre _ u1
  refine ⟨hl, ⟨gp1, fun h => p2 (by rw [← gp2, h]), by simp only [gp2, p3], ?_⟩,
    ⟨gd1, by simp only [gd2, d2], ?_⟩, ⟨gu1, by simp only [gu2, u2], ?_⟩⟩
  · rw [hmult x hx _ gp1, gp2]; exact p4
  · rw [hmult x hx _ gd1, gd2]; exact d3
  · rw [hmult x hx _ gu1, gu2]; exact u3

/-- **Level data of a vine (II)** (with its joints in either order). -/
theorem nonempty_iiData {G : UMultigraph V} {j₁ j₂ : V} (h : IsVineXU .II G j₁ j₂) :
    Nonempty (IIData G j₁ j₂) := by
  obtain ⟨hB, k', hk, f, hinj, himg, hj, hbonds⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k, k' = [k] := by
    have : k'.length = 1 := by simpa [VineType.template] using hk
    match k', this with
    | [k₀], _ => exact ⟨k₀, rfl⟩
  obtain ⟨hbl, hn⟩ := expandII_eq k
  rw [hn] at himg
  rw [hbl] at hbonds
  have hmult : ∀ p ∈ G.verts, ∀ q ∈ G.verts, G.mult s(p, q) = cntII k (f p) (f q) := by
    intro p hp q hq
    rw [mult_eq_count_map hinj hp hq, hbonds, Multiset.coe_count]; rfl
  have hj₁ := hB.1
  have hj₂ := hB.2.1
  have hne := hB.2.2.1
  have hfne : f j₁ ≠ f j₂ := fun h => hne (hinj hj₁ hj₂ h)
  have h01 : (f j₁ = 0 ∧ f j₂ = 1) ∨ (f j₁ = 1 ∧ f j₂ = 0) := by
    have h1 : f j₁ ∈ ({0, 1} : Finset ℕ) := by rw [← hj]; simp
    have h2 : f j₂ ∈ ({0, 1} : Finset ℕ) := by rw [← hj]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    omega
  rcases h01 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact nonempty_iiData_of_tmpl k f hinj himg hj₁ hj₂ h1 h2 hmult
  · obtain ⟨D⟩ := nonempty_iiData_of_tmpl k f hinj himg hj₂ hj₁ h2 h1 hmult
    exact ⟨D.rev (Ne.symm hne)⟩

end WaveTurbulence.TVine.Struct
