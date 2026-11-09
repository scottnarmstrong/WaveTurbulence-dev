/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.SizeBound

/-!
# N2 Lemma 1.8: the count on the generated family, and `sizeBound`
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine Core

universe u

/-! ## The joints as gadgets -/

theorem removable2_of_valid {es : Edges} {x₁ y₁ x₂ y₂ : ℕ} (h1 : mult es x₁ y₁ ≠ 0)
    (h2 : mult (eraseOne es x₁ y₁) x₂ y₂ ≠ 0) : Removable2 es x₁ y₁ x₂ y₂ := by
  have := mult_eraseOne' h1 x₂ y₂
  exact ⟨by omega, by omega⟩

theorem mult_gadget_raw {es : Edges} {x y w₁ w₂ : ℕ} {inner : Edges} (hxy : mult es x y ≠ 0) (u v : ℕ) :
    mult (gadget es x y w₁ w₂ inner) u v + ind u v x y =
      mult es u v + ind u v x w₁ + mult inner u v + ind u v w₂ y := by
  have := mult_eraseOne' hxy u v
  simp only [gadget, gadgetList, mult_append, mult_list_cons, mult_nil]
  omega

theorem placeTwo_sameMult {es : Edges} {X₁ Y₁ J₁ X₂ Y₂ J₂ : ℕ} (h : Removable2 es X₁ Y₁ X₂ Y₂) :
    SameMult (placeTwo es X₁ Y₁ J₁ X₂ Y₂ J₂) (gadget (gadget es X₁ Y₁ J₁ J₁ []) X₂ Y₂ J₂ J₂ []) := by
  have h1 : mult es X₁ Y₁ ≠ 0 := by have := h.1; omega
  have h2 : mult (gadget es X₁ Y₁ J₁ J₁ []) X₂ Y₂ ≠ 0 := by
    have := mult_gadget_raw (w₁ := J₁) (w₂ := J₁) (inner := []) h1 X₂ Y₂
    have := h.2
    unfold ind at *
    split_ifs at * <;> simp_all <;> omega
  intro u v
  have a := mult_placeTwo (J₁ := J₁) (J₂ := J₂) h u v
  have b := mult_gadget_raw (w₁ := J₂) (w₂ := J₂) (inner := []) h2 u v
  have c := mult_gadget_raw (w₁ := J₁) (w₂ := J₁) (inner := []) h1 u v
  simp only [mult_nil] at b c
  omega

theorem genC_fresh {p : CParam} (hp : p.Valid) :
    ¬ InEnds (genC p) p.jname ∧ ¬ InEnds (genC p) (p.jname + 1) :=
  ⟨fun h => absurd (genC_lt_jname hp h) (lt_irrefl _), fun h => absurd (genC_lt_jname hp h) (by omega)⟩

/-- A 2-cut rung of the closure persists in the block (two joints) when no joint sits on its double bond. -/
theorem rungL_placeTwo {p : CParam} (hp : p.Valid) {x₁ y₁ x₂ y₂ : ℕ} (hj : (JParam.two x₁ y₁ x₂ y₂).Valid p)
    {a b xm xp ym yp : ℕ} {Km Kp : Finset ℕ} (hR : RungL (genC p) a b xm xp ym yp Km Kp)
    (h₁ : s(x₁, y₁) ≠ s(a, b)) (h₂ : s(x₂, y₂) ≠ s(a, b)) :
    ∃ xm' xp' ym' yp' Km' Kp', RungL (genB p (.two x₁ y₁ x₂ y₂)) a b xm' xp' ym' yp' Km' Kp' ∧
      Km ⊆ Km' ∧ Kp ⊆ Kp' := by
  obtain ⟨hJ, hJ1⟩ := genC_fresh hp
  obtain ⟨⟨lt₁, lt₂, -, m₁, m₂⟩, -⟩ := hj
  have hRem := removable2_of_valid m₁ m₂
  have hG₁ := gadgetOK_joint (es := genC p) m₁ (by omega) hJ
  obtain ⟨_, _, _, _, Km₁, Kp₁, hR₁, s₁, t₁⟩ := rungL_gadget hR hG₁ h₁
  have hm2 : mult (gadget (genC p) x₁ y₁ p.jname p.jname []) x₂ y₂ ≠ 0 := by
    have := mult_gadget_raw (w₁ := p.jname) (w₂ := p.jname) (inner := []) m₁ x₂ y₂
    have e2 := (inEnds_of_mult_ne_zero (show mult (genC p) x₂ y₂ ≠ 0 by have := hRem.2; omega))
    have hx2 : x₂ ≠ p.jname := fun hh => hJ (hh ▸ e2.1)
    have hy2 : y₂ ≠ p.jname := fun hh => hJ (hh ▸ e2.2)
    rw [ind_eq_zero (u := x₂) (v := y₂) (x := x₁) (y := p.jname) (by omega),
      ind_eq_zero (u := x₂) (v := y₂) (x := p.jname) (y := y₁) (by omega)] at this
    have := hRem.2; simp only [mult_nil] at *; omega
  have hJ1' : ¬ InEnds (gadget (genC p) x₁ y₁ p.jname p.jname []) (p.jname + 1) := by
    rw [hG₁.inEnds_gadget]; simp only [Finset.mem_singleton]; rintro (h | h)
    · exact hJ1 h
    · omega
  have hG₂ : GadgetOK (gadget (genC p) x₁ y₁ p.jname p.jname []) x₂ y₂ (p.jname + 1) (p.jname + 1) []
      {p.jname + 1} := gadgetOK_joint hm2 (by omega) hJ1'
  obtain ⟨xm', xp', ym', yp', Km', Kp', h, s₂, t₂⟩ := rungL_gadget hR₁ hG₂ h₂
  refine ⟨xm', xp', ym', yp', Km', Kp', ?_, s₁.trans s₂, t₁.trans t₂⟩
  show IsRungAt (ofEdges (placeJ (genC p) p.jname (.two x₁ y₁ x₂ y₂))) _ _ _ _ _ _ _ _
  rw [placeJ_two, ofEdges_eq_of_sameMult (placeTwo_sameMult hRem)]
  exact h

/-- The same for one joint pair. -/
theorem rungL_placeOne {p : CParam} (hp : p.Valid) {x y : ℕ} (hj : (JParam.one x y).Valid p)
    {a b xm xp ym yp : ℕ} {Km Kp : Finset ℕ} (hR : RungL (genC p) a b xm xp ym yp Km Kp)
    (h₁ : s(x, y) ≠ s(a, b)) :
    ∃ xm' xp' ym' yp' Km' Kp', RungL (genB p (.one x y)) a b xm' xp' ym' yp' Km' Kp' ∧
      Km ⊆ Km' ∧ Kp ⊆ Kp' := by
  obtain ⟨hJ, hJ1⟩ := genC_fresh hp
  obtain ⟨⟨lt, m⟩, -⟩ := hj
  have hG := gadgetOK_joints (es := genC p) m (by omega) (show p.jname ≠ p.jname + 1 by omega) hJ hJ1
  exact rungL_gadget hR hG h₁

/-! ## Counting rungs -/

theorem card_filter_ne_one (m : ℕ) (F : ℕ → Sym2 ℕ) (hF : ∀ i j, F i = F j → i = j) (P : Sym2 ℕ) :
    m - 1 ≤ ((Finset.range m).filter (fun i => P ≠ F i)).card := by
  classical
  have h1 : ((Finset.range m).filter (fun i => P = F i)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact hF a b (ha.2.symm.trans hb.2)
  have := Finset.card_filter_add_card_filter_not (s := Finset.range m) (fun i => P = F i)
  rw [Finset.card_range] at this
  simp only [ne_eq]
  omega

theorem card_filter_ne_two (m : ℕ) (F : ℕ → Sym2 ℕ) (hF : ∀ i j, F i = F j → i = j) (P Q : Sym2 ℕ) :
    m - 2 ≤ ((Finset.range m).filter (fun i => P ≠ F i ∧ Q ≠ F i)).card := by
  classical
  have hP := card_filter_ne_one m F hF P
  have : ((Finset.range m).filter (fun i => P ≠ F i)).filter (fun i => Q ≠ F i) =
      (Finset.range m).filter (fun i => P ≠ F i ∧ Q ≠ F i) := Finset.filter_filter _ _ _
  rw [← this]
  have h1 : (((Finset.range m).filter (fun i => P ≠ F i)).filter (fun i => Q = F i)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact hF a b (ha.2.symm.trans hb.2)
  have := Finset.card_filter_add_card_filter_not
    (s := (Finset.range m).filter (fun i => P ≠ F i)) (fun i => Q = F i)
  simp only [ne_eq] at this hP h1 ⊢
  omega

theorem rungPair_inj (c : ℕ) : ∀ i j, s(c + 4 * i, c + 4 * i + 1) = s(c + 4 * j, c + 4 * j + 1) → i = j := by
  intro i j h; rw [Sym2.eq_iff] at h; omega

theorem card_image_rung (c : ℕ) (A : Finset ℕ) : (A.image fun i => c + 4 * i).card = A.card :=
  Finset.card_image_of_injective _ (fun i j (h : c + 4 * i = c + 4 * j) => by omega)

/-! ## The atoms of a generated block -/

theorem card_genB_le {p : CParam} (hp : p.Valid) {j : JParam} (hj : j.Valid p) :
    (ofEdges (genB p j)).verts.card ≤ 5 + 2 * (p.k + p.k₂) := by
  classical
  set S : Finset ℕ := Finset.range 3 ∪ (Finset.range p.k).image (fun i => 3 + 4 * i) ∪
    (Finset.range p.k).image (fun i => 3 + 4 * i + 1) ∪ (Finset.range p.k₂).image (fun i => 5 + 4 * i) ∪
    (Finset.range p.k₂).image (fun i => 5 + 4 * i + 1) ∪ {p.jname, p.jname + 1}
  have hsub : (ofEdges (genB p j)).verts ⊆ S := by
    intro z hz
    rw [mem_ofEdges_verts] at hz
    have hz' : InEnds (genC p) z ∨ z = p.jname ∨ z = p.jname + 1 := by
      obtain ⟨hj', -⟩ := hj
      rcases j with ⟨x₁, y₁, x₂, y₂⟩ | ⟨x, y⟩
      · obtain ⟨-, -, -, m₁, m₂⟩ := hj'
        exact (inEnds_placeTwo (removable2_of_valid m₁ m₂) z).mp hz
      · exact (inEnds_placeOne hj'.2 z).mp hz
    simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    rcases hz' with hz' | rfl | rfl
    · rcases genC_ends hp hz' with h | ⟨i, hi, h | h⟩ | ⟨i, hi, h | h⟩
      · left; left; left; left; left; omega
      · left; left; left; left; right; exact ⟨i, hi, h.symm⟩
      · left; left; left; right; exact ⟨i, hi, h.symm⟩
      · left; left; right; exact ⟨i, hi, h.symm⟩
      · left; right; exact ⟨i, hi, h.symm⟩
    · right; left; rfl
    · right; right; rfl
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  have c1 := Finset.card_image_le (s := Finset.range p.k) (f := fun i => 3 + 4 * i)
  have c2 := Finset.card_image_le (s := Finset.range p.k) (f := fun i => 3 + 4 * i + 1)
  have c3 := Finset.card_image_le (s := Finset.range p.k₂) (f := fun i => 5 + 4 * i)
  have c4 := Finset.card_image_le (s := Finset.range p.k₂) (f := fun i => 5 + 4 * i + 1)
  have u1 := Finset.card_union_le (Finset.range 3) ((Finset.range p.k).image (fun i => 3 + 4 * i))
  have u2 := Finset.card_union_le (Finset.range 3 ∪ (Finset.range p.k).image (fun i => 3 + 4 * i))
    ((Finset.range p.k).image (fun i => 3 + 4 * i + 1))
  have u3 := Finset.card_union_le (Finset.range 3 ∪ (Finset.range p.k).image (fun i => 3 + 4 * i) ∪
    (Finset.range p.k).image (fun i => 3 + 4 * i + 1)) ((Finset.range p.k₂).image (fun i => 5 + 4 * i))
  have u4 := Finset.card_union_le (Finset.range 3 ∪ (Finset.range p.k).image (fun i => 3 + 4 * i) ∪
    (Finset.range p.k).image (fun i => 3 + 4 * i + 1) ∪ (Finset.range p.k₂).image (fun i => 5 + 4 * i))
    ((Finset.range p.k₂).image (fun i => 5 + 4 * i + 1))
  have c5 : ({p.jname, p.jname + 1} : Finset ℕ).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_range] at u1
  rw [Finset.card_range] at c1 c2 c3 c4
  omega

/-! ## The rungs of the generated block -/

/-- The bonds carrying the joints. -/
def JParam.pairs : JParam → Sym2 ℕ × Sym2 ℕ
  | .two x₁ y₁ x₂ y₂ => (s(x₁, y₁), s(x₂, y₂))
  | .one x y => (s(x, y), s(x, y))

theorem rungL_placeJ {p : CParam} (hp : p.Valid) {j : JParam} (hj : j.Valid p) {a b xm xp ym yp : ℕ}
    {Km Kp : Finset ℕ} (hR : RungL (genC p) a b xm xp ym yp Km Kp) (h₁ : j.pairs.1 ≠ s(a, b))
    (h₂ : j.pairs.2 ≠ s(a, b)) :
    ∃ xm' xp' ym' yp' Km' Kp', RungL (genB p j) a b xm' xp' ym' yp' Km' Kp' ∧ Km ⊆ Km' ∧ Kp ⊆ Kp' := by
  rcases j with ⟨x₁, y₁, x₂, y₂⟩ | ⟨x, y⟩
  · exact rungL_placeTwo hp hj hR h₁ h₂
  · exact rungL_placeOne hp hj hR h₁

theorem delL_of_rungL {p : CParam} {j : JParam} {n xm xp ym yp : ℕ} {Km Kp : Finset ℕ}
    (hR : RungL (genB p j) n (n + 1) xm xp ym yp Km Kp) (hn : n + 1 < p.jname) {zm zp : ℕ} (hzm : zm ∈ Km)
    (hzp : zp ∈ Kp) (hzm' : zm < p.jname) (hzp' : zp < p.jname) : DelL (genB p j) p.jname (p.jname + 1) n :=
  ⟨xm, xp, ym, yp, Km, Kp, hR, by omega, by omega, by omega, by omega, ⟨zm, hzm, by omega, by omega⟩,
    ⟨zp, hzp, by omega, by omega⟩⟩

theorem connected_gen1 (K : ℕ) : Connected (ofEdges (gen1 K)) :=
  connected_ladder K connected_tri mult_tri_01 (by omega) (fresh_gen1 K)

theorem zero_mem_gen1 (K : ℕ) : 0 ∈ (ofEdges (gen1 K)).verts :=
  mem_ofEdges_verts.mpr (gen1_ends_of (Or.inl (by omega)))

/-- The rungs of the first ladder. -/
theorem rungL_gen1 (K i : ℕ) (hi : i + 2 ≤ K) :
    ∃ xm xp ym yp Km Kp, RungL (gen1 K) (3 + 4 * i) (3 + 4 * i + 1) xm xp ym yp Km Kp ∧
      3 + 4 * (i + 1) ∈ Km ∧ 0 ∈ Kp := by
  obtain ⟨xm, xp, ym, yp, Km, Kp, h, h1, h2⟩ :=
    rungL_ladder K connected_tri mult_tri_01 (by omega) (fresh_gen1 K) i hi (fun _ => by decide)
  exact ⟨xm, xp, ym, yp, Km, Kp, h, h1,
    h2 (mem_ofEdges_verts.mpr (inEnds_tri.mpr (by omega)))⟩

theorem ind_one_iff (u v x y : ℕ) : ind u v x y = 1 ↔ s(u, v) = s(x, y) := by
  unfold ind; split_ifs with h <;> simp [h]

theorem ind_zero_iff (u v x y : ℕ) : ind u v x y = 0 ↔ s(u, v) ≠ s(x, y) := by
  unfold ind; split_ifs with h <;> simp [h]

/-- In a block with two ladders, the joints sit on the two triple bonds. -/
theorem joints_two_ladders {k k' x₀ y₀ : ℕ} (hp : CParam.Valid ⟨k + 1, some (x₀, y₀, k' + 1)⟩) {j : JParam}
    (hj : j.Valid ⟨k + 1, some (x₀, y₀, k' + 1)⟩) :
    ∀ a b, s(a, b) ≠ s(4 * k + 3, 4 * k + 4) → s(a, b) ≠ s(4 * k' + 5, 4 * k' + 6) →
      j.pairs.1 ≠ s(a, b) ∧ j.pairs.2 ≠ s(a, b) := by
  obtain ⟨hk, hk', hlt₀, h0, h0le⟩ := hp
  generalize hpdef : (⟨k + 1, some (x₀, y₀, k' + 1)⟩ : CParam) = p at hj
  have hJ : p.jname = 4 * k + 4 * k' + 11 := by
    rw [← hpdef]; simp only [CParam.jname, CParam.k₂]; ring
  have hgenC : genC p = ladder (k' + 1) (gen1 (k + 1)) x₀ y₀ 5 := by rw [← hpdef]; rfl
  set E := gen1 (k + 1)
  have hF : Fresh (k' + 1) E 5 := fresh_second (k + 1) (k' + 1)
  have ht₁E : mult E (4 * k + 3) (4 * k + 4) = 3 := gen1_triple k
  have hne₀ : s(x₀, y₀) ≠ s(4 * k + 3, 4 * k + 4) := by
    intro h; have := ht₁E; rw [mult_eq_count, ← h, ← mult_eq_count] at this; omega
  have T₁ : mult (genC p) (4 * k + 3) (4 * k + 4) = 3 := by
    have := ladder_old (k' + 1) (x := x₀) (y := y₀) (N := 5) (u := 4 * k + 3) (v := 4 * k + 4) h0
      (by rintro ⟨i, _, h⟩; omega) (by rintro ⟨i, _, h⟩; omega)
    rw [if_neg (fun h => hne₀ h.2.symm), ht₁E] at this
    rw [hgenC]; omega
  have T₂ : mult (genC p) (4 * k' + 5) (4 * k' + 6) = 3 := by
    have := ladder_newest k' h0 hF
    rw [show 5 + 4 * k' = 4 * k' + 5 by ring, show 4 * k' + 5 + 1 = 4 * k' + 6 by ring] at this
    rw [hgenC]; exact this
  have hle := hj.2
  have t12 : s(4 * k + 3, 4 * k + 4) ≠ s(4 * k' + 5, 4 * k' + 6) := by rw [Ne, Sym2.eq_iff]; omega
  obtain ⟨hj', -⟩ := hj
  rcases j with ⟨x₁, y₁, x₂, y₂⟩ | ⟨x, y⟩
  · obtain ⟨-, -, -, m₁, m₂⟩ := hj'
    have hRem := removable2_of_valid m₁ m₂
    have key : ∀ u v, u < p.jname → v < p.jname → mult (genC p) u v = 3 →
        ind u v x₁ y₁ + ind u v x₂ y₂ ≥ 1 := by
      intro u v hu hv h3
      have := mult_placeTwo (J₁ := p.jname) (J₂ := p.jname + 1) hRem u v
      rw [h3, ind_eq_zero (u := u) (v := v) (x := x₁) (y := p.jname) (by omega),
        ind_eq_zero (u := u) (v := v) (x := p.jname) (y := y₁) (by omega),
        ind_eq_zero (u := u) (v := v) (x := x₂) (y := p.jname + 1) (by omega),
        ind_eq_zero (u := u) (v := v) (x := p.jname + 1) (y := y₂) (by omega)] at this
      by_contra hh
      have e : genB p (.two x₁ y₁ x₂ y₂) = placeTwo (genC p) x₁ y₁ p.jname x₂ y₂ (p.jname + 1) := rfl
      have := multLe2_le hle (show mult (genB p (.two x₁ y₁ x₂ y₂)) u v ≠ 0 by rw [e]; omega)
      rw [e] at this
      omega
    have k₁ := key _ _ (by rw [hJ]; omega) (by rw [hJ]; omega) T₁
    have k₂ := key _ _ (by rw [hJ]; omega) (by rw [hJ]; omega) T₂
    intro a b ha hb
    have i1 := ind_zero_iff (4 * k + 3) (4 * k + 4)
    have i2 := ind_zero_iff (4 * k' + 5) (4 * k' + 6)
    have o1 := ind_one_iff (4 * k + 3) (4 * k + 4)
    have o2 := ind_one_iff (4 * k' + 5) (4 * k' + 6)
    constructor
    · intro h
      simp only [JParam.pairs] at h
      have a1 : ind (4 * k + 3) (4 * k + 4) x₁ y₁ = 0 := (i1 _ _).mpr (by rw [h]; exact Ne.symm ha)
      have a2 : ind (4 * k' + 5) (4 * k' + 6) x₁ y₁ = 0 := (i2 _ _).mpr (by rw [h]; exact Ne.symm hb)
      have b1 := (o1 x₂ y₂).mp (by unfold ind at *; split_ifs at * <;> omega)
      have b2 := (o2 x₂ y₂).mp (by unfold ind at *; split_ifs at * <;> omega)
      exact t12 (b1.trans b2.symm)
    · intro h
      simp only [JParam.pairs] at h
      have a1 : ind (4 * k + 3) (4 * k + 4) x₂ y₂ = 0 := (i1 _ _).mpr (by rw [h]; exact Ne.symm ha)
      have a2 : ind (4 * k' + 5) (4 * k' + 6) x₂ y₂ = 0 := (i2 _ _).mpr (by rw [h]; exact Ne.symm hb)
      have b1 := (o1 x₁ y₁).mp (by unfold ind at *; split_ifs at * <;> omega)
      have b2 := (o2 x₁ y₁).mp (by unfold ind at *; split_ifs at * <;> omega)
      exact t12 (b1.trans b2.symm)
  · obtain ⟨-, m⟩ := hj'
    have key : ∀ u v, u < p.jname → v < p.jname → mult (genC p) u v = 3 → s(u, v) = s(x, y) := by
      intro u v hu hv h3
      have := mult_placeOne (J₁ := p.jname) (J₂ := p.jname + 1) m u v
      rw [h3, ind_eq_zero (u := u) (v := v) (x := x) (y := p.jname) (by omega),
        ind_eq_zero (u := u) (v := v) (x := p.jname) (y := p.jname + 1) (by omega),
        ind_eq_zero (u := u) (v := v) (x := p.jname + 1) (y := y) (by omega)] at this
      by_contra hh
      rw [(ind_zero_iff u v x y).mpr hh] at this
      have e : genB p (.one x y) = placeOne (genC p) x y p.jname (p.jname + 1) := rfl
      have := multLe2_le hle (show mult (genB p (.one x y)) u v ≠ 0 by rw [e]; omega)
      rw [e] at this
      omega
    exact absurd ((key _ _ (by rw [hJ]; omega) (by rw [hJ]; omega) T₁).trans
      (key _ _ (by rw [hJ]; omega) (by rw [hJ]; omega) T₂).symm) t12

/-! ## Deletable rungs of the generated blocks -/

theorem jname_one (K : ℕ) : CParam.jname ⟨K, none⟩ = 4 * K + 3 := by simp [CParam.jname, CParam.k₂]

theorem jname_two (k k' x₀ y₀ : ℕ) : CParam.jname ⟨k + 1, some (x₀, y₀, k' + 1)⟩ = 4 * k + 4 * k' + 11 := by
  simp only [CParam.jname, CParam.k₂]; ring

theorem delL_one {K : ℕ} {j : JParam} (hj : j.Valid ⟨K, none⟩) {i : ℕ} (hi : i + 2 ≤ K)
    (h₁ : j.pairs.1 ≠ s(3 + 4 * i, 3 + 4 * i + 1)) (h₂ : j.pairs.2 ≠ s(3 + 4 * i, 3 + 4 * i + 1)) :
    DelL (genB ⟨K, none⟩ j) (CParam.jname ⟨K, none⟩) (CParam.jname ⟨K, none⟩ + 1) (3 + 4 * i) := by
  obtain ⟨xm, xp, ym, yp, Km, Kp, hR, hm, h0⟩ := rungL_gen1 K i hi
  obtain ⟨_, _, _, _, Km', Kp', hR', hKm, hKp⟩ := rungL_placeJ (p := ⟨K, none⟩) trivial hj hR h₁ h₂
  exact delL_of_rungL hR' (by rw [jname_one]; omega) (hKm hm) (hKp h0) (by rw [jname_one]; omega)
    (by rw [jname_one]; omega)

theorem delL_two_first {k k' x₀ y₀ : ℕ} (hp : CParam.Valid ⟨k + 1, some (x₀, y₀, k' + 1)⟩) {j : JParam}
    (hj : j.Valid ⟨k + 1, some (x₀, y₀, k' + 1)⟩) {i : ℕ} (hi : i < k)
    (hne : s(x₀, y₀) ≠ s(3 + 4 * i, 3 + 4 * i + 1)) :
    DelL (genB ⟨k + 1, some (x₀, y₀, k' + 1)⟩ j) (CParam.jname ⟨k + 1, some (x₀, y₀, k' + 1)⟩)
      (CParam.jname ⟨k + 1, some (x₀, y₀, k' + 1)⟩ + 1) (3 + 4 * i) := by
  have hp' := hp
  obtain ⟨-, -, hlt₀, h0, -⟩ := hp
  obtain ⟨xm, xp, ym, yp, Km, Kp, hR, hm, hz⟩ := rungL_gen1 (k + 1) i (by omega)
  obtain ⟨_, _, _, _, Km₁, Kp₁, hR₁, hK₁, hK₁'⟩ :=
    rungL_ladder_persist (k' + 1) hR h0 (by omega) hne (fresh_second (k + 1) (k' + 1))
  have jt := joints_two_ladders hp' hj (3 + 4 * i)
    (3 + 4 * i + 1) (by rw [Ne, Sym2.eq_iff]; omega) (by rw [Ne, Sym2.eq_iff]; omega)
  obtain ⟨_, _, _, _, Km', Kp', hR', hKm, hKp⟩ := rungL_placeJ hp' hj hR₁ jt.1 jt.2
  exact delL_of_rungL hR' (by rw [jname_two]; omega) (hKm (hK₁ hm)) (hKp (hK₁' hz)) (by rw [jname_two]; omega)
    (by rw [jname_two]; omega)

theorem delL_two_second {k k' x₀ y₀ : ℕ} (hp : CParam.Valid ⟨k + 1, some (x₀, y₀, k' + 1)⟩) {j : JParam}
    (hj : j.Valid ⟨k + 1, some (x₀, y₀, k' + 1)⟩) {i : ℕ} (hi : i < k')
    (h0' : i = 0 → 2 ≤ mult (gen1 (k + 1)) x₀ y₀) :
    DelL (genB ⟨k + 1, some (x₀, y₀, k' + 1)⟩ j) (CParam.jname ⟨k + 1, some (x₀, y₀, k' + 1)⟩)
      (CParam.jname ⟨k + 1, some (x₀, y₀, k' + 1)⟩ + 1) (5 + 4 * i) := by
  have hp' := hp
  obtain ⟨-, -, hlt₀, h0, -⟩ := hp
  obtain ⟨xm, xp, ym, yp, Km, Kp, hR, hm, hz⟩ := rungL_ladder (k' + 1) (connected_gen1 (k + 1)) h0 (by omega)
    (fresh_second (k + 1) (k' + 1)) i (by omega) h0'
  have jt := joints_two_ladders hp' hj (5 + 4 * i) (5 + 4 * i + 1) (by rw [Ne, Sym2.eq_iff]; omega)
    (by rw [Ne, Sym2.eq_iff]; omega)
  obtain ⟨_, _, _, _, Km', Kp', hR', hKm, hKp⟩ := rungL_placeJ hp' hj hR jt.1 jt.2
  exact delL_of_rungL hR' (by rw [jname_two]; omega) (hKm hm) (hKp (hz (zero_mem_gen1 (k + 1))))
    (by rw [jname_two]; omega) (by rw [jname_two]; omega)

/-! ## N2 Lemma 1.8 -/

/-- **The rung count** (N2 Lemma 1.8's proof): a T-vine isomorphic to `genB p j` has at least `k + k' − 3`
deletable rungs. -/
theorem laddersLe {V : Type*} [DecidableEq V] {G : UMultigraph V} {j₁ j₂ : V} (hT : IsTVineU G j₁ j₂)
    {p : CParam} {j : JParam} (hp : p.Valid) (hj : j.Valid p) (φ : Iso G (genB p j))
    (hJ : (φ.f j₁ = p.jname ∧ φ.f j₂ = p.jname + 1) ∨ (φ.f j₁ = p.jname + 1 ∧ φ.f j₂ = p.jname)) :
    p.k + p.k₂ ≤ 3 + deletableCount G j₁ j₂ := by
  classical
  have hj₁ : j₁ ∈ G.verts := hT.1.1
  have hj₂ : j₂ ∈ G.verts := hT.1.2.1
  have count : ∀ T : Finset ℕ, (∀ n ∈ T, DelL (genB p j) p.jname (p.jname + 1) n) →
      T.card ≤ deletableCount G j₁ j₂ := fun T hT' => card_le_deletableCount φ hj₁ hj₂ hJ T hT'
  rcases p with ⟨K, _ | ⟨x₀, y₀, K'⟩⟩
  · -- one ladder: at most two rungs are hit by the joints
    simp only [CParam.k₂]
    have hA := card_filter_ne_two (K - 1) (fun i => s(3 + 4 * i, 3 + 4 * i + 1)) (rungPair_inj 3)
      j.pairs.1 j.pairs.2
    have hT' := count (((Finset.range (K - 1)).filter
        (fun i => j.pairs.1 ≠ s(3 + 4 * i, 3 + 4 * i + 1) ∧ j.pairs.2 ≠ s(3 + 4 * i, 3 + 4 * i + 1))).image
          fun i => 3 + 4 * i) (by
      intro n hn
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
      rw [Finset.mem_filter, Finset.mem_range] at hi
      exact delL_one hj (by omega) hi.2.1 hi.2.2)
    rw [card_image_rung] at hT'
    omega
  · -- two ladders
    have hp' := hp
    obtain ⟨hk, hk', hlt₀, h0, h0le⟩ := hp
    dsimp only at hk hk' h0 h0le
    obtain ⟨k, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ m, K' = m + 1 := ⟨K' - 1, by omega⟩
    simp only [CParam.k₂]
    have disj : ∀ (A B : Finset ℕ), Disjoint (A.image fun i => 3 + 4 * i) (B.image fun i => 5 + 4 * i) := by
      intro A B
      rw [Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨i', -, h⟩ := Finset.mem_image.mp hz'
      omega
    by_cases hm2 : 2 ≤ mult (gen1 (k + 1)) x₀ y₀
    · have hA := card_filter_ne_one k (fun i => s(3 + 4 * i, 3 + 4 * i + 1)) (rungPair_inj 3) s(x₀, y₀)
      have hT' := count ((((Finset.range k).filter (fun i => s(x₀, y₀) ≠ s(3 + 4 * i, 3 + 4 * i + 1))).image
          fun i => 3 + 4 * i) ∪ ((Finset.range k').image fun i => 5 + 4 * i)) (by
        intro n hn
        rcases Finset.mem_union.mp hn with hn | hn
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
          rw [Finset.mem_filter, Finset.mem_range] at hi
          exact delL_two_first hp' hj hi.1 hi.2
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
          exact delL_two_second hp' hj (Finset.mem_range.mp hi) (fun _ => hm2))
      rw [Finset.card_union_of_disjoint (disj _ _), card_image_rung, card_image_rung, Finset.card_range] at hT'
      omega
    · have hA := card_filter_ne_one k' (fun i => s(5 + 4 * i, 5 + 4 * i + 1)) (rungPair_inj 5) s(5, 6)
      have hT' := count (((Finset.range k).image fun i => 3 + 4 * i) ∪
          (((Finset.range k').filter (fun i => s(5, 6) ≠ s(5 + 4 * i, 5 + 4 * i + 1))).image
            fun i => 5 + 4 * i)) (by
        intro n hn
        rcases Finset.mem_union.mp hn with hn | hn
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
          refine delL_two_first hp' hj (Finset.mem_range.mp hi) ?_
          intro h
          obtain ⟨_, _, _, _, _, _, hR, -⟩ := rungL_gen1 (k + 1) i (by have := Finset.mem_range.mp hi; omega)
          have := hR.mult_ab
          rw [ofEdges_mult, mult_eq_count, ← h, ← mult_eq_count] at this
          omega
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
          rw [Finset.mem_filter, Finset.mem_range] at hi
          refine delL_two_second hp' hj hi.1 (fun h0 => absurd ?_ hi.2)
          subst h0; rfl)
      rw [Finset.card_union_of_disjoint (disj _ _), card_image_rung, card_image_rung, Finset.card_range] at hT'
      omega

/-- **N2 Lemma 1.8 (size bound).** Every T-vine satisfies `|B| ≤ 11 + 2 D(B)`. -/
theorem sizeBound : SizeBoundStatement.{u} := by
  intro V _ G j₁ j₂ hT
  obtain ⟨p, j, hp, hj, φ, hJ⟩ := generation G j₁ j₂ hT
  rw [card_verts_iso φ]
  have hc := card_genB_le hp hj
  have hD := laddersLe hT hp hj φ hJ
  omega

end WaveTurbulence.TVine.Checker
