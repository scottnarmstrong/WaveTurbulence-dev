/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.RungPersist

/-!
# The rungs of a ladder

* `connected_gadget`: gadget replacement keeps a bond list connected;
* `rungL_create`: after a ladder extension (the (Z1) move on the triple bond `a ≡ b` just created on `c–d`), the
  pair `a = b` is a 2-cut rung, with poles the new pair and the old atoms, provided `c–d` had multiplicity ≥ 2;
* `rungL_ladder_persist`: a 2-cut rung persists through a whole ladder started on another bond;
* `rungL_ladder`: in `ladder k es x y N`, the pair `N + 4i, N + 4i + 1` is a 2-cut rung for every `i + 2 ≤ k`
  (`i ≥ 1`, or `i = 0` when `x–y` has multiplicity ≥ 2), its outer pole containing the atoms of `es` and its inner
  pole the next pair.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine Core

/-- `GadgetOK` for a (Z1) move with fresh names. -/
theorem gadgetOK_z1 {es : Edges} {x y a : ℕ} (hxy : mult es x y ≠ 0) (hne : x ≠ y) (ha : ¬ InEnds es a)
    (ha1 : ¬ InEnds es (a + 1)) : GadgetOK es x y a (a + 1) [(a, a + 1), (a, a + 1), (a, a + 1)] {a, a + 1} where
  hxy := hxy
  x_ne_y := hne
  w₁_mem := by simp
  w₂_mem := by simp
  fresh := by intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw; rcases hw with rfl | rfl <;> assumption
  inner_in := by intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he; rcases he with rfl | rfl | rfl <;> simp
  conn := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · refine Relation.ReflTransGen.single ⟨by simp, by simp, ?_⟩
      rw [mult_list_cons, ind_eq_one (Or.inl ⟨rfl, rfl⟩)]; simp

/-- `GadgetOK` for one joint. -/
theorem gadgetOK_joint {es : Edges} {x y J : ℕ} (hxy : mult es x y ≠ 0) (hne : x ≠ y) (hJ : ¬ InEnds es J) :
    GadgetOK es x y J J [] {J} where
  hxy := hxy
  x_ne_y := hne
  w₁_mem := by simp
  w₂_mem := by simp
  fresh := by intro w hw; rw [Finset.mem_singleton] at hw; subst hw; exact hJ
  inner_in := by simp
  conn := by intro w hw; rw [Finset.mem_singleton] at hw; subst hw; exact Relation.ReflTransGen.refl

/-- `GadgetOK` for two adjacent joints. -/
theorem gadgetOK_joints {es : Edges} {x y J₁ J₂ : ℕ} (hxy : mult es x y ≠ 0) (hne : x ≠ y) (hJ : J₁ ≠ J₂)
    (hJ₁ : ¬ InEnds es J₁) (hJ₂ : ¬ InEnds es J₂) : GadgetOK es x y J₁ J₂ [(J₁, J₂)] {J₁, J₂} where
  hxy := hxy
  x_ne_y := hne
  w₁_mem := by simp
  w₂_mem := by simp
  fresh := by intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw; rcases hw with rfl | rfl <;> assumption
  inner_in := by intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he; simp
  conn := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · refine Relation.ReflTransGen.single ⟨by simp, by simp, ?_⟩
      rw [mult_list_cons, ind_eq_one (Or.inl ⟨rfl, rfl⟩)]; simp

/-! ## Connectivity -/

/-- One old step, rerouted through the gadget if it used the replaced copy. -/
theorem reroute {es : Edges} {x y w₁ w₂ : ℕ} {inner : Edges} {W Y : Finset ℕ}
    (hG : GadgetOK es x y w₁ w₂ inner W) (hxY : x ∈ Y) (hyY : y ∈ Y) (hWY : W ⊆ Y) {p q : ℕ} (hp : p ∈ Y)
    (hq : q ∈ Y) (hpW : p ∉ W) (hqW : q ∉ W) (hpq : mult es p q ≠ 0) :
    Relation.ReflTransGen (AdjIn (ofEdges (gadget es x y w₁ w₂ inner)) Y) p q := by
  have hold := hG.mult_old hpW hqW
  by_cases hn : mult (gadget es x y w₁ w₂ inner) p q = 0
  · have hpq' : s(p, q) = s(x, y) := by
      by_contra hh; unfold ind at hold; rw [if_neg hh] at hold; omega
    have hxw : AdjIn (ofEdges (gadget es x y w₁ w₂ inner)) Y x w₁ :=
      ⟨hxY, hWY hG.w₁_mem, by rw [ofEdges_mult, hG.mult_x_new hG.w₁_mem, if_pos rfl]; omega⟩
    have hwy : AdjIn (ofEdges (gadget es x y w₁ w₂ inner)) Y w₂ y :=
      ⟨hWY hG.w₂_mem, hyY, by rw [ofEdges_mult, mult_comm, hG.mult_y_new hG.w₂_mem, if_pos rfl]; omega⟩
    have path : Relation.ReflTransGen (AdjIn (ofEdges (gadget es x y w₁ w₂ inner)) Y) x y :=
      (Relation.ReflTransGen.single hxw).trans ((gadget_conn hG hWY hG.w₂_mem).tail hwy)
    rw [Sym2.eq_iff] at hpq'
    rcases hpq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact path
    · exact rtg_adjIn_symm path
  · exact Relation.ReflTransGen.single ⟨hp, hq, by rw [ofEdges_mult]; exact hn⟩

theorem connected_gadget {es : Edges} {x y w₁ w₂ : ℕ} {inner : Edges} {W : Finset ℕ}
    (hG : GadgetOK es x y w₁ w₂ inner W) (hc : Connected (ofEdges es)) :
    Connected (ofEdges (gadget es x y w₁ w₂ inner)) := by
  set Y := (ofEdges (gadget es x y w₁ w₂ inner)).verts
  have memY : ∀ z, z ∈ Y ↔ InEnds es z ∨ z ∈ W := fun z => by rw [mem_ofEdges_verts, hG.inEnds_gadget]
  have hxY : x ∈ Y := (memY x).mpr (Or.inl hG.x_ends)
  have hyY : y ∈ Y := (memY y).mpr (Or.inl hG.y_ends)
  have hWY : W ⊆ Y := fun w hw => (memY w).mpr (Or.inr hw)
  have toX : ∀ u ∈ Y, Relation.ReflTransGen (AdjIn (ofEdges (gadget es x y w₁ w₂ inner)) Y) x u := by
    intro u hu
    rcases (memY u).mp hu with hu | hu
    · have := hc x (mem_ofEdges_verts.mpr hG.x_ends) u (mem_ofEdges_verts.mpr hu)
      refine rtg_map (fun p q ⟨hp, hq, hpq⟩ => ?_) this
      have hpe := mem_ofEdges_verts.mp hp; have hqe := mem_ofEdges_verts.mp hq
      exact reroute hG hxY hyY hWY ((memY p).mpr (Or.inl hpe)) ((memY q).mpr (Or.inl hqe))
        (fun h => hG.fresh p h hpe) (fun h => hG.fresh q h hqe) (by rw [ofEdges_mult] at hpq; exact hpq)
    · have hxw : AdjIn (ofEdges (gadget es x y w₁ w₂ inner)) Y x w₁ :=
        ⟨hxY, hWY hG.w₁_mem, by rw [ofEdges_mult, hG.mult_x_new hG.w₁_mem, if_pos rfl]; omega⟩
      exact (Relation.ReflTransGen.single hxw).trans (gadget_conn hG hWY hu)
  intro u hu v hv
  exact (rtg_adjIn_symm (toX u hu)).trans (toX v hv)

theorem connected_tri : Connected (ofEdges tri) := by
  intro u hu v hv
  have hu' := inEnds_tri.mp (mem_ofEdges_verts.mp hu)
  have hv' := inEnds_tri.mp (mem_ofEdges_verts.mp hv)
  have adj : ∀ p q, p ≤ 2 → q ≤ 2 → p ≠ q → AdjIn (ofEdges tri) (ofEdges tri).verts p q := by
    intro p q hp hq hpq
    refine ⟨mem_ofEdges_verts.mpr (inEnds_tri.mpr hp), mem_ofEdges_verts.mpr (inEnds_tri.mpr hq), ?_⟩
    rw [ofEdges_mult, mult_tri_eq p q hp hq, if_neg hpq]; omega
  by_cases h : u = v
  · subst h; exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (adj u v hu' hv' h)

theorem connected_ladder : ∀ (k : ℕ) {es : Edges} {x y N : ℕ} (_hc : Connected (ofEdges es))
    (_hxy : mult es x y ≠ 0) (_hne : x ≠ y) (_hf : Fresh k es N), Connected (ofEdges (ladder k es x y N))
  | 0, _, _, _, _, hc, _, _, _ => hc
  | k + 1, es, x, y, N, hc, hxy, hne, hf => by
    rw [ladder]
    have hN : ¬ InEnds es N := hf N ⟨0, by omega, Or.inl (by omega)⟩
    have hN1 : ¬ InEnds es (N + 1) := hf (N + 1) ⟨0, by omega, Or.inr (by omega)⟩
    have hG := gadgetOK_z1 hxy hne hN hN1
    refine connected_ladder k (connected_gadget hG hc) (z1_ne_zero_new es x y N (N + 1) hxy) (by omega) ?_
    intro z hz hz'
    rcases inEnds_z1 hxy hz' with h | h | h
    · exact hf z (isNew_succ.mpr (Or.inr (Or.inr hz))) h
    · obtain ⟨i, _, h'⟩ := hz; omega
    · obtain ⟨i, _, h'⟩ := hz; omega

/-! ## Creation of a rung -/

/-- **Creation**: after the (Z1) moves on `c–d` (creating `a ≡ a+1`) and on `a ≡ a+1` (creating `a+4 ≡ a+5`), the
pair `a = a+1` is a 2-cut rung with poles `{a+4, a+5}` and the old atoms, provided `c–d` had multiplicity ≥ 2. -/
theorem rungL_create {E : Edges} {c d a : ℕ} (hconn : Connected (ofEdges E)) (hcd : 2 ≤ mult E c d) (hne : c ≠ d)
    (ha : ¬ InEnds E a) (ha1 : ¬ InEnds E (a + 1)) (ha4 : ¬ InEnds E (a + 4)) (ha5 : ¬ InEnds E (a + 5)) :
    RungL (z1 (z1 E c d a (a + 1)) a (a + 1) (a + 4) (a + 5)) a (a + 1) (a + 4) c (a + 5) d {a + 4, a + 5}
      (ofEdges E).verts := by
  have hG₁ := gadgetOK_z1 (show mult E c d ≠ 0 by omega) hne ha ha1
  set E₁ := z1 E c d a (a + 1) with hE₁
  have h3 : mult E₁ a (a + 1) = 3 := by
    rw [hE₁, z1_eq_gadget, hG₁.mult_in_new (by simp) (by simp)]
    simp only [mult_list_cons, mult_nil, ind_eq_one (Or.inl ⟨rfl, rfl⟩)]
  have hE₁4 : ¬ InEnds E₁ (a + 4) := by
    rw [hE₁, z1_eq_gadget, hG₁.inEnds_gadget]; simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact ha4 h
    · omega
    · omega
  have hE₁5 : ¬ InEnds E₁ (a + 5) := by
    rw [hE₁, z1_eq_gadget, hG₁.inEnds_gadget]; simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact ha5 h
    · omega
    · omega
  have hG₂ := gadgetOK_z1 (show mult E₁ a (a + 1) ≠ 0 by omega) (by omega) hE₁4 hE₁5
  have hc := hG₁.x_ends; have hd := hG₁.y_ends
  have nE : ∀ z, InEnds E z → z ≠ a ∧ z ≠ a + 1 ∧ z ≠ a + 4 ∧ z ≠ a + 5 := by
    intro z hz
    exact ⟨fun h => ha (h ▸ hz), fun h => ha1 (h ▸ hz), fun h => ha4 (h ▸ hz), fun h => ha5 (h ▸ hz)⟩
  obtain ⟨ca, ca1, ca4, ca5⟩ := nE c hc
  obtain ⟨da, da1, da4, da5⟩ := nE d hd
  have W₁ : ∀ z, z ∈ ({a, a + 1} : Finset ℕ) ↔ z = a ∨ z = a + 1 := by intro z; simp
  have W₂ : ∀ z, z ∈ ({a + 4, a + 5} : Finset ℕ) ↔ z = a + 4 ∨ z = a + 5 := by intro z; simp
  -- the multiplicities in `E₂` of pairs avoiding the new atoms
  have m₂ : ∀ u v, u ≠ a + 4 → u ≠ a + 5 → v ≠ a + 4 → v ≠ a + 5 →
      mult (z1 E₁ a (a + 1) (a + 4) (a + 5)) u v + ind u v a (a + 1) = mult E₁ u v := by
    intro u v h1 h2 h3 h4
    rw [z1_eq_gadget]; exact hG₂.mult_old (by rw [W₂]; omega) (by rw [W₂]; omega)
  have m₁ : ∀ u v, u ≠ a → u ≠ a + 1 → v ≠ a → v ≠ a + 1 → mult E₁ u v + ind u v c d = mult E u v := by
    intro u v h1 h2 h3 h4
    rw [hE₁, z1_eq_gadget]; exact hG₁.mult_old (by rw [W₁]; omega) (by rw [W₁]; omega)
  have memE₂ : ∀ z, z ∈ (ofEdges (z1 E₁ a (a + 1) (a + 4) (a + 5))).verts ↔
      InEnds E z ∨ z = a ∨ z = a + 1 ∨ z = a + 4 ∨ z = a + 5 := by
    intro z
    rw [mem_ofEdges_verts, z1_eq_gadget, hG₂.inEnds_gadget, hE₁, z1_eq_gadget, hG₁.inEnds_gadget, W₁, W₂]
    tauto
  refine ⟨by omega, (memE₂ a).mpr (Or.inr (Or.inl rfl)), (memE₂ (a + 1)).mpr (Or.inr (Or.inr (Or.inl rfl))),
    ?_, ?_, ?_, ?_, ?_, ?_, by simp, mem_ofEdges_verts.mpr hc, by simp, mem_ofEdges_verts.mpr hd, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · have := m₂ a (a + 1) (by omega) (by omega) (by omega) (by omega)
    rw [ind_eq_one (Or.inl ⟨rfl, rfl⟩), h3] at this
    rw [ofEdges_mult]; omega
  · rw [Finset.disjoint_left]
    intro z hz hz'
    rw [W₂] at hz
    have := nE z (mem_ofEdges_verts.mp hz'); omega
  · ext z
    simp only [Finset.mem_union, Finset.mem_erase, memE₂ z, W₂, mem_ofEdges_verts]
    constructor
    · rintro (h | h)
      · omega
      · have := nE z h; exact ⟨this.2.1, this.1, Or.inl h⟩
    · rintro ⟨h1, h2, h3 | h3 | h3 | h3 | h3⟩
      · exact Or.inr h3
      · omega
      · omega
      · exact Or.inl (Or.inl h3)
      · exact Or.inl (Or.inr h3)
  · intro u hu v hv
    rw [W₂] at hu hv
    have adj : AdjIn (ofEdges (z1 E₁ a (a + 1) (a + 4) (a + 5))) {a + 4, a + 5} (a + 4) (a + 5) := by
      refine ⟨by simp, by simp, ?_⟩
      rw [ofEdges_mult, z1_eq_gadget, hG₂.mult_in_new (by simp) (by simp)]
      simp only [mult_list_cons, mult_nil, ind_eq_one (Or.inl ⟨rfl, rfl⟩)]; omega
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single adj
    · exact Relation.ReflTransGen.single (adjIn_symm adj)
    · exact Relation.ReflTransGen.refl
  · intro u hu v hv
    refine rtg_map (fun p q ⟨hp, hq, hpq⟩ => Relation.ReflTransGen.single ⟨hp, hq, ?_⟩) (hconn u hu v hv)
    have hp' := nE p (mem_ofEdges_verts.mp hp); have hq' := nE q (mem_ofEdges_verts.mp hq)
    have e2 := m₂ p q hp'.2.2.1 hp'.2.2.2 hq'.2.2.1 hq'.2.2.2
    have e1 := m₁ p q hp'.1 hp'.2.1 hq'.1 hq'.2.1
    rw [ind_eq_zero (by omega)] at e2
    rw [ofEdges_mult] at hpq ⊢
    by_cases h : s(p, q) = s(c, d)
    · have : mult E p q = mult E c d := by rw [mult_eq_count, h, ← mult_eq_count]
      unfold ind at e1; rw [if_pos h] at e1; omega
    · unfold ind at e1; rw [if_neg h] at e1; omega
  · intro u hu w hw
    rw [W₂] at hu
    have hw' := nE w (mem_ofEdges_verts.mp hw)
    rw [ofEdges_mult, mult_comm, z1_eq_gadget]
    exact hG₂.mult_new_zero (by rw [W₂]; omega) hw'.1 hw'.2.1 (by rw [W₂]; exact hu)
  · rw [ofEdges_mult, z1_eq_gadget, hG₂.mult_x_new (by simp), if_pos rfl]
  · have := m₂ a c (by omega) (by omega) (by omega) (by omega)
    rw [ind_eq_zero (by omega), Nat.add_zero] at this
    rw [ofEdges_mult, this, mult_comm, hE₁, z1_eq_gadget, hG₁.mult_x_new (by simp), if_pos rfl]
  · rw [ofEdges_mult, z1_eq_gadget, hG₂.mult_y_new (by simp), if_pos rfl]
  · have := m₂ (a + 1) d (by omega) (by omega) (by omega) (by omega)
    rw [ind_eq_zero (by omega), Nat.add_zero] at this
    rw [ofEdges_mult, this, mult_comm, hE₁, z1_eq_gadget, hG₁.mult_y_new (by simp), if_pos rfl]
  · intro z h1 h2 h3
    rw [ofEdges_mult]
    by_cases hz : z = a + 4 ∨ z = a + 5
    · rw [z1_eq_gadget, hG₂.mult_x_new (by rw [W₂]; exact hz), if_neg h2]
    rw [not_or] at hz
    have := m₂ a z (by omega) (by omega) hz.1 hz.2
    rw [ind_eq_zero (by omega), Nat.add_zero] at this
    rw [this]
    by_cases hza : z = a
    · subst hza
      rw [hE₁, z1_eq_gadget, hG₁.mult_in_new (by simp) (by simp)]
      simp only [mult_list_cons, mult_nil]
      rw [ind_eq_zero (by omega)]
    by_cases hzd : z = d
    · subst hzd
      rw [mult_comm, hE₁, z1_eq_gadget, hG₁.mult_y_new (by simp), if_neg (by omega)]
    · rw [mult_comm, hE₁, z1_eq_gadget]
      exact hG₁.mult_new_zero (by rw [W₁]; omega) h3 hzd (by simp)
  · intro z h1 h2 h3
    rw [ofEdges_mult]
    by_cases hz : z = a + 4 ∨ z = a + 5
    · rw [z1_eq_gadget, hG₂.mult_y_new (by rw [W₂]; exact hz), if_neg h2]
    rw [not_or] at hz
    have := m₂ (a + 1) z (by omega) (by omega) hz.1 hz.2
    rw [ind_eq_zero (by omega), Nat.add_zero] at this
    rw [this]
    by_cases hza : z = a + 1
    · subst hza
      rw [hE₁, z1_eq_gadget, hG₁.mult_in_new (by simp) (by simp)]
      simp only [mult_list_cons, mult_nil]
      rw [ind_eq_zero (by omega)]
    by_cases hzc : z = c
    · subst hzc
      rw [mult_comm, hE₁, z1_eq_gadget, hG₁.mult_x_new (by simp), if_neg (by omega)]
    · rw [mult_comm, hE₁, z1_eq_gadget]
      exact hG₁.mult_new_zero (by rw [W₁]; omega) hzc h3 (by simp)

/-! ## Rungs through a ladder -/

theorem fresh_z1 {k : ℕ} {es : Edges} {x y N : ℕ} (hxy : mult es x y ≠ 0) (hf : Fresh (k + 1) es N) :
    Fresh k (z1 es x y N (N + 1)) (N + 4) := by
  intro z hz hz'
  rcases inEnds_z1 hxy hz' with h | h | h
  · exact hf z (isNew_succ.mpr (Or.inr (Or.inr hz))) h
  · obtain ⟨i, _, h'⟩ := hz; omega
  · obtain ⟨i, _, h'⟩ := hz; omega

theorem rungL_ladder_persist : ∀ (m : ℕ) {E : Edges} {x y M a b xm xp ym yp : ℕ} {Km Kp : Finset ℕ}
    (_hR : RungL E a b xm xp ym yp Km Kp) (_hxy : mult E x y ≠ 0) (_hne : x ≠ y) (_hab : s(x, y) ≠ s(a, b))
    (_hf : Fresh m E M),
    ∃ xm' xp' ym' yp' Km' Kp', RungL (ladder m E x y M) a b xm' xp' ym' yp' Km' Kp' ∧ Km ⊆ Km' ∧ Kp ⊆ Kp'
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, hR, _, _, _, _ => ⟨_, _, _, _, _, _, hR, subset_refl _, subset_refl _⟩
  | m + 1, E, x, y, M, a, b, xm, xp, ym, yp, Km, Kp, hR, hxy, hne, hab, hf => by
    rw [ladder]
    have hM : ¬ InEnds E M := hf M ⟨0, by omega, Or.inl (by omega)⟩
    have hM1 : ¬ InEnds E (M + 1) := hf (M + 1) ⟨0, by omega, Or.inr (by omega)⟩
    have hG := gadgetOK_z1 hxy hne hM hM1
    obtain ⟨xm', xp', ym', yp', Km', Kp', h, h1, h2⟩ := rungL_gadget hR hG hab
    rw [← z1_eq_gadget] at h
    have haM : a ≠ M := fun hh => hM (hh ▸ hR.a_ends)
    have haM1 : a ≠ M + 1 := fun hh => hM1 (hh ▸ hR.a_ends)
    have hbM : b ≠ M := fun hh => hM (hh ▸ hR.b_ends)
    have hbM1 : b ≠ M + 1 := fun hh => hM1 (hh ▸ hR.b_ends)
    obtain ⟨xm'', xp'', ym'', yp'', Km'', Kp'', h', h1', h2'⟩ :=
      rungL_ladder_persist m h (z1_ne_zero_new E x y M (M + 1) hxy) (by omega)
        (by rw [Ne, Sym2.eq_iff]; omega) (fresh_z1 hxy hf)
    exact ⟨xm'', xp'', ym'', yp'', Km'', Kp'', h', h1.trans h1', h2.trans h2'⟩

theorem ofEdges_verts_z1_sub {es : Edges} {x y a b : ℕ} (hxy : mult es x y ≠ 0) :
    (ofEdges es).verts ⊆ (ofEdges (z1 es x y a b)).verts := by
  intro z hz
  exact mem_ofEdges_verts.mpr (inEnds_z1_of hxy (Or.inl (mem_ofEdges_verts.mp hz)))

/-- **The rungs of a ladder.** -/
theorem rungL_ladder : ∀ (k : ℕ) {es : Edges} {x y N : ℕ} (_hc : Connected (ofEdges es)) (_hxy : mult es x y ≠ 0)
    (_hne : x ≠ y) (_hf : Fresh k es N) (i : ℕ) (_hi : i + 2 ≤ k) (_h0 : i = 0 → 2 ≤ mult es x y),
    ∃ xm xp ym yp Km Kp, RungL (ladder k es x y N) (N + 4 * i) (N + 4 * i + 1) xm xp ym yp Km Kp ∧
      N + 4 * (i + 1) ∈ Km ∧ (ofEdges es).verts ⊆ Kp
  | 0, _, _, _, _, _, _, _, _, _, hi, _ => by omega
  | k + 1, es, x, y, N, hc, hxy, hne, hf, i, hi, h0 => by
    rw [ladder]
    have hN : ¬ InEnds es N := hf N ⟨0, by omega, Or.inl (by omega)⟩
    have hN1 : ¬ InEnds es (N + 1) := hf (N + 1) ⟨0, by omega, Or.inr (by omega)⟩
    have hG := gadgetOK_z1 hxy hne hN hN1
    have hc' := connected_gadget hG hc
    rw [← z1_eq_gadget] at hc'
    rcases i with _ | i
    · -- the first rung: created by the second move
      obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [ladder]
      have hN4 : ¬ InEnds es (N + 4) := hf (N + 4) ⟨1, by omega, Or.inl (by omega)⟩
      have hN5 : ¬ InEnds es (N + 5) := hf (N + 5) ⟨1, by omega, Or.inr (by omega)⟩
      have hR := rungL_create hc (h0 rfl) hne hN hN1 hN4 hN5
      have hf' := fresh_z1 (z1_ne_zero_new es x y N (N + 1) hxy) (fresh_z1 hxy hf)
      obtain ⟨xm', xp', ym', yp', Km', Kp', h, h1, h2⟩ := rungL_ladder_persist k hR
        (z1_ne_zero_new _ N (N + 1) (N + 4) (N + 5) (z1_ne_zero_new es x y N (N + 1) hxy)) (by omega)
        (by rw [Ne, Sym2.eq_iff]; omega) hf'
      refine ⟨xm', xp', ym', yp', Km', Kp', by simpa using h, h1 (by simp), h2⟩
    · obtain ⟨xm, xp, ym, yp, Km, Kp, h, h1, h2⟩ := rungL_ladder k hc' (z1_ne_zero_new es x y N (N + 1) hxy)
        (by omega) (fresh_z1 hxy hf) i (by omega) (fun _ => by
          have := mult_z1' es x y N (N + 1) N (N + 1) hxy
          rw [mult_eq_zero_of_not_inEnds hN] at this
          simp only [z1New, Sym2.eq_iff] at this
          split_ifs at this <;> omega)
      refine ⟨xm, xp, ym, yp, Km, Kp, ?_, ?_, (ofEdges_verts_z1_sub hxy).trans h2⟩
      · rw [show N + 4 * (i + 1) = N + 4 + 4 * i by ring]; exact h
      · rw [show N + 4 * (i + 1 + 1) = N + 4 + 4 * (i + 1) by ring]; exact h1

end WaveTurbulence.TVine.Checker
