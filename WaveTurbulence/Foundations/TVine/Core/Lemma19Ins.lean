/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.SmoothInv

/-!
# Rung insertion at a 2-edge-cut: the inserted graph (N2 Lemma 1.9(2), applied undirected)

* 2-edge-cuts of a block: `cut_split`, `cut_compl`, `connOn_side` (each side of a 2-edge-cut is connected),
  `cross_mult_eq` (the two cut copies are the only crossing bonds);
* `InsData G X p q p' q' u v`: the data of an insertion; for `Gi := insertRung G p q p' q' u v`:
  `InsData.verts`, `InsData.mult_u`, `InsData.mult_v`, `InsData.mult_old`, `InsData.isRungAt` (the new rung is a
  2-cut rung with poles `X`, `G.verts \ X`), `InsData.rungDel_eq` (the crossed deletion undoes the insertion),
  `InsData.loopless`, `InsData.isBlockU`, `InsData.mult_le_two`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

/-! ## Two-edge cuts of a block -/

/-- Splitting a set into two parts with no bond between them splits its cut. -/
theorem cut_split (G : UMultigraph V) {X Z W : Finset V} (hX : X ⊆ G.verts) (hZW : Z ∪ W = X)
    (hdisj : Disjoint Z W) (hnb : ∀ z ∈ Z, ∀ w ∈ W, G.mult s(z, w) = 0) : cut G Z + cut G W = cut G X := by
  have hZX : Z ⊆ X := hZW ▸ Finset.subset_union_left
  have hWX : W ⊆ X := hZW ▸ Finset.subset_union_right
  have hZ : G.verts \ Z = W ∪ (G.verts \ X) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx, hxZ⟩
      by_cases hxX : x ∈ X
      · left; rw [← hZW] at hxX; rcases Finset.mem_union.mp hxX with h | h
        · exact absurd h hxZ
        · exact h
      · right; exact ⟨hx, hxX⟩
    · rintro (h | ⟨hx, hxX⟩)
      · exact ⟨hX (hWX h), fun h' => Finset.disjoint_left.mp hdisj h' h⟩
      · exact ⟨hx, fun h' => hxX (hZX h')⟩
  have hW : G.verts \ W = Z ∪ (G.verts \ X) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx, hxW⟩
      by_cases hxX : x ∈ X
      · left; rw [← hZW] at hxX; rcases Finset.mem_union.mp hxX with h | h
        · exact h
        · exact absurd h hxW
      · right; exact ⟨hx, hxX⟩
    · rintro (h | ⟨hx, hxX⟩)
      · exact ⟨hX (hZX h), fun h' => Finset.disjoint_left.mp hdisj h h'⟩
      · exact ⟨hx, fun h' => hxX (hWX h')⟩
  have hd1 : Disjoint W (G.verts \ X) := by
    rw [Finset.disjoint_left]; intro x hx h; exact (Finset.mem_sdiff.mp h).2 (hWX hx)
  have hd2 : Disjoint Z (G.verts \ X) := by
    rw [Finset.disjoint_left]; intro x hx h; exact (Finset.mem_sdiff.mp h).2 (hZX hx)
  have h0 : ∑ z ∈ Z, ∑ w ∈ W, G.mult s(z, w) = 0 :=
    Finset.sum_eq_zero fun z hz => Finset.sum_eq_zero fun w hw => hnb z hz w hw
  have h0' : ∑ w ∈ W, ∑ z ∈ Z, G.mult s(w, z) = 0 :=
    Finset.sum_eq_zero fun w hw => Finset.sum_eq_zero fun z hz => by rw [Sym2.eq_swap]; exact hnb z hz w hw
  unfold cut
  rw [hZ, hW]
  simp only [Finset.sum_union hd1, Finset.sum_union hd2]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h0, h0', zero_add, zero_add,
    ← Finset.sum_union hdisj, hZW]

/-- The complement of a set has the same cut. -/
theorem cut_compl (G : UMultigraph V) {X : Finset V} (hX : X ⊆ G.verts) : cut G (G.verts \ X) = cut G X := by
  unfold cut
  rw [Finset.sdiff_sdiff_eq_self hX, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  rw [Sym2.eq_swap]

/-- **A side of a 2-edge-cut of a block is connected.** -/
theorem connOn_side {G : UMultigraph V} {j₁ j₂ : V} (hB : IsBlockU G j₁ j₂) {X : Finset V} (hX : X ⊆ G.verts)
    (hc : cut G X = 2) {y₀ : V} (hy₀ : y₀ ∈ G.verts \ X) : ConnOn G X := by
  apply connOn_of_closed
  intro Z hZ hne hcl
  by_contra hZX
  set W := X \ Z with hWdef
  have hWne : W.Nonempty := Finset.sdiff_nonempty.mpr fun h => hZX (Finset.Subset.antisymm hZ h)
  have hnb : ∀ z ∈ Z, ∀ w ∈ W, G.mult s(z, w) = 0 := by
    intro z hz w hw; by_contra hm
    exact (Finset.mem_sdiff.mp hw).2 (hcl z hz w (Finset.mem_sdiff.mp hw).1 hm)
  have hsplit := cut_split G hX (Finset.union_sdiff_of_subset hZ) Finset.disjoint_sdiff hnb
  rw [← hWdef] at hsplit
  have hpos : ∀ S ⊆ X, S.Nonempty → cut G S ≠ 0 := by
    intro S hS hSne h0
    have hall := eq_of_closed' hB.2.2.2.2.2.2 (hS.trans hX) hSne
      (fun a ha w hw hm => closed_of_cut_zero G h0 a ha w hw hm)
    have : y₀ ∈ S := by rw [hall]; exact (Finset.mem_sdiff.mp hy₀).1
    exact (Finset.mem_sdiff.mp hy₀).2 (hS this)
  obtain ⟨k, hk⟩ := hB.even_cut (hZ.trans hX)
  obtain ⟨k', hk'⟩ := hB.even_cut ((Finset.sdiff_subset).trans hX : W ⊆ G.verts)
  have h1 := hpos Z hZ hne
  have h2 := hpos W Finset.sdiff_subset hWne
  omega

/-- **The cut copies are the only crossing bonds**: for a 2-edge-cut `δ(X)` containing copies of `p–q` and
`p'–q'` (`p, p' ∈ X`), every crossing multiplicity is the number of these copies. -/
theorem cross_mult_eq {G : UMultigraph V} {X : Finset V} {p q p' q' : V} (hc : cut G X = 2)
    (hp : p ∈ X) (hp' : p' ∈ X) (hq : q ∈ G.verts \ X) (hq' : q' ∈ G.verts \ X)
    (hm : G.mult s(p, q) ≠ 0) (hm' : G.mult s(p', q') ≠ 0) (hsame : s(p, q) = s(p', q') → G.mult s(p, q) = 2) :
    ∀ x ∈ X, ∀ y ∈ G.verts \ X,
      G.mult s(x, y) = ({s(p, q), s(p', q')} : Multiset (Sym2 V)).count s(x, y) := by
  have hrow : ∀ {a b : V}, b ∈ G.verts \ X → ∀ x ∈ X,
      ∑ y ∈ G.verts \ X, (if s(x, y) = s(a, b) then 1 else 0) = if x = a then 1 else 0 := by
    intro a b hb x hx
    have hbX : b ∉ X := (Finset.mem_sdiff.mp hb).2
    by_cases hxa : x = a
    · subst hxa
      have : ∀ y, (s(x, y) = s(x, b)) ↔ y = b := fun y => Sym2.congr_right
      simp only [this, Finset.sum_ite_eq', hb, if_true]
    · have : ∀ y, ¬ (s(x, y) = s(a, b)) := by
        intro y h
        rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hxa h1
        · exact hbX (h1 ▸ hx)
      simp [this, hxa]
  have hle : ∀ x ∈ X, ∀ y ∈ G.verts \ X,
      ({s(p, q), s(p', q')} : Multiset (Sym2 V)).count s(x, y) ≤ G.mult s(x, y) := by
    intro x _ y _
    rw [count_pair]
    by_cases h1 : s(x, y) = s(p, q)
    · by_cases h2 : s(x, y) = s(p', q')
      · rw [if_pos h1, if_pos h2, h1, hsame (h1.symm.trans h2)]
      · rw [if_pos h1, if_neg h2, h1]; omega
    · by_cases h2 : s(x, y) = s(p', q')
      · rw [if_neg h1, if_pos h2, h2]; omega
      · rw [if_neg h1, if_neg h2]; omega
  have hsumg : ∑ x ∈ X, ∑ y ∈ G.verts \ X, ({s(p, q), s(p', q')} : Multiset (Sym2 V)).count s(x, y) = 2 := by
    simp only [count_pair, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun x hx => hrow hq x hx, Finset.sum_congr rfl fun x hx => hrow hq' x hx,
      Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos hp, if_pos hp']
  have hrowle : ∀ x ∈ X, ∑ y ∈ G.verts \ X, ({s(p, q), s(p', q')} : Multiset (Sym2 V)).count s(x, y) ≤
      ∑ y ∈ G.verts \ X, G.mult s(x, y) := fun x hx => Finset.sum_le_sum fun y hy => hle x hx y hy
  have heq := (Finset.sum_eq_sum_iff_of_le hrowle).mp (by rw [hsumg]; unfold cut at hc; exact hc.symm)
  intro x hx y hy
  exact (((Finset.sum_eq_sum_iff_of_le fun y hy => hle x hx y hy).mp (heq x hx)) y hy).symm

/-! ## The insertion data -/

/-- The data of a rung insertion at the 2-edge-cut `δ(X)` with crossing copies `p–q`, `p'–q'`, fresh `u ≠ v`. -/
structure InsData (G : UMultigraph V) (X : Finset V) (p q p' q' u v : V) : Prop where
  hX : X ⊆ G.verts
  hc : cut G X = 2
  hp : p ∈ X
  hp' : p' ∈ X
  hq : q ∈ G.verts \ X
  hq' : q' ∈ G.verts \ X
  hm : G.mult s(p, q) ≠ 0
  hm' : G.mult s(p', q') ≠ 0
  hsame : s(p, q) = s(p', q') → G.mult s(p, q) = 2
  hu : u ∉ G.verts
  hv : v ∉ G.verts
  huv : u ≠ v

namespace InsData

variable {G : UMultigraph V} {X : Finset V} {p q p' q' u v : V} (h : InsData G X p q p' q' u v)
include h

theorem pV : p ∈ G.verts := h.hX h.hp
theorem p'V : p' ∈ G.verts := h.hX h.hp'
theorem qV : q ∈ G.verts := (Finset.mem_sdiff.mp h.hq).1
theorem q'V : q' ∈ G.verts := (Finset.mem_sdiff.mp h.hq').1
theorem ne_u {x : V} (hx : x ∈ G.verts) : x ≠ u := fun e => h.hu (e ▸ hx)
theorem ne_v {x : V} (hx : x ∈ G.verts) : x ≠ v := fun e => h.hv (e ▸ hx)
theorem qX : q ∉ X := (Finset.mem_sdiff.mp h.hq).2
theorem q'X : q' ∉ X := (Finset.mem_sdiff.mp h.hq').2

theorem verts : (insertRung G p q p' q' u v).verts = insert u (insert v G.verts) := by
  show insert u (insert v (G.verts ∪ {p, q, p', q'})) = _
  rw [Finset.union_eq_left.mpr]
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  exacts [h.pV, h.qV, h.p'V, h.q'V]

theorem mem_verts {x : V} : x ∈ (insertRung G p q p' q' u v).verts ↔ x = u ∨ x = v ∨ x ∈ G.verts := by
  rw [h.verts]; simp only [Finset.mem_insert]

/-- The bonds at `u`: `u = v` (double) and `u–p`, `u–q`. -/
theorem mult_u (x : V) : (insertRung G p q p' q' u v).mult s(u, x) =
    2 * (if x = v then 1 else 0) + (if x = p then 1 else 0) + (if x = q then 1 else 0) := by
  rw [insertRung_mult, mult_eq_zero_of_left G h.hu, Nat.zero_sub, zero_add]
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  have e1 : (s(u, x) = s(p, u)) ↔ x = p := by rw [Sym2.eq_swap (a := p)]; exact Sym2.congr_right
  have e2 : (s(u, x) = s(u, q)) ↔ x = q := Sym2.congr_right
  have e3 : ¬ (s(u, x) = s(p', v)) := by
    intro e; rcases Sym2.eq_iff.mp e with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h.ne_u h.p'V h1.symm
    · exact h.huv h1
  have e4 : ¬ (s(u, x) = s(v, q')) := by
    intro e; rcases Sym2.eq_iff.mp e with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h.huv h1
    · exact h.ne_u h.q'V h1.symm
  have e5 : (s(u, x) = s(u, v)) ↔ x = v := Sym2.congr_right
  simp only [e1, e2, e3, e4, e5, if_false]
  split_ifs <;> omega

/-- The bonds at `v`: `v = u` (double) and `v–p'`, `v–q'`. -/
theorem mult_v (x : V) : (insertRung G p q p' q' u v).mult s(v, x) =
    2 * (if x = u then 1 else 0) + (if x = p' then 1 else 0) + (if x = q' then 1 else 0) := by
  rw [insertRung_mult, mult_eq_zero_of_left G h.hv, Nat.zero_sub, zero_add]
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  have e1 : ¬ (s(v, x) = s(p, u)) := by
    intro e; rcases Sym2.eq_iff.mp e with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h.ne_v h.pV h1.symm
    · exact h.huv h1.symm
  have e2 : ¬ (s(v, x) = s(u, q)) := by
    intro e; rcases Sym2.eq_iff.mp e with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h.huv h1.symm
    · exact h.ne_v h.qV h1.symm
  have e3 : (s(v, x) = s(p', v)) ↔ x = p' := by rw [Sym2.eq_swap (a := p')]; exact Sym2.congr_right
  have e4 : (s(v, x) = s(v, q')) ↔ x = q' := Sym2.congr_right
  have e5 : (s(v, x) = s(u, v)) ↔ x = u := by rw [Sym2.eq_swap (a := u)]; exact Sym2.congr_right
  simp only [e1, e2, e3, e4, e5, if_false]
  split_ifs <;> omega

/-- Away from `u, v`, the insertion only removes the cut copies. -/
theorem mult_old {x y : V} (hxu : x ≠ u) (hxv : x ≠ v) (hyu : y ≠ u) (hyv : y ≠ v) :
    (insertRung G p q p' q' u v).mult s(x, y) =
      G.mult s(x, y) - ({s(p, q), s(p', q')} : Multiset (Sym2 V)).count s(x, y) := by
  have key : ∀ e : Sym2 V, (u ∈ e ∨ v ∈ e) → s(x, y) ≠ e := by
    rintro e (he | he) rfl
    · rcases Sym2.mem_iff.mp he with h' | h'
      exacts [hxu h'.symm, hyu h'.symm]
    · rcases Sym2.mem_iff.mp he with h' | h'
      exacts [hxv h'.symm, hyv h'.symm]
  have hnot : s(x, y) ∉ ({s(p, u), s(u, q), s(p', v), s(v, q'), s(u, v), s(u, v)} : Multiset (Sym2 V)) := by
    intro hmem
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
    rcases hmem with h' | h' | h' | h' | h' | h'
    · exact key _ (Or.inl (Sym2.mem_mk_right p u)) h'
    · exact key _ (Or.inl (Sym2.mem_mk_left u q)) h'
    · exact key _ (Or.inr (Sym2.mem_mk_right p' v)) h'
    · exact key _ (Or.inr (Sym2.mem_mk_left v q')) h'
    · exact key _ (Or.inl (Sym2.mem_mk_left u v)) h'
    · exact key _ (Or.inl (Sym2.mem_mk_left u v)) h'
  rw [insertRung_mult, Multiset.count_eq_zero.mpr hnot, add_zero]

/-- The cut copies number at most the multiplicity. -/
theorem count_cut_le (x y : V) :
    ({s(p, q), s(p', q')} : Multiset (Sym2 V)).count s(x, y) ≤ G.mult s(x, y) := by
  rw [count_pair]
  by_cases h1 : s(x, y) = s(p, q)
  · by_cases h2 : s(x, y) = s(p', q')
    · rw [if_pos h1, if_pos h2, h1, h.hsame (h1.symm.trans h2)]
    · rw [if_pos h1, if_neg h2, h1]; have := h.hm; omega
  · by_cases h2 : s(x, y) = s(p', q')
    · rw [if_neg h1, if_pos h2, h2]; have := h.hm'; omega
    · rw [if_neg h1, if_neg h2]; omega

/-- Inside a side the insertion changes nothing. -/
theorem mult_side {x y : V} (hxy : (x ∈ X ∧ y ∈ X) ∨ (x ∈ G.verts \ X ∧ y ∈ G.verts \ X)) :
    (insertRung G p q p' q' u v).mult s(x, y) = G.mult s(x, y) := by
  have hxV : x ∈ G.verts := by rcases hxy with ⟨h1, _⟩ | ⟨h1, _⟩; exacts [h.hX h1, (Finset.mem_sdiff.mp h1).1]
  have hyV : y ∈ G.verts := by rcases hxy with ⟨_, h1⟩ | ⟨_, h1⟩; exacts [h.hX h1, (Finset.mem_sdiff.mp h1).1]
  rw [h.mult_old (h.ne_u hxV) (h.ne_v hxV) (h.ne_u hyV) (h.ne_v hyV), count_pair]
  have hcross : ∀ {a b : V}, a ∈ X → b ∈ G.verts \ X → s(x, y) ≠ s(a, b) := by
    intro a b ha hb e
    have hbX := (Finset.mem_sdiff.mp hb).2
    rcases Sym2.eq_iff.mp e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact hbX (h2 ▸ hy)
    · exact (Finset.mem_sdiff.mp hx).2 (h1 ▸ ha)
    · exact hbX (h1 ▸ hx)
    · exact (Finset.mem_sdiff.mp hy).2 (h2 ▸ ha)
  rw [if_neg (hcross h.hp h.hq), if_neg (hcross h.hp' h.hq')]
  rfl

/-- Between the sides only the new rails remain: no bond. -/
theorem mult_cross {x y : V} (hx : x ∈ X) (hy : y ∈ G.verts \ X) :
    (insertRung G p q p' q' u v).mult s(x, y) = 0 := by
  have hxV := h.hX hx
  have hyV := (Finset.mem_sdiff.mp hy).1
  rw [h.mult_old (h.ne_u hxV) (h.ne_v hxV) (h.ne_u hyV) (h.ne_v hyV),
    cross_mult_eq h.hc h.hp h.hp' h.hq h.hq' h.hm h.hm' h.hsame x hx y hy, Nat.sub_self]

theorem lift_side {K : Finset V} (hK : (K ⊆ X) ∨ (K ⊆ G.verts \ X)) (hc : ConnOn G K) :
    ConnOn (insertRung G p q p' q' u v) K := by
  intro a ha b hb
  refine Relation.ReflTransGen.mono (fun x y hxy => ?_) a b (hc a ha b hb)
  obtain ⟨hx, hy, hm⟩ := hxy
  refine ⟨hx, hy, ?_⟩
  rw [h.mult_side (by rcases hK with hK | hK; exacts [Or.inl ⟨hK hx, hK hy⟩, Or.inr ⟨hK hx, hK hy⟩])]
  exact hm

/-- **The new rung is a 2-cut rung** with poles `X` and `G.verts \ X`. -/
theorem isRungAt {j₁ j₂ : V} (hB : IsBlockU G j₁ j₂) :
    IsRungAt (insertRung G p q p' q' u v) u v p q p' q' X (G.verts \ X) where
  ne := h.huv
  a_mem := h.mem_verts.mpr (Or.inl rfl)
  b_mem := h.mem_verts.mpr (Or.inr (Or.inl rfl))
  mult_ab := by rw [h.mult_u]; simp [h.ne_v h.pV, h.ne_v h.qV, Ne.symm (h.ne_v h.pV), Ne.symm (h.ne_v h.qV)]
  disj := Finset.disjoint_sdiff
  union := by
    rw [Finset.union_sdiff_of_subset h.hX, h.verts,
      Finset.erase_insert (by simp [h.huv, h.hu]), Finset.erase_insert h.hv]
  connm := h.lift_side (Or.inl le_rfl) (connOn_side hB h.hX h.hc h.hq)
  connp := h.lift_side (Or.inr le_rfl)
    (connOn_side hB Finset.sdiff_subset (by rw [cut_compl G h.hX]; exact h.hc)
      (Finset.mem_sdiff.mpr ⟨h.pV, fun hh => (Finset.mem_sdiff.mp hh).2 h.hp⟩))
  noBond x hx y hy := h.mult_cross hx hy
  xm_mem := h.hp
  xp_mem := h.hq
  ym_mem := h.hp'
  yp_mem := h.hq'
  a_xm := by
    rw [h.mult_u]
    have : p ≠ q := fun e => h.qX (e ▸ h.hp)
    simp [h.ne_v h.pV, this]
  a_xp := by
    rw [h.mult_u]
    have : q ≠ p := fun e => h.qX (e ▸ h.hp)
    simp [h.ne_v h.qV, this]
  b_ym := by
    rw [h.mult_v]
    have : p' ≠ q' := fun e => h.q'X (e ▸ h.hp')
    simp [h.ne_u h.p'V, this]
  b_yp := by
    rw [h.mult_v]
    have : q' ≠ p' := fun e => h.q'X (e ▸ h.hp')
    simp [h.ne_u h.q'V, this]
  a_other z h1 h2 h3 := by rw [h.mult_u]; simp [h1, h2, h3]
  b_other z h1 h2 h3 := by rw [h.mult_v]; simp [h1, h2, h3]

/-- **The crossed deletion undoes the insertion.** -/
theorem rungDel_eq {j₁ j₂ : V} (hB : IsBlockU G j₁ j₂) :
    rungDel (insertRung G p q p' q' u v) u v p q p' q' false = G := by
  have hRc := (h.isRungAt hB).toCore
  apply ext
  · rw [hRc.verts_rungDel, h.verts, Finset.erase_insert (by simp [h.huv, h.hu]), Finset.erase_insert h.hv]
  · intro e
    induction e using Sym2.ind with
    | h x y =>
      rw [rungDel_mult]
      show _ = G.mult s(x, y)
      by_cases huv : u ∈ s(x, y) ∨ v ∈ s(x, y)
      · rw [if_pos huv]
        rcases huv with h1 | h1 <;> rcases Sym2.mem_iff.mp h1 with h2 | h2
        · rw [← h2, mult_eq_zero_of_left G h.hu]
        · rw [← h2, mult_eq_zero_of_right G h.hu]
        · rw [← h2, mult_eq_zero_of_left G h.hv]
        · rw [← h2, mult_eq_zero_of_right G h.hv]
      · rw [if_neg huv]
        have hxu : x ≠ u := fun e => huv (Or.inl (e ▸ Sym2.mem_mk_left x y))
        have hyu : y ≠ u := fun e => huv (Or.inl (e ▸ Sym2.mem_mk_right x y))
        have hxv : x ≠ v := fun e => huv (Or.inr (e ▸ Sym2.mem_mk_left x y))
        have hyv : y ≠ v := fun e => huv (Or.inr (e ▸ Sym2.mem_mk_right x y))
        rw [h.mult_old hxu hxv hyu hyv]
        show _ + ({s(p, q), s(p', q')} : Multiset (Sym2 V)).count s(x, y) = _
        have := h.count_cut_le x y
        omega

/-- The inserted graph is loopless if `G` is. -/
theorem loopless (hl : G.Loopless) : (insertRung G p q p' q' u v).Loopless := by
  intro w
  by_cases hwu : w = u
  · rw [hwu, h.mult_u]; simp [h.huv, Ne.symm (h.ne_u h.pV), Ne.symm (h.ne_u h.qV)]
  by_cases hwv : w = v
  · rw [hwv, h.mult_v]; simp [Ne.symm h.huv, Ne.symm (h.ne_v h.p'V), Ne.symm (h.ne_v h.q'V)]
  rw [h.mult_old hwu hwv hwu hwv, hl w, Nat.zero_sub]

/-- Multiplicities of the inserted graph are at most `2` if those of `G` are. -/
theorem mult_le_two (hm2 : ∀ x ∈ G.verts, ∀ y ∈ G.verts, x ≠ y → G.mult s(x, y) ≤ 2) :
    ∀ x ∈ (insertRung G p q p' q' u v).verts, ∀ y ∈ (insertRung G p q p' q' u v).verts, x ≠ y →
      (insertRung G p q p' q' u v).mult s(x, y) ≤ 2 := by
  have hu2 : ∀ y, y ≠ u → (insertRung G p q p' q' u v).mult s(u, y) ≤ 2 := by
    intro y _
    rw [h.mult_u]
    have hpq : p ≠ q := fun e => h.qX (e ▸ h.hp)
    by_cases hyv : y = v
    · subst hyv; simp [h.ne_v h.pV, h.ne_v h.qV, Ne.symm (h.ne_v h.pV), Ne.symm (h.ne_v h.qV)]
    · split_ifs <;> simp_all
  have hv2 : ∀ y, y ≠ v → (insertRung G p q p' q' u v).mult s(v, y) ≤ 2 := by
    intro y _
    rw [h.mult_v]
    have hpq : p' ≠ q' := fun e => h.q'X (e ▸ h.hp')
    by_cases hyu : y = u
    · subst hyu; simp [h.ne_u h.p'V, h.ne_u h.q'V, Ne.symm (h.ne_u h.p'V), Ne.symm (h.ne_u h.q'V)]
    · split_ifs <;> simp_all
  intro x hx y hy hxy
  by_cases hxu : x = u
  · rw [hxu]; exact hu2 y (fun e => hxy (hxu.trans e.symm))
  by_cases hyu : y = u
  · rw [hyu, Sym2.eq_swap]; exact hu2 x hxu
  by_cases hxv : x = v
  · rw [hxv]; exact hv2 y (fun e => hxy (hxv.trans e.symm))
  by_cases hyv : y = v
  · rw [hyv, Sym2.eq_swap]; exact hv2 x hxv
  have hxV : x ∈ G.verts := by rcases h.mem_verts.mp hx with h1 | h1 | h1 <;> tauto
  have hyV : y ∈ G.verts := by rcases h.mem_verts.mp hy with h1 | h1 | h1 <;> tauto
  rw [h.mult_old hxu hxv hyu hyv]
  have := hm2 x hxV y hyV hxy
  omega

end InsData

end WaveTurbulence.TVine.Core
