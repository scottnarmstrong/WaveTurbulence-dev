/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Regular

/-!
# Smoothing invariants and cut arithmetic

* `deg_smooth`, `connected_smooth`, `loopless_y2Move`;
* `cut_smooth`: `cut (smooth G j n n') K + 2·[n, n' ∈ K] = cut G K` for `j ∉ K`;
* `cut_insert`: `cut (insert j K) + 2·Σ_{u ∈ K} mult(j, u) = cut K + deg j` (no loop at `j`);
* `closed_of_cut_zero`, `cut_ge_term`;
* `doubledTriangle_cut_ne_two`: no atom set of a doubled triangle has exactly two leaving bonds.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

theorem count_pair_v (e x y : V) :
    ({x, y} : Multiset V).count e = (if e = x then 1 else 0) + (if e = y then 1 else 0) := by
  rw [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, add_comm]

theorem nbrs_ne_of_loop {G : UMultigraph V} {j n n' : V} (hl : G.mult s(j, j) = 0) (hnb : nbrs G j = {n, n'}) :
    n ≠ j ∧ n' ≠ j := by
  have := not_mem_nbrs_of_loop hl
  rw [hnb] at this
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or] at this
  exact ⟨Ne.symm this.1, Ne.symm this.2⟩

theorem mem_verts_of_nbrs {G : UMultigraph V} {j n n' : V} (hnb : nbrs G j = {n, n'}) : j ∈ G.verts := by
  have hl' : 0 < ({n, n'} : Multiset V).count n := by rw [count_pair_self]; omega
  by_cases hnj : n = j
  · subst hnj; exact (nbrs_mem_verts hnb).1
  · rw [← mult_of_nbrs_eq hnb hnj] at hl'
    exact G.supp _ (by omega) j (Sym2.mem_mk_left j n)

/-- Smoothing keeps the degrees of the other atoms. -/
theorem deg_smooth {G : UMultigraph V} {j n n' : V} (hl : G.mult s(j, j) = 0) (hnb : nbrs G j = {n, n'})
    {v : V} (hvj : v ≠ j) : deg (smooth G j n n') v = deg G v := by
  obtain ⟨hnj, hn'j⟩ := nbrs_ne_of_loop hl hnb
  have hnV := nbrs_mem_verts hnb
  have hjV := mem_verts_of_nbrs hnb
  set S := G.verts.erase j with hS
  have hnS : n ∈ S := Finset.mem_erase.mpr ⟨hnj, hnV.1⟩
  have hn'S : n' ∈ S := Finset.mem_erase.mpr ⟨hn'j, hnV.2⟩
  have hm : ∀ w, w ≠ j →
      (smooth G j n n').mult s(v, w) = G.mult s(v, w) + (if s(v, w) = s(n, n') then 1 else 0) :=
    fun w hw => by rw [smooth_mult_at G hvj, if_neg hw]
  have hind : ∑ w ∈ S, (if s(v, w) = s(n, n') then 1 else 0) + (if s(v, v) = s(n, n') then 1 else 0) =
      ({n, n'} : Multiset V).count v := by
    by_cases hnn : n = n'
    · subst hnn
      have hiff : ∀ w, (s(v, w) = s(n, n)) ↔ (v = n ∧ w = n) := by
        intro w; rw [Sym2.eq_iff]; tauto
      simp only [hiff]
      by_cases hvn : v = n
      · subst hvn
        simp only [true_and, and_self, if_true]
        rw [Finset.sum_ite_eq' S v, if_pos hnS, count_pair_self, if_pos rfl]
      · simp [hvn, count_pair_of_ne hvn]
    · rw [sum_ind_sym2 hnn hnS hn'S]
      have hloop : ¬ (s(v, v) = s(n, n')) := by
        intro h; rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hnn (h1.symm.trans h2)
        · exact hnn (h2.symm.trans h1)
      rw [if_neg hloop, add_zero]
      by_cases hvn : v = n
      · subst hvn; rw [count_pair_self, if_pos rfl]
      · rw [count_pair_of_ne hvn, if_neg hvn, zero_add]
  unfold deg
  rw [smooth_verts hnV.1 hnV.2, ← hS,
    Finset.sum_congr rfl fun w hw => hm w (Finset.ne_of_mem_erase hw), Finset.sum_add_distrib, hm v hvj,
    ← Finset.add_sum_erase _ _ hjV, ← hS, Sym2.eq_swap (a := v) (b := j), mult_of_nbrs_eq hnb hvj, ← hind]
  ring

theorem loopless_y2Move {H : UMultigraph V} {a b c d : V} (hP : IsY2Pair H a b c d) (hl : H.Loopless) :
    (y2Move H a b c d).Loopless := by
  intro v
  rw [y2Move_mult, hl, zero_add]
  split_ifs with h1 h2
  · rfl
  · exfalso; rcases Sym2.eq_iff.mp h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact hP.ext_ne (h3.symm.trans h4)
    · exact hP.ext_ne (h4.symm.trans h3)
  · rfl

/-- Smoothing keeps connectivity. -/
theorem connected_smooth {G : UMultigraph V} {j n n' : V} (hl : G.mult s(j, j) = 0) (hnb : nbrs G j = {n, n'})
    (hc : Connected G) : Connected (smooth G j n n') := by
  classical
  obtain ⟨hnj, hn'j⟩ := nbrs_ne_of_loop hl hnb
  have hnV := nbrs_mem_verts hnb
  have hjV := mem_verts_of_nbrs hnb
  apply connected_of_closed
  intro X hX hne hcl
  rw [smooth_verts hnV.1 hnV.2] at hX hcl ⊢
  have hXj : ∀ x ∈ X, x ≠ j := fun x hx => Finset.ne_of_mem_erase (hX hx)
  have hle : ∀ u w, u ≠ j → w ≠ j → G.mult s(u, w) ≤ (smooth G j n n').mult s(u, w) := by
    intro u w hu hw; rw [smooth_mult_at G hu, if_neg hw]; omega
  have hnn' : (smooth G j n n').mult s(n, n') ≠ 0 := by
    rw [smooth_mult_at G hnj, if_neg hn'j, if_pos rfl]; omega
  have hnX : n ∈ X ↔ n' ∈ X := by
    constructor
    · intro h; exact hcl n h n' (Finset.mem_erase.mpr ⟨hn'j, hnV.2⟩) hnn'
    · intro h; exact hcl n' h n (Finset.mem_erase.mpr ⟨hnj, hnV.1⟩) (by rw [Sym2.eq_swap]; exact hnn')
  set Y := if n ∈ X then insert j X else X with hY
  have hXY : X ⊆ Y := by rw [hY]; split_ifs <;> intro x hx <;> simp [hx]
  have hYV : Y ⊆ G.verts := by
    intro x hx; rw [hY] at hx; split_ifs at hx
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hjV
      · exact Finset.mem_of_mem_erase (hX hx)
    · exact Finset.mem_of_mem_erase (hX hx)
  have hYc : ∀ u ∈ Y, ∀ w ∈ G.verts, G.mult s(u, w) ≠ 0 → w ∈ Y := by
    intro u hu w hw hm
    by_cases huj : u = j
    · subst huj
      have hw' : w ≠ u := by rintro rfl; exact hm hl
      rw [mult_of_nbrs_eq hnb hw'] at hm
      have hnX' : n ∈ X := by
        by_contra h; rw [hY, if_neg h] at hu; exact hXj u hu rfl
      rcases pair_count_pos (Nat.pos_of_ne_zero hm) with rfl | rfl
      · exact hXY hnX'
      · exact hXY (hnX.mp hnX')
    · have huX : u ∈ X := by
        rw [hY] at hu; split_ifs at hu
        · rcases Finset.mem_insert.mp hu with h | h
          · exact absurd h huj
          · exact h
        · exact hu
      by_cases hwj : w = j
      · subst hwj
        rw [Sym2.eq_swap, mult_of_nbrs_eq hnb huj] at hm
        have : n ∈ X := by
          rcases pair_count_pos (Nat.pos_of_ne_zero hm) with h | h
          · exact h ▸ huX
          · exact hnX.mpr (h ▸ huX)
        rw [hY, if_pos this]; simp
      · exact hXY (hcl u huX w (Finset.mem_erase.mpr ⟨hwj, hw⟩) (by have := hle u w huj hwj; omega))
  obtain ⟨x₀, hx₀⟩ := hne
  have hYall : Y = G.verts := eq_of_closed' hc hYV ⟨x₀, hXY hx₀⟩ hYc
  apply Finset.Subset.antisymm hX
  intro v hv
  have hvj := Finset.ne_of_mem_erase hv
  have : v ∈ Y := by rw [hYall]; exact Finset.mem_of_mem_erase hv
  rw [hY] at this; split_ifs at this
  · rcases Finset.mem_insert.mp this with h | h
    · exact absurd h hvj
    · exact h
  · exact this

/-! ## Cut arithmetic -/

theorem cut_ge_term (G : UMultigraph V) {X : Finset V} {u w : V} (hu : u ∈ X) (hw : w ∈ G.verts)
    (hwX : w ∉ X) : G.mult s(u, w) ≤ cut G X := by
  unfold cut
  have h1 : G.mult s(u, w) ≤ ∑ w' ∈ G.verts \ X, G.mult s(u, w') :=
    Finset.single_le_sum (f := fun w' => G.mult s(u, w')) (fun _ _ => Nat.zero_le _)
      (Finset.mem_sdiff.mpr ⟨hw, hwX⟩)
  exact h1.trans (Finset.single_le_sum (f := fun u' => ∑ w' ∈ G.verts \ X, G.mult s(u', w'))
    (fun _ _ => Nat.zero_le _) hu)

theorem closed_of_cut_zero (G : UMultigraph V) {X : Finset V} (h : cut G X = 0) :
    ∀ u ∈ X, ∀ w ∈ G.verts, G.mult s(u, w) ≠ 0 → w ∈ X := by
  intro u hu w hw hm
  by_contra hwX
  have := cut_ge_term G hu hw hwX
  omega

/-- Adding an atom to a set. -/
theorem cut_insert (G : UMultigraph V) {K : Finset V} {j : V} (hjK : j ∉ K) (hjV : j ∈ G.verts)
    (hKV : K ⊆ G.verts) (hl : G.mult s(j, j) = 0) :
    cut G (insert j K) + 2 * ∑ u ∈ K, G.mult s(j, u) = cut G K + deg G j := by
  set W := G.verts \ insert j K with hW
  have hsd : G.verts \ K = insert j W := by
    ext x; simp only [hW, Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hxK⟩; by_cases hxj : x = j
      · exact Or.inl hxj
      · exact Or.inr ⟨hx, fun h => h.elim hxj hxK⟩
    · rintro (rfl | ⟨hx, hxK⟩)
      · exact ⟨hjV, hjK⟩
      · exact ⟨hx, fun h => hxK (Or.inr h)⟩
  have hjW : j ∉ W := by simp [hW]
  have hdeg : deg G j = ∑ u ∈ K, G.mult s(j, u) + ∑ w ∈ W, G.mult s(j, w) := by
    unfold deg
    rw [hl, add_zero]
    have : G.verts = K ∪ insert j W := by rw [← hsd, Finset.union_sdiff_of_subset hKV]
    rw [this, Finset.sum_union (by
      rw [Finset.disjoint_left]; intro x hxK hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hjK hxK
      · exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_insert_of_mem hxK)), Finset.sum_insert hjW, hl]
    ring
  unfold cut
  rw [Finset.sum_insert hjK, hsd, ← hW]
  simp only [Finset.sum_insert hjW, Finset.sum_add_distrib]
  rw [hdeg]
  have hsym : ∑ u ∈ K, G.mult s(u, j) = ∑ u ∈ K, G.mult s(j, u) :=
    Finset.sum_congr rfl fun u _ => by rw [Sym2.eq_swap]
  rw [hsym]
  ring

/-- Smoothing `j ∉ K` changes `cut K` only when both neighbours of `j` lie in `K`. -/
theorem cut_smooth {G : UMultigraph V} {j n n' : V} (hl : G.mult s(j, j) = 0) (hnb : nbrs G j = {n, n'})
    {K : Finset V} (hjK : j ∉ K) (hKV : K ⊆ G.verts) :
    cut (smooth G j n n') K + 2 * (if n ∈ K ∧ n' ∈ K then 1 else 0) = cut G K := by
  obtain ⟨hnj, hn'j⟩ := nbrs_ne_of_loop hl hnb
  have hnV := nbrs_mem_verts hnb
  have hjV := mem_verts_of_nbrs hnb
  set S := G.verts.erase j with hS
  set W := S \ K with hW
  have hsd : G.verts \ K = insert j W := by
    ext x; simp only [hW, hS, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hx, hxK⟩; by_cases hxj : x = j
      · exact Or.inl hxj
      · exact Or.inr ⟨⟨hxj, hx⟩, hxK⟩
    · rintro (rfl | ⟨⟨_, hx⟩, hxK⟩)
      · exact ⟨hjV, hjK⟩
      · exact ⟨hx, hxK⟩
  have hjW : j ∉ W := by simp [hW, hS]
  have hKj : ∀ u ∈ K, u ≠ j := fun u hu h => hjK (h ▸ hu)
  -- `G`-side
  have hG : cut G K = ∑ u ∈ K, ∑ w ∈ W, G.mult s(u, w) + ∑ u ∈ K, G.mult s(u, j) := by
    unfold cut
    rw [hsd, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.sum_insert hjW, add_comm]
  have hjrow : ∑ u ∈ K, G.mult s(u, j) = (if n ∈ K then 1 else 0) + (if n' ∈ K then 1 else 0) := by
    rw [Finset.sum_congr rfl fun u hu => by rw [Sym2.eq_swap, mult_of_nbrs_eq hnb (hKj u hu)]]
    simp only [count_pair_v, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  -- smoothed side
  have hS' : cut (smooth G j n n') K = ∑ u ∈ K, ∑ w ∈ W, (G.mult s(u, w) + (if s(u, w) = s(n, n') then 1 else 0)) := by
    unfold cut
    rw [smooth_verts hnV.1 hnV.2, ← hS, ← hW]
    apply Finset.sum_congr rfl; intro u hu
    apply Finset.sum_congr rfl; intro w hw
    rw [smooth_mult_at G (hKj u hu), if_neg (Finset.ne_of_mem_erase (Finset.mem_sdiff.mp hw).1)]
  have hnS : n ∈ S := Finset.mem_erase.mpr ⟨hnj, hnV.1⟩
  have hn'S : n' ∈ S := Finset.mem_erase.mpr ⟨hn'j, hnV.2⟩
  have hind : ∑ u ∈ K, ∑ w ∈ W, (if s(u, w) = s(n, n') then 1 else 0) =
      (if n ∈ K ∧ n' ∉ K then 1 else 0) + (if n' ∈ K ∧ n ∉ K then 1 else 0) := by
    by_cases hnn : n = n'
    · subst hnn
      have hzero : ∑ u ∈ K, ∑ w ∈ W, (if s(u, w) = s(n, n) then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero; intro u hu
        apply Finset.sum_eq_zero; intro w hw
        rw [if_neg]
        intro h
        have hun : u = n ∧ w = n := by rcases Sym2.eq_iff.mp h with h' | h' <;> exact h'
        exact (Finset.mem_sdiff.mp hw).2 (by rw [hun.2, ← hun.1]; exact hu)
      rw [hzero]; simp
    · have hrow : ∀ u, ∑ w ∈ W, (if s(u, w) = s(n, n') then 1 else 0) =
          (if u = n ∧ n' ∈ W then 1 else 0) + (if u = n' ∧ n ∈ W then 1 else 0) := by
        intro u
        by_cases hun : u = n
        · subst hun
          have : ∀ w, (s(u, w) = s(u, n')) ↔ w = n' := fun w => Sym2.congr_right
          simp only [this, Finset.sum_ite_eq', hnn, false_and, if_false, add_zero, true_and]
        · by_cases hun' : u = n'
          · subst hun'
            have : ∀ w, (s(u, w) = s(n, u)) ↔ w = n := fun w => by rw [Sym2.eq_swap (a := n), Sym2.congr_right]
            simp only [this, Finset.sum_ite_eq', hun, false_and, if_false, zero_add, true_and]
          · have : ∀ w, ¬ (s(u, w) = s(n, n')) := fun w h => by
              rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
              exacts [hun h1, hun' h1]
            simp [this, hun, hun']
      rw [Finset.sum_congr rfl fun u _ => hrow u, Finset.sum_add_distrib]
      have e1 : ∑ u ∈ K, (if u = n ∧ n' ∈ W then 1 else 0) = if n ∈ K ∧ n' ∉ K then 1 else 0 := by
        by_cases h : n' ∈ W
        · have : n' ∉ K := (Finset.mem_sdiff.mp h).2
          simp only [h, and_true, this, not_false_eq_true]; rw [Finset.sum_ite_eq']
        · have : ¬ (n' ∉ K) := fun h' => h (Finset.mem_sdiff.mpr ⟨hn'S, h'⟩)
          simp [h, this]
      have e2 : ∑ u ∈ K, (if u = n' ∧ n ∈ W then 1 else 0) = if n' ∈ K ∧ n ∉ K then 1 else 0 := by
        by_cases h : n ∈ W
        · have : n ∉ K := (Finset.mem_sdiff.mp h).2
          simp only [h, and_true, this, not_false_eq_true]; rw [Finset.sum_ite_eq']
        · have : ¬ (n ∉ K) := fun h' => h (Finset.mem_sdiff.mpr ⟨hnS, h'⟩)
          simp [h, this]
      rw [e1, e2]
  rw [hS', hG, hjrow]
  simp only [Finset.sum_add_distrib]
  rw [hind]
  by_cases h1 : n ∈ K <;> by_cases h2 : n' ∈ K <;> simp [h1, h2] <;> ring

end WaveTurbulence.TVine.Core
