/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.ContainerJoints

/-!
# Degrees, connectivity and cuts along (Y2) moves and joint smoothings

* `connOn_of_closed`, `connected_of_closed`: connectivity from closed sets;
* `deg_y2Move`, `connected_y2Move`: a (Y2) move keeps the degrees of the surviving atoms and connectivity;
* `deg_smooth`, `connected_smooth`: smoothing a degree-2 atom keeps the other degrees and connectivity;
* `cut_smooth`: smoothing `j ∉ K` lowers `cut K` by `2` iff both neighbours of `j` lie in `K`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

/-! ## Connectivity from closed sets -/

theorem connOn_of_closed {H : UMultigraph V} {K : Finset V}
    (h : ∀ X ⊆ K, X.Nonempty → (∀ u ∈ X, ∀ w ∈ K, H.mult s(u, w) ≠ 0 → w ∈ X) → X = K) : ConnOn H K := by
  classical
  intro u hu w hw
  set X := K.filter fun v => Relation.ReflTransGen (AdjIn H K) u v with hXdef
  have hX : X = K := h X (Finset.filter_subset _ _) ⟨u, Finset.mem_filter.mpr ⟨hu, .refl⟩⟩ (by
    intro x hx y hy hm
    obtain ⟨hxK, hxr⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hy, hxr.tail ⟨hxK, hy, hm⟩⟩)
  have hwX : w ∈ X := by rw [hX]; exact hw
  exact (Finset.mem_filter.mp hwX).2

theorem connected_of_closed {H : UMultigraph V}
    (h : ∀ X ⊆ H.verts, X.Nonempty → (∀ u ∈ X, ∀ w ∈ H.verts, H.mult s(u, w) ≠ 0 → w ∈ X) → X = H.verts) :
    Connected H := connOn_of_closed h

/-! ## (Y2) moves -/

theorem deg_y2Move {H : UMultigraph V} {a b c d : V} (hP : IsY2Pair H a b c d) {v : V} (hva : v ≠ a)
    (hvb : v ≠ b) : deg (y2Move H a b c d) v = deg H v := by
  set S := (H.verts.erase a).erase b with hS
  have hcS : c ∈ S := by simp [hS, hP.c_ne_a, hP.c_ne_b, hP.c_mem]
  have hdS : d ∈ S := by simp [hS, hP.d_ne_a, hP.d_ne_b, hP.d_mem]
  have hm : ∀ w, w ≠ a → w ≠ b →
      (y2Move H a b c d).mult s(v, w) = H.mult s(v, w) + (if s(v, w) = s(c, d) then 1 else 0) := by
    intro w hwa hwb
    rw [y2Move_mult, if_neg (mt (mem_pair_iff hva hvb).mp (by tauto))]
  unfold deg
  rw [y2Move_verts hP, ← hS,
    Finset.sum_congr rfl fun w hw => hm w (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hw))
      (Finset.ne_of_mem_erase hw),
    Finset.sum_add_distrib, sum_ind_sym2 hP.ext_ne hcS hdS, hm v hva hvb]
  have hloop : ¬ (s(v, v) = s(c, d)) := by
    intro h; rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hP.ext_ne (h1.symm.trans h2)
    · exact hP.ext_ne (h2.symm.trans h1)
  rw [if_neg hloop]
  have hbV : b ∈ H.verts.erase a := Finset.mem_erase.mpr ⟨hP.ne.symm, hP.b_mem⟩
  rw [← Finset.add_sum_erase _ _ hP.a_mem, ← Finset.add_sum_erase _ _ hbV, ← hS]
  have ha : H.mult s(v, a) = if v = c then 1 else 0 := by
    rw [Sym2.eq_swap, hP.mult_a, if_neg hvb]
  have hb : H.mult s(v, b) = if v = d then 1 else 0 := by
    rw [Sym2.eq_swap, hP.mult_b, if_neg hva]
  rw [ha, hb]
  ring

theorem connected_y2Move {H : UMultigraph V} {a b c d : V} (hP : IsY2Pair H a b c d) (hc : Connected H) :
    Connected (y2Move H a b c d) := by
  classical
  apply connected_of_closed
  intro X hX hne hcl
  rw [y2Move_verts hP] at hX hcl ⊢
  have hXab : ∀ x ∈ X, x ≠ a ∧ x ≠ b := fun x hx => by
    have := hX hx; simp only [Finset.mem_erase] at this; exact ⟨this.2.1, this.1⟩
  have hnew : ∀ u w, u ≠ a → u ≠ b → w ≠ a → w ≠ b →
      H.mult s(u, w) ≤ (y2Move H a b c d).mult s(u, w) := by
    intro u w hua hub hwa hwb
    rw [y2Move_mult, if_neg (by rintro (h | h) <;> rcases Sym2.mem_iff.mp h with h | h <;> tauto)]
    omega
  have hcdab : ¬ (a ∈ s(c, d) ∨ b ∈ s(c, d)) := by
    rintro (h | h) <;> rcases Sym2.mem_iff.mp h with h | h
    · exact hP.c_ne_a h.symm
    · exact hP.d_ne_a h.symm
    · exact hP.c_ne_b h.symm
    · exact hP.d_ne_b h.symm
  have hcd : (y2Move H a b c d).mult s(c, d) ≠ 0 := by
    rw [y2Move_mult, if_neg hcdab, if_pos rfl]
    omega
  have hcV : c ∈ (H.verts.erase a).erase b := by simp [hP.c_ne_a, hP.c_ne_b, hP.c_mem]
  have hdV : d ∈ (H.verts.erase a).erase b := by simp [hP.d_ne_a, hP.d_ne_b, hP.d_mem]
  have hcdX : c ∈ X ↔ d ∈ X := by
    constructor
    · intro h; exact hcl c h d hdV hcd
    · intro h; exact hcl d h c hcV (by rw [Sym2.eq_swap]; exact hcd)
  set Y := if c ∈ X then insert a (insert b X) else X with hY
  have hYV : Y ⊆ H.verts := by
    intro x hx
    rw [hY] at hx
    split_ifs at hx
    · simp only [Finset.mem_insert] at hx
      rcases hx with rfl | rfl | hx
      · exact hP.a_mem
      · exact hP.b_mem
      · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hX hx))
    · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hX hx))
  have hXY : X ⊆ Y := by rw [hY]; split_ifs <;> intro x hx <;> simp [hx]
  have hYc : ∀ u ∈ Y, ∀ w ∈ H.verts, H.mult s(u, w) ≠ 0 → w ∈ Y := by
    intro u hu w hw hm
    by_cases huab : u = a ∨ u = b
    · -- then `c ∈ X`
      have hcX : c ∈ X := by
        by_contra h; rw [hY, if_neg h] at hu
        rcases huab with h' | h'
        · exact (hXab u hu).1 h'
        · exact (hXab u hu).2 h'
      rw [hY, if_pos hcX]
      rcases huab with rfl | rfl
      · rw [hP.mult_a] at hm
        by_cases h1 : w = b
        · simp [h1]
        · rw [if_neg h1] at hm
          by_cases h2 : w = c
          · simp [h2, hcX]
          · rw [if_neg h2] at hm; exact absurd rfl hm
      · rw [hP.mult_b] at hm
        by_cases h1 : w = a
        · simp [h1]
        · rw [if_neg h1] at hm
          by_cases h2 : w = d
          · simp [h2, hcdX.mp hcX]
          · rw [if_neg h2] at hm; exact absurd rfl hm
    · have huX : u ∈ X := by
        rw [hY] at hu; split_ifs at hu
        · simp only [Finset.mem_insert] at hu; tauto
        · exact hu
      by_cases hwa : w = a
      · subst hwa
        have : u = c := by
          rw [Sym2.eq_swap, hP.mult_a] at hm
          by_contra h; rw [if_neg (fun h' => huab (Or.inr h')), if_neg h] at hm; exact hm rfl
        subst this
        rw [hY, if_pos huX]; simp
      by_cases hwb : w = b
      · subst hwb
        have : u = d := by
          rw [Sym2.eq_swap, hP.mult_b] at hm
          by_contra h; rw [if_neg (fun h' => huab (Or.inl h')), if_neg h] at hm; exact hm rfl
        subst this
        rw [hY, if_pos (hcdX.mpr huX)]; simp
      · have hwV : w ∈ (H.verts.erase a).erase b := by simp [hwa, hwb, hw]
        have := hnew u w (hXab u huX).1 (hXab u huX).2 hwa hwb
        exact hXY (hcl u huX w hwV (by omega))
  obtain ⟨x₀, hx₀⟩ := hne
  have hYall : Y = H.verts := eq_of_closed' hc hYV ⟨x₀, hXY hx₀⟩ hYc
  apply Finset.Subset.antisymm hX
  intro v hv
  simp only [Finset.mem_erase] at hv
  have : v ∈ Y := by rw [hYall]; exact hv.2.2
  rw [hY] at this
  split_ifs at this
  · simp only [Finset.mem_insert] at this
    rcases this with h | h | h
    · exact absurd h hv.2.1
    · exact absurd h hv.1
    · exact h
  · exact this

end WaveTurbulence.TVine.Core
