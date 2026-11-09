/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Pendant

/-!
# N3 Lemma 4.1: a T-vine has no interior cut atom (path-wise)

`noCutVertex_holds : NoCutVertexStatement`. Proof (N3 Lemma 4.1): the doubled triangle is 2-connected; undoing a
(Y2) move (a (Z1) move) keeps a loopless 4-regular graph 2-connected (`twoConn_of_y2Move`); so the closure is
2-connected, and un-smoothing the joints keeps every interior atom a non-cut atom (`connOn_erase_of_smooth`).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

/-- `H` is 2-connected: removing any one atom leaves it connected. -/
def TwoConn (H : UMultigraph V) : Prop := ∀ v ∈ H.verts, ConnOn H (H.verts.erase v)

/-- Every atom set of a doubled triangle is connected. -/
theorem doubledTriangle_connOn {T : UMultigraph V} (hT : IsDoubledTriangle T) {K : Finset V}
    (hK : K ⊆ T.verts) : ConnOn T K := by
  apply connOn_of_closed
  intro X hX hne hcl
  apply Finset.Subset.antisymm hX
  intro w hw
  obtain ⟨x, hx⟩ := hne
  by_cases hxw : x = w
  · exact hxw ▸ hx
  · exact hcl x hx w hw (by rw [doubledTriangle_mult_of_ne hT (hK (hX hx)) (hK hw) hxw]; omega)

/-- Undoing a (Y2) move keeps connectivity. -/
theorem connected_of_y2Move {H : UMultigraph V} {a b c d : V} (hP : IsY2Pair H a b c d)
    (hc : Connected (y2Move H a b c d)) : Connected H := by
  classical
  apply connected_of_closed
  intro X hX hne hcl
  have hab : a ∈ X ↔ b ∈ X := ⟨fun h => hcl a h b hP.b_mem (by rw [hP.mult_ab]; omega),
    fun h => hcl b h a hP.a_mem (by rw [Sym2.eq_swap, hP.mult_ab]; omega)⟩
  have hac : a ∈ X ↔ c ∈ X := ⟨fun h => hcl a h c hP.c_mem (by rw [hP.mult_ac]; omega),
    fun h => hcl c h a hP.a_mem (by rw [Sym2.eq_swap, hP.mult_ac]; omega)⟩
  have hbd : b ∈ X ↔ d ∈ X := ⟨fun h => hcl b h d hP.d_mem (by rw [hP.mult_bd]; omega),
    fun h => hcl d h b hP.b_mem (by rw [Sym2.eq_swap, hP.mult_bd]; omega)⟩
  set X' := (X.erase a).erase b with hX'
  have hX'V : X' ⊆ (y2Move H a b c d).verts := by
    rw [y2Move_verts hP]; intro x hx
    simp only [hX', Finset.mem_erase] at hx ⊢; exact ⟨hx.1, hx.2.1, hX hx.2.2⟩
  have hcV : c ∈ (H.verts.erase a).erase b := by simp [hP.c_ne_a, hP.c_ne_b, hP.c_mem]
  have hne' : X'.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    by_cases hxab : x = a ∨ x = b
    · have hcX : c ∈ X := by
        rcases hxab with rfl | rfl
        · exact hac.mp hx
        · exact hac.mp (hab.mpr hx)
      exact ⟨c, by simp [hX', hP.c_ne_a, hP.c_ne_b, hcX]⟩
    · exact ⟨x, by simp only [hX', Finset.mem_erase]; exact ⟨fun h => hxab (Or.inr h), fun h => hxab (Or.inl h), hx⟩⟩
  have hall := eq_of_closed' hc hX'V hne' (by
    intro u hu w hw hm
    rw [y2Move_verts hP] at hw
    simp only [hX', Finset.mem_erase] at hu hw ⊢
    refine ⟨hw.1, hw.2.1, ?_⟩
    rw [y2Move_mult, if_neg (by rintro (h | h) <;> rcases Sym2.mem_iff.mp h with h | h <;> tauto)] at hm
    by_cases hG : H.mult s(u, w) = 0
    · rw [hG, zero_add] at hm
      have huw : s(u, w) = s(c, d) := by by_contra h; rw [if_neg h] at hm; exact hm rfl
      have hcdX : c ∈ X ↔ d ∈ X := hac.symm.trans (hab.trans hbd)
      rcases Sym2.eq_iff.mp huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcdX.mp hu.2.2
      · exact hcdX.mpr hu.2.2
    · exact hcl u hu.2.2 w hw.2.2 hG)
  apply Finset.Subset.antisymm hX
  intro v hv
  by_cases hva : v = a
  · subst hva
    have : c ∈ X' := by rw [hall, y2Move_verts hP]; exact hcV
    exact hac.mpr (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase this))
  by_cases hvb : v = b
  · subst hvb
    have : c ∈ X' := by rw [hall, y2Move_verts hP]; exact hcV
    exact hab.mp (hac.mpr (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase this)))
  have : v ∈ X' := by rw [hall, y2Move_verts hP]; simp [hva, hvb, hv]
  exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase this)

/-- An atom of degree `k` has a neighbour outside `Z` if `Z` carries fewer than `k` of its bond ends. -/
theorem exists_nbr_outside {H : UMultigraph V} {v : V} {Z : Finset V} {k : ℕ} (hdeg : deg H v = k)
    (hZ : ∑ z ∈ Z, H.mult s(v, z) + H.mult s(v, v) < k) :
    ∃ w ∈ H.verts, w ∉ Z ∧ H.mult s(v, w) ≠ 0 := by
  by_contra hne
  push_neg at hne
  have h1 : ∑ w ∈ H.verts, H.mult s(v, w) ≤ ∑ z ∈ Z, H.mult s(v, z) := by
    rw [← Finset.sum_filter_add_sum_filter_not H.verts (· ∈ Z)]
    have h2 : ∑ w ∈ H.verts.filter (fun w => w ∉ Z), H.mult s(v, w) = 0 :=
      Finset.sum_eq_zero fun w hw => by
        obtain ⟨hwV, hwZ⟩ := Finset.mem_filter.mp hw
        by_contra h; exact absurd (hne w hwV hwZ) h
    rw [h2, add_zero]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_filter.mp hx).2)
      (fun _ _ _ => Nat.zero_le _)
  unfold deg at hdeg
  omega

/-- Undoing a (Y2) move: removing an atom off the pair. -/
theorem connOn_erase_of_y2Move_off {H : UMultigraph V} {a b c d v : V} (hP : IsY2Pair H a b c d)
    (h2 : TwoConn (y2Move H a b c d)) (hvV : v ∈ H.verts) (hva : v ≠ a) (hvb : v ≠ b) :
    ConnOn H (H.verts.erase v) := by
  classical
  apply connOn_of_closed
  intro X hX hne hcl
  have hXv : ∀ x ∈ X, x ≠ v ∧ x ∈ H.verts := fun x hx => by
    have := hX hx; exact ⟨Finset.ne_of_mem_erase this, Finset.mem_of_mem_erase this⟩
  have hmemE : ∀ {x}, x ∈ H.verts → x ≠ v → x ∈ H.verts.erase v := fun h1 h2 => Finset.mem_erase.mpr ⟨h2, h1⟩
  have hab : a ∈ X ↔ b ∈ X := ⟨fun h => hcl a h b (hmemE hP.b_mem (Ne.symm hvb)) (by rw [hP.mult_ab]; omega),
    fun h => hcl b h a (hmemE hP.a_mem (Ne.symm hva)) (by rw [Sym2.eq_swap, hP.mult_ab]; omega)⟩
  have hac : c ≠ v → (a ∈ X ↔ c ∈ X) := fun hcv =>
    ⟨fun h => hcl a h c (hmemE hP.c_mem hcv) (by rw [hP.mult_ac]; omega),
     fun h => hcl c h a (hmemE hP.a_mem (Ne.symm hva)) (by rw [Sym2.eq_swap, hP.mult_ac]; omega)⟩
  have hbd : d ≠ v → (b ∈ X ↔ d ∈ X) := fun hdv =>
    ⟨fun h => hcl b h d (hmemE hP.d_mem hdv) (by rw [hP.mult_bd]; omega),
     fun h => hcl d h b (hmemE hP.b_mem (Ne.symm hvb)) (by rw [Sym2.eq_swap, hP.mult_bd]; omega)⟩
  -- one of `c, d` is not `v`
  have hcd : c ≠ v ∨ d ≠ v := by
    by_contra h; push_neg at h; exact hP.ext_ne (h.1.trans h.2.symm)
  -- if the pair is in `X`, so is an external
  have hext : a ∈ X → (c ∈ X ∧ c ≠ v) ∨ (d ∈ X ∧ d ≠ v) := by
    intro ha
    rcases hcd with h | h
    · exact Or.inl ⟨(hac h).mp ha, h⟩
    · exact Or.inr ⟨(hbd h).mp (hab.mp ha), h⟩
  set X' := (X.erase a).erase b with hX'
  have hV' : (y2Move H a b c d).verts = (H.verts.erase a).erase b := y2Move_verts hP
  have hvV' : v ∈ (y2Move H a b c d).verts := by rw [hV']; simp [hva, hvb, hvV]
  have hX'V : X' ⊆ (y2Move H a b c d).verts.erase v := by
    intro x hx
    simp only [hX', Finset.mem_erase] at hx
    rw [hV']; simp only [Finset.mem_erase]
    exact ⟨(hXv x hx.2.2).1, hx.1, hx.2.1, (hXv x hx.2.2).2⟩
  have hne' : X'.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    by_cases hxab : x = a ∨ x = b
    · have ha : a ∈ X := by rcases hxab with rfl | rfl; exacts [hx, hab.mpr hx]
      rcases hext ha with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact ⟨c, by simp [hX', hP.c_ne_a, hP.c_ne_b, h1]⟩
      · exact ⟨d, by simp [hX', hP.d_ne_a, hP.d_ne_b, h1]⟩
    · exact ⟨x, by simp only [hX', Finset.mem_erase]; exact ⟨fun h => hxab (Or.inr h), fun h => hxab (Or.inl h), hx⟩⟩
  have hall := eq_of_closed' (h2 v hvV') hX'V hne' (by
    intro u hu w hw hm
    have hwV : w ∈ (H.verts.erase a).erase b := by rw [← hV']; exact Finset.mem_of_mem_erase hw
    have hwv := Finset.ne_of_mem_erase hw
    simp only [Finset.mem_erase] at hwV
    simp only [hX', Finset.mem_erase] at hu ⊢
    refine ⟨hwV.1, hwV.2.1, ?_⟩
    have hnab : ¬ (a ∈ s(u, w) ∨ b ∈ s(u, w)) := by
      rintro (h | h) <;> rcases Sym2.mem_iff.mp h with h | h
      exacts [hu.2.1 h.symm, hwV.2.1 h.symm, hu.1 h.symm, hwV.1 h.symm]
    rw [y2Move_mult, if_neg hnab] at hm
    by_cases hG : H.mult s(u, w) = 0
    · rw [hG, zero_add] at hm
      have huw : s(u, w) = s(c, d) := by by_contra h; rw [if_neg h] at hm; exact hm rfl
      have huv := (hXv u hu.2.2).1
      rcases Sym2.eq_iff.mp huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hbd hwv).mp (hab.mp ((hac huv).mpr hu.2.2))
      · exact (hac hwv).mp (hab.mpr ((hbd huv).mpr hu.2.2))
    · exact hcl u hu.2.2 w (hmemE hwV.2.2 hwv) hG)
  apply Finset.Subset.antisymm hX
  intro x hx
  have hxv := Finset.ne_of_mem_erase hx
  have hxV := Finset.mem_of_mem_erase hx
  have hsub : ∀ y, y ≠ a → y ≠ b → y ≠ v → y ∈ H.verts → y ∈ X := by
    intro y h1 h2 h3 h4
    have : y ∈ X' := by rw [hall, hV']; simp [h1, h2, h3, h4]
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase this)
  have hpair : a ∈ X := by
    rcases hcd with h | h
    · exact (hac h).mpr (hsub c hP.c_ne_a hP.c_ne_b h hP.c_mem)
    · exact hab.mpr ((hbd h).mpr (hsub d hP.d_ne_a hP.d_ne_b h hP.d_mem))
  by_cases hxa : x = a
  · exact hxa ▸ hpair
  by_cases hxb : x = b
  · exact hxb ▸ hab.mp hpair
  exact hsub x hxa hxb hxv hxV

/-- Undoing a (Y2) move: removing the pair atom `a`. -/
theorem connOn_erase_of_y2Move_a {H : UMultigraph V} {a b c d : V} (hP : IsY2Pair H a b c d)
    (hl : H.Loopless) (hreg : ∀ v ∈ H.verts, deg H v = 4) (h2 : TwoConn (y2Move H a b c d))
    (hc : Connected (y2Move H a b c d)) : ConnOn H (H.verts.erase a) := by
  classical
  apply connOn_of_closed
  intro X hX hne hcl
  have hXa : ∀ x ∈ X, x ≠ a ∧ x ∈ H.verts := fun x hx => by
    have := hX hx; exact ⟨Finset.ne_of_mem_erase this, Finset.mem_of_mem_erase this⟩
  have hmemE : ∀ {x}, x ∈ H.verts → x ≠ a → x ∈ H.verts.erase a := fun h1 h2 => Finset.mem_erase.mpr ⟨h2, h1⟩
  have hbd : b ∈ X ↔ d ∈ X :=
    ⟨fun h => hcl b h d (hmemE hP.d_mem hP.d_ne_a) (by rw [hP.mult_bd]; omega),
     fun h => hcl d h b (hmemE hP.b_mem hP.ne.symm) (by rw [Sym2.eq_swap, hP.mult_bd]; omega)⟩
  have hV' : (y2Move H a b c d).verts = (H.verts.erase a).erase b := y2Move_verts hP
  set X' := X.erase b with hX'
  have hX'V : X' ⊆ (y2Move H a b c d).verts := by
    intro x hx
    rw [hV']
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hx,
      Finset.mem_erase.mpr ⟨(hXa x (Finset.mem_of_mem_erase hx)).1, (hXa x (Finset.mem_of_mem_erase hx)).2⟩⟩
  -- bonds of `H'` inside `X'` come from `H`, except possibly the new bond `c–d`
  have hstep : ∀ u ∈ X', ∀ w ∈ (y2Move H a b c d).verts, (y2Move H a b c d).mult s(u, w) ≠ 0 →
      w ∈ X' ∨ s(u, w) = s(c, d) := by
    intro u hu w hw hm
    rw [hV'] at hw
    simp only [Finset.mem_erase] at hw
    rw [y2Move_mult, if_neg (by
      rintro (h | h) <;> rcases Sym2.mem_iff.mp h with h | h
      · exact (hXa u (Finset.mem_of_mem_erase hu)).1 h.symm
      · exact hw.2.1 h.symm
      · exact (Finset.ne_of_mem_erase hu) h.symm
      · exact hw.1 h.symm)] at hm
    by_cases hG : H.mult s(u, w) = 0
    · rw [hG, zero_add] at hm
      exact Or.inr (by by_contra h; rw [if_neg h] at hm; exact hm rfl)
    · exact Or.inl (Finset.mem_erase.mpr ⟨hw.1, hcl u (Finset.mem_of_mem_erase hu) w (hmemE hw.2.2 hw.2.1) hG⟩)
  have hcX'V : c ∈ (y2Move H a b c d).verts := by rw [hV']; simp [hP.c_ne_a, hP.c_ne_b, hP.c_mem]
  have hdX'V : d ∈ (y2Move H a b c d).verts := by rw [hV']; simp [hP.d_ne_a, hP.d_ne_b, hP.d_mem]
  -- an atom `x ∉ {a, b}` of `H'` outside `X` but with all `H`-neighbours off `{a, b, x}` in `X` is impossible
  have hforce : ∀ x, x ≠ a → x ≠ b → x ∈ H.verts → (∀ w, w ≠ a → w ≠ b → w ≠ x → w ∈ H.verts → w ∈ X) →
      H.mult s(x, a) + H.mult s(x, b) < 4 → x ∈ X := by
    intro x hxa hxb hxV hall hsmall
    obtain ⟨w, hwV, hwZ, hm⟩ := exists_nbr_outside (Z := {a, b, x}) (hreg x hxV) (by
      rw [Finset.sum_insert (by simp [Ne.symm hxa, hP.ne]), Finset.sum_pair (Ne.symm hxb), hl x]; omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwZ
    have hwX := hall w hwZ.1 hwZ.2.1 hwZ.2.2 hwV
    exact hcl w hwX x (hmemE hxV hxa) (by rw [Sym2.eq_swap]; exact hm)
  by_cases hcd : c ∈ X ↔ d ∈ X
  · -- `X'` is closed in `H'`
    have hne' : X'.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      by_cases hxb : x = b
      · exact ⟨d, Finset.mem_erase.mpr ⟨hP.d_ne_b, hbd.mp (hxb ▸ hx)⟩⟩
      · exact ⟨x, Finset.mem_erase.mpr ⟨hxb, hx⟩⟩
    have hall := eq_of_closed' hc hX'V hne' (by
      intro u hu w hw hm
      rcases hstep u hu w hw hm with h | h
      · exact h
      · have hu' := Finset.mem_of_mem_erase hu
        rw [hV'] at hw; simp only [Finset.mem_erase] at hw
        rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Finset.mem_erase.mpr ⟨hw.1, hcd.mp hu'⟩
        · exact Finset.mem_erase.mpr ⟨hw.1, hcd.mpr hu'⟩)
    apply Finset.Subset.antisymm hX
    intro x hx
    have hsub : ∀ y, y ≠ a → y ≠ b → y ∈ H.verts → y ∈ X := by
      intro y h1 h2 h3
      have : y ∈ X' := by rw [hall, hV']; simp [h1, h2, h3]
      exact Finset.mem_of_mem_erase this
    by_cases hxb : x = b
    · exact hxb ▸ hbd.mpr (hsub d hP.d_ne_a hP.d_ne_b hP.d_mem)
    · exact hsub x (Finset.ne_of_mem_erase hx) hxb (Finset.mem_of_mem_erase hx)
  · exfalso
    by_cases hcX : c ∈ X
    · have hdX : d ∉ X := fun h => hcd ⟨fun _ => h, fun _ => hcX⟩
      -- `X'` is closed in `H' − d`, so it is everything but `d`
      have hall := eq_of_closed' (h2 d hdX'V) (S := X') (fun x hx => Finset.mem_erase.mpr
        ⟨fun h => hdX (h ▸ Finset.mem_of_mem_erase hx), hX'V hx⟩)
        ⟨c, Finset.mem_erase.mpr ⟨hP.c_ne_b, hcX⟩⟩ (by
          intro u hu w hw hm
          rcases hstep u hu w (Finset.mem_of_mem_erase hw) hm with h | h
          · exact h
          · have hwd := Finset.ne_of_mem_erase hw
            rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact absurd rfl hwd
            · exact Finset.mem_erase.mpr ⟨hP.c_ne_b, hcX⟩)
      apply hdX
      apply hforce d hP.d_ne_a hP.d_ne_b hP.d_mem
      · intro w h1 h2 h3 h4
        have : w ∈ X' := by rw [hall, hV']; simp [h1, h2, h3, h4]
        exact Finset.mem_of_mem_erase this
      · rw [Sym2.eq_swap, hP.mult_a, if_neg hP.d_ne_b, if_neg (Ne.symm hP.ext_ne), Sym2.eq_swap, hP.mult_bd]
        omega
    · have hdX : d ∈ X := by by_contra h; exact hcd ⟨fun h' => absurd h' hcX, fun h' => absurd h' h⟩
      have hall := eq_of_closed' (h2 c hcX'V) (S := X') (fun x hx => Finset.mem_erase.mpr
        ⟨fun h => hcX (h ▸ Finset.mem_of_mem_erase hx), hX'V hx⟩)
        ⟨d, Finset.mem_erase.mpr ⟨hP.d_ne_b, hdX⟩⟩ (by
          intro u hu w hw hm
          rcases hstep u hu w (Finset.mem_of_mem_erase hw) hm with h | h
          · exact h
          · have hwc := Finset.ne_of_mem_erase hw
            rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Finset.mem_erase.mpr ⟨hP.d_ne_b, hdX⟩
            · exact absurd rfl hwc)
      apply hcX
      apply hforce c hP.c_ne_a hP.c_ne_b hP.c_mem
      · intro w h1 h2 h3 h4
        have : w ∈ X' := by rw [hall, hV']; simp [h1, h2, h3, h4]
        exact Finset.mem_of_mem_erase this
      · rw [Sym2.eq_swap, hP.mult_ac, Sym2.eq_swap, hP.mult_b, if_neg hP.c_ne_a, if_neg hP.ext_ne]
        omega

/-- **Undoing a (Y2) move keeps 2-connectivity** (loopless, 4-regular). -/
theorem twoConn_of_y2Move {H : UMultigraph V} {a b c d : V} (hP : IsY2Pair H a b c d) (hl : H.Loopless)
    (hreg : ∀ v ∈ H.verts, deg H v = 4) (h2 : TwoConn (y2Move H a b c d))
    (hc : Connected (y2Move H a b c d)) : TwoConn H := by
  intro v hv
  by_cases hva : v = a
  · subst hva; exact connOn_erase_of_y2Move_a hP hl hreg h2 hc
  by_cases hvb : v = b
  · subst hvb
    rw [← y2Move_swap] at h2 hc
    exact connOn_erase_of_y2Move_a hP.swap hl hreg h2 hc
  exact connOn_erase_of_y2Move_off hP h2 hv hva hvb

/-- Along a (Y2)-path to a doubled triangle, a loopless 4-regular graph is connected and 2-connected. -/
theorem twoConn_of_y2Path {H T' : UMultigraph V} {ps : List (Sym2 V)} (hp : Y2Path H ps T')
    (hT : IsDoubledTriangle T') : H.Loopless → (∀ v ∈ H.verts, deg H v = 4) → Connected H ∧ TwoConn H := by
  induction hp with
  | nil G =>
    intro _ _
    exact ⟨doubledTriangle_connOn hT (le_refl _), fun v _ => doubledTriangle_connOn hT (Finset.erase_subset _ _)⟩
  | @cons H T' p q p' q' rest hP hrest ih =>
    intro hl hreg
    have hl' := loopless_y2Move hP hl
    have hreg' : ∀ v ∈ (y2Move H p q p' q').verts, deg (y2Move H p q p' q') v = 4 := by
      intro v hv
      have hv' := y2Move_verts_sub hv
      rw [deg_y2Move hP hv'.1 hv'.2]
      rw [y2Move_verts hP] at hv
      exact hreg v (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv))
    obtain ⟨hc', h2'⟩ := ih hT hl' hreg'
    exact ⟨connected_of_y2Move hP hc', twoConn_of_y2Move hP hl hreg h2' hc'⟩

/-- Un-smoothing a joint keeps a non-cut atom a non-cut atom. -/
theorem connOn_erase_of_smooth {G : UMultigraph V} {j n n' v : V} (hl : G.mult s(j, j) = 0)
    (hnb : nbrs G j = {n, n'}) (hnn : n ≠ n') (hvV : v ∈ G.verts) (hvj : v ≠ j)
    (h : ConnOn (smooth G j n n') ((smooth G j n n').verts.erase v)) : ConnOn G (G.verts.erase v) := by
  classical
  obtain ⟨hnj, hn'j⟩ := nbrs_ne_of_loop hl hnb
  have hnV := nbrs_mem_verts hnb
  have hjV := mem_verts_of_nbrs hnb
  have hV' : (smooth G j n n').verts = G.verts.erase j := smooth_verts hnV.1 hnV.2
  have hjn : G.mult s(j, n) ≠ 0 := by rw [mult_of_nbrs_eq hnb hnj, count_pair_self]; omega
  have hjn' : G.mult s(j, n') ≠ 0 := by
    rw [mult_of_nbrs_eq hnb hn'j, count_pair_of_ne (Ne.symm hnn), if_pos rfl]; omega
  apply connOn_of_closed
  intro X hX hne hcl
  have hmemE : ∀ {x}, x ∈ G.verts → x ≠ v → x ∈ G.verts.erase v := fun h1 h2 => Finset.mem_erase.mpr ⟨h2, h1⟩
  have hjX_of : ∀ y, (y = n ∨ y = n') → y ∈ X → j ∈ X := by
    rintro y (rfl | rfl) hy
    · exact hcl _ hy j (hmemE hjV (Ne.symm hvj)) (by rw [Sym2.eq_swap]; exact hjn)
    · exact hcl _ hy j (hmemE hjV (Ne.symm hvj)) (by rw [Sym2.eq_swap]; exact hjn')
  have hX_of_j : j ∈ X → ∀ y, (y = n ∨ y = n') → y ≠ v → y ∈ X := by
    rintro hj y (rfl | rfl) hyv
    · exact hcl j hj _ (hmemE hnV.1 hyv) hjn
    · exact hcl j hj _ (hmemE hnV.2 hyv) hjn'
  have hone : n ≠ v ∨ n' ≠ v := by
    by_contra h; push_neg at h; exact hnn (h.1.trans h.2.symm)
  set X' := X.erase j with hX'
  have hX'V : X' ⊆ (smooth G j n n').verts.erase v := by
    intro x hx
    rw [hV']
    have hxX := Finset.mem_of_mem_erase hx
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase (hX hxX),
      Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hx, Finset.mem_of_mem_erase (hX hxX)⟩⟩
  have hne' : X'.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    by_cases hxj : x = j
    · subst hxj
      rcases hone with h | h
      · exact ⟨n, Finset.mem_erase.mpr ⟨hnj, hX_of_j hx n (Or.inl rfl) h⟩⟩
      · exact ⟨n', Finset.mem_erase.mpr ⟨hn'j, hX_of_j hx n' (Or.inr rfl) h⟩⟩
    · exact ⟨x, Finset.mem_erase.mpr ⟨hxj, hx⟩⟩
  have hall := eq_of_closed' h hX'V hne' (by
    intro u hu w hw hm
    have huj := Finset.ne_of_mem_erase hu
    have huX := Finset.mem_of_mem_erase hu
    have hwv := Finset.ne_of_mem_erase hw
    have hwV' := Finset.mem_of_mem_erase hw
    rw [hV'] at hwV'
    have hwj := Finset.ne_of_mem_erase hwV'
    have hwV := Finset.mem_of_mem_erase hwV'
    rw [smooth_mult_at G huj, if_neg hwj] at hm
    by_cases hG : G.mult s(u, w) = 0
    · rw [hG, zero_add] at hm
      have huw : s(u, w) = s(n, n') := by by_contra h'; rw [if_neg h'] at hm; exact hm rfl
      refine Finset.mem_erase.mpr ⟨hwj, ?_⟩
      rcases Sym2.eq_iff.mp huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hX_of_j (hjX_of u (Or.inl rfl) huX) w (Or.inr rfl) hwv
      · exact hX_of_j (hjX_of u (Or.inr rfl) huX) w (Or.inl rfl) hwv
    · exact Finset.mem_erase.mpr ⟨hwj, hcl u huX w (hmemE hwV hwv) hG⟩)
  apply Finset.Subset.antisymm hX
  intro x hx
  have hsub : ∀ y, y ≠ j → y ≠ v → y ∈ G.verts → y ∈ X := by
    intro y h1 h2 h3
    have : y ∈ X' := by rw [hall, hV']; simp [h1, h2, h3]
    exact Finset.mem_of_mem_erase this
  by_cases hxj : x = j
  · subst hxj
    rcases hone with h | h
    · exact hjX_of n (Or.inl rfl) (hsub n hnj h hnV.1)
    · exact hjX_of n' (Or.inr rfl) (hsub n' hn'j h hnV.2)
  · exact hsub x hxj (Finset.ne_of_mem_erase hx) (Finset.mem_of_mem_erase hx)

/-- **N3 Lemma 4.1** (no interior cut atom). -/
theorem noCutVertex_holds : NoCutVertexStatement.{u} := by
  intro V _ G j₁ j₂ hT w hw
  have hl := hT.loopless
  obtain ⟨hB, hm2, C, hC, hRT⟩ := hT
  obtain ⟨hj₁V, hj₂V, hj, hd₁, hd₂, hd, hconn⟩ := hB
  have hσ := hC.1
  have hCl := hC.2.2.1
  obtain ⟨n1, n1', n2, n2', h1, h2, rfl⟩ := hC.eq_smooth hl hj
  have hn1V := nbrs_mem_verts h1
  have hB₁V : (smooth G j₁ n1 n1').verts = G.verts.erase j₁ := smooth_verts hn1V.1 hn1V.2
  have hl₂ := smooth_loop_j₂ hl hj hσ h1
  have hn2V := nbrs_mem_verts h2
  have hCV : (smooth (smooth G j₁ n1 n1') j₂ n2 n2').verts = (G.verts.erase j₁).erase j₂ := by
    rw [smooth_verts hn2V.1 hn2V.2, hB₁V]
  simp only [interior, Finset.mem_erase] at hw
  obtain ⟨hwj₂, hwj₁, hwV⟩ := hw
  -- the closure is 4-regular
  have hreg : ∀ v ∈ (smooth (smooth G j₁ n1 n1') j₂ n2 n2').verts,
      deg (smooth (smooth G j₁ n1 n1') j₂ n2 n2') v = 4 := by
    intro v hv
    rw [hCV] at hv
    simp only [Finset.mem_erase] at hv
    rw [deg_smooth hl₂ h2 hv.1, deg_smooth (hl j₁) h1 hv.2.1]
    exact hd v hv.2.2 hv.2.1 hv.1
  obtain ⟨ps, T', hp, hT'⟩ := reducesToT_iff.mp hRT
  obtain ⟨-, h2C⟩ := twoConn_of_y2Path hp hT' hCl hreg
  have hn2j := nbrs_ne_of_loop hl₂ h2
  have hn1j := nbrs_ne_of_loop (hl j₁) h1
  have hnn2 : n2 ≠ n2' := by
    intro h
    have := hCl n2
    rw [smooth_mult_at _ hn2j.1, if_neg hn2j.1, h, if_pos rfl] at this
    omega
  have hnn1 : n1 ≠ n1' := by
    intro h
    have hσc : G.mult s(j₁, j₂) = ({n1, n1'} : Multiset V).count j₂ := mult_of_nbrs_eq h1 (Ne.symm hj)
    have hn1j₂ : n1 ≠ j₂ := by
      intro h'
      have h2c : ({n1, n1'} : Multiset V).count j₂ = 2 := by rw [← h, ← h', count_pair_self, if_pos rfl]
      omega
    have := hCl n1
    rw [smooth_mult_at _ hn1j₂, if_neg hn1j₂, smooth_mult_at _ hn1j.1, if_neg hn1j.1, h, if_pos rfl] at this
    omega
  have hwB₁ : w ∈ (smooth G j₁ n1 n1').verts := by rw [hB₁V]; exact Finset.mem_erase.mpr ⟨hwj₁, hwV⟩
  have hwC : w ∈ (smooth (smooth G j₁ n1 n1') j₂ n2 n2').verts := by
    rw [hCV]; simp [hwj₁, hwj₂, hwV]
  have step1 := connOn_erase_of_smooth hl₂ h2 hnn2 hwB₁ hwj₂ (h2C w hwC)
  exact connOn_erase_of_smooth (hl j₁) h1 hnn1 hwV hwj₁ step1

end WaveTurbulence.TVine.Core
