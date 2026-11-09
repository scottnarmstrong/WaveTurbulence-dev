/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Base

/-!
# Soundness of the sides of the 2-cut removals (M4 §8 F2, first half)

* `splits2_spec`, `mem_splits2_filter`: `splits2` enumerates exactly the removals of at most two bond copies;
* `sideOf_spec`: a side is reached from one atom, and either covers everything or is closed with a connected
  complement;
* `cut_eq_cross`: L1's `cut G X` is the number of bond copies of the instance crossing `X`;
* `samePiece_of_sides`: atoms on the same side of every removal are in the same piece (L1's cut-based
  `SamePieceU`);
* `not_samePiece_of_side`: atoms separated by some side are not.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine WaveTurbulence.TVine.Core

/-! ## Removals of at most two bond copies -/

theorem splits1_spec : ∀ {es : Edges} {p : Edges × Edges}, p ∈ splits1 es →
    p.1.length ≤ 1 ∧ (p.1 ++ p.2).Perm es
  | [], p, h => by
    simp only [splits1, List.mem_singleton] at h; subst h; simp
  | e :: es, p, h => by
    simp only [splits1, List.mem_append, List.mem_map, List.mem_singleton] at h
    rcases h with ⟨p', hp', rfl⟩ | rfl
    · obtain ⟨h1, h2⟩ := splits1_spec hp'
      exact ⟨h1, List.perm_middle.trans (h2.cons e)⟩
    · simp

theorem splits2_spec : ∀ {es : Edges} {p : Edges × Edges}, p ∈ splits2 es →
    p.1.length ≤ 2 ∧ (p.1 ++ p.2).Perm es
  | [], p, h => by
    simp only [splits2, List.mem_singleton] at h; subst h; simp
  | e :: es, p, h => by
    simp only [splits2, List.mem_append, List.mem_map] at h
    rcases h with ⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩
    · obtain ⟨h1, h2⟩ := splits2_spec hp'
      exact ⟨h1, List.perm_middle.trans (h2.cons e)⟩
    · obtain ⟨h1, h2⟩ := splits1_spec hp'
      refine ⟨by simp only [List.length_cons]; omega, ?_⟩
      simp only [List.cons_append]
      exact h2.cons e

theorem mem_splits1_filter (P : ℕ × ℕ → Bool) : ∀ {es : Edges}, (es.filter P).length ≤ 1 →
    ∃ p ∈ splits1 es, p.2 = es.filter (fun e => !P e)
  | [], _ => ⟨([], []), by simp [splits1], rfl⟩
  | e :: es, h => by
    by_cases he : P e = true
    · rw [List.filter_cons_of_pos he, List.length_cons] at h
      have hnil : es.filter P = [] := List.length_eq_zero_iff.mp (by omega)
      refine ⟨([e], es), by simp [splits1], ?_⟩
      rw [List.filter_cons_of_neg (by simp [he])]
      symm
      rw [List.filter_eq_self]
      intro x hx
      have := List.filter_eq_nil_iff.mp hnil x hx
      simpa using this
    · rw [List.filter_cons_of_neg he] at h
      obtain ⟨p, hp, hp2⟩ := mem_splits1_filter P h
      refine ⟨(p.1, e :: p.2), ?_, ?_⟩
      · simp only [splits1, List.mem_append, List.mem_map]
        exact Or.inl ⟨p, hp, rfl⟩
      · rw [List.filter_cons_of_pos (by simpa using he), hp2]

theorem mem_splits2_filter (P : ℕ × ℕ → Bool) : ∀ {es : Edges}, (es.filter P).length ≤ 2 →
    ∃ p ∈ splits2 es, p.2 = es.filter (fun e => !P e)
  | [], _ => ⟨([], []), by simp [splits2], rfl⟩
  | e :: es, h => by
    by_cases he : P e = true
    · rw [List.filter_cons_of_pos he, List.length_cons] at h
      obtain ⟨p, hp, hp2⟩ := mem_splits1_filter P (es := es) (by omega)
      refine ⟨(e :: p.1, p.2), ?_, ?_⟩
      · simp only [splits2, List.mem_append, List.mem_map]
        exact Or.inr ⟨p, hp, rfl⟩
      · rw [List.filter_cons_of_neg (by simp [he]), hp2]
    · rw [List.filter_cons_of_neg he] at h
      obtain ⟨p, hp, hp2⟩ := mem_splits2_filter P h
      refine ⟨(p.1, e :: p.2), ?_, ?_⟩
      · simp only [splits2, List.mem_append, List.mem_map]
        exact Or.inl ⟨p, hp, rfl⟩
      · rw [List.filter_cons_of_pos (by simpa using he), hp2]

/-! ## Sides -/

theorem sideOf_spec {V : ℕ} {es' : Edges} {X : ℕ} (h : sideOf V es' = some X) :
    (∃ s, Reached es' s X) ∧ ((∀ v < 32, mem v (sdiff V X) = false) ∨
      ((∃ t, Reached es' t (sdiff V X)) ∧ closedB es' X = true)) := by
  unfold sideOf at h
  split at h
  · simp at h
  · rename_i s _
    simp only at h
    split at h
    · rename_i hY
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨⟨s, comp_reached _ _⟩, Or.inl fun v hv => lowBit_none hY hv⟩
    · rename_i t hY
      split_ifs at h with hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hc
      refine ⟨⟨s, comp_reached _ _⟩, Or.inr ⟨⟨t, ?_⟩, hc.2⟩⟩
      have := comp_reached es' t
      rwa [show comp es' t = sdiff V (comp es' s) by simpa using hc.1] at this

theorem go_spec {V : ℕ} : ∀ {rs : List Edges} {sides : List ℕ}, allSides.go V rs = some sides →
    (∀ r ∈ rs, ∃ X ∈ sides, sideOf V r = some X) ∧ (∀ X ∈ sides, ∃ r ∈ rs, sideOf V r = some X)
  | [], sides, h => by
    simp only [allSides.go, Option.some.injEq] at h
    subst h; simp
  | r :: rs, sides, h => by
    simp only [allSides.go] at h
    split at h
    · rename_i X Xs h1 h2
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨ih1, ih2⟩ := go_spec h2
      refine ⟨fun r' hr' => ?_, fun X' hX' => ?_⟩
      · rcases List.mem_cons.mp hr' with rfl | hr'
        · exact ⟨X, List.mem_cons_self, h1⟩
        · obtain ⟨Y, hY, hY'⟩ := ih1 r' hr'
          exact ⟨Y, List.mem_cons_of_mem _ hY, hY'⟩
      · rcases List.mem_cons.mp hX' with rfl | hX'
        · exact ⟨r, List.mem_cons_self, h1⟩
        · obtain ⟨r', hr', h'⟩ := ih2 X' hX'
          exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩
    · simp at h

/-! ## Paths along kept bonds -/

theorem exists_edge_of_adj {l : Edges} {b c : ℕ} (h : Adj l b c) : ∃ e ∈ l, isPair b c e = true := by
  unfold Adj mult at h
  obtain ⟨e, he⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero h)
  exact ⟨e, (List.mem_filter.mp he).1, (List.mem_filter.mp he).2⟩

theorem rtg_const {l : Edges} {Q : ℕ → Prop} (hl : ∀ e ∈ l, (Q e.1 ↔ Q e.2)) {x y : ℕ}
    (h : Relation.ReflTransGen (Adj l) x y) : (Q x ↔ Q y) := by
  induction h with
  | refl => exact Iff.rfl
  | @tail b c _ hbc ih =>
    obtain ⟨e, he, hp⟩ := exists_edge_of_adj hbc
    rcases (isPair_iff b c e).mp hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [ih, ← h1, ← h2]; exact hl e he
    · rw [ih, ← h1, ← h2]; exact (hl e he).symm

/-! ## Cuts as crossing bond copies -/

theorem sum_mult_cross (es : Edges) (A B : Finset ℕ) (hAB : Disjoint A B) :
    ∑ a ∈ A, ∑ b ∈ B, mult es a b =
      (es.filter fun e => decide ((e.1 ∈ A ∧ e.2 ∈ B) ∨ (e.2 ∈ A ∧ e.1 ∈ B))).length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have hz : ∀ a b, isPair a b e = true → (a = e.1 ∧ b = e.2) ∨ (a = e.2 ∧ b = e.1) := by
      intro a b h
      rcases (isPair_iff a b e).mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
    have hsum : ∑ a ∈ A, ∑ b ∈ B, (if isPair a b e = true then 1 else 0) =
        if (e.1 ∈ A ∧ e.2 ∈ B) ∨ (e.2 ∈ A ∧ e.1 ∈ B) then 1 else 0 := by
      by_cases h1 : e.1 ∈ A ∧ e.2 ∈ B
      · rw [if_pos (Or.inl h1), Finset.sum_eq_single e.1, Finset.sum_eq_single e.2,
          if_pos ((isPair_iff _ _ _).mpr (Or.inl ⟨rfl, rfl⟩))]
        · intro b hb hne
          rw [if_neg]
          intro h
          rcases hz _ b h with ⟨-, h'⟩ | ⟨-, h'⟩
          · exact hne h'
          · exact Finset.disjoint_left.mp hAB h1.1 (by rw [← h']; exact hb)
        · intro h; exact absurd h1.2 h
        · intro a ha hne
          apply Finset.sum_eq_zero
          intro b hb
          rw [if_neg]
          intro h
          rcases hz a b h with ⟨h', -⟩ | ⟨-, h'⟩
          · exact hne h'
          · exact Finset.disjoint_left.mp hAB h1.1 (by rw [← h']; exact hb)
        · intro h; exact absurd h1.1 h
      · by_cases h2 : e.2 ∈ A ∧ e.1 ∈ B
        · rw [if_pos (Or.inr h2), Finset.sum_eq_single e.2, Finset.sum_eq_single e.1,
            if_pos ((isPair_iff _ _ _).mpr (Or.inr ⟨rfl, rfl⟩))]
          · intro b hb hne
            rw [if_neg]
            intro h
            rcases hz _ b h with ⟨-, h'⟩ | ⟨-, h'⟩
            · exact Finset.disjoint_left.mp hAB h2.1 (by rw [← h']; exact hb)
            · exact hne h'
          · intro h; exact absurd h2.2 h
          · intro a ha hne
            apply Finset.sum_eq_zero
            intro b hb
            rw [if_neg]
            intro h
            rcases hz a b h with ⟨h', -⟩ | ⟨h', -⟩
            · exact Finset.disjoint_left.mp hAB ha (by rw [h']; exact h2.2)
            · exact hne h'
          · intro h; exact absurd h2.1 h
        · rw [if_neg (by tauto)]
          apply Finset.sum_eq_zero
          intro a ha
          apply Finset.sum_eq_zero
          intro b hb
          rw [if_neg]
          intro h
          rcases hz a b h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h1 ⟨ha, hb⟩
          · exact h2 ⟨ha, hb⟩
    simp only [mult_cons, Finset.sum_add_distrib, ih, hsum, List.filter_cons]
    by_cases hd : (e.1 ∈ A ∧ e.2 ∈ B) ∨ (e.2 ∈ A ∧ e.1 ∈ B) <;> simp [hd] <;> omega

variable {V : Type*} [DecidableEq V]

/-- L1's `cut` as the number of bond copies of the instance crossing `X`. -/
theorem cut_eq_cross {G : UMultigraph V} {es : Edges} (φ : Iso G es) {X : Finset V} (hX : X ⊆ G.verts) :
    cut G X = (es.filter fun e => decide (φ.g e.1 ∈ X ↔ φ.g e.2 ∉ X)).length := by
  have hinj := φ.f_injOn
  have hs : ∑ u ∈ X, ∑ w ∈ G.verts \ X, G.mult s(u, w) =
      ∑ a ∈ X.image φ.f, ∑ b ∈ (G.verts \ X).image φ.f, mult es a b := by
    rw [Finset.sum_image (fun x hx y hy h => hinj (hX hx) (hX hy) h)]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_image (fun x hx y hy h => hinj (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hy).1 h)]
    apply Finset.sum_congr rfl
    intro q hq
    exact φ.mult_eq p (hX hp) q (Finset.mem_sdiff.mp hq).1
  have hdisj : Disjoint (X.image φ.f) ((G.verts \ X).image φ.f) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, hpq⟩ := Finset.mem_image.mp hb
    rw [Finset.mem_sdiff] at hq
    have := hinj hq.1 (hX hp) hpq
    exact hq.2 (this ▸ hp)
  have m : ∀ z, InEnds es z → (z ∈ X.image φ.f ↔ φ.g z ∈ X) ∧ (z ∈ (G.verts \ X).image φ.f ↔ φ.g z ∉ X) := by
    intro z hz
    refine ⟨⟨fun h => ?_, fun h => Finset.mem_image.mpr ⟨φ.g z, h, φ.fg z hz⟩⟩,
      ⟨fun h => ?_, fun h => Finset.mem_image.mpr ⟨φ.g z, Finset.mem_sdiff.mpr ⟨φ.gv z hz, h⟩, φ.fg z hz⟩⟩⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
      rwa [φ.gf p (hX hp)]
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
      rw [Finset.mem_sdiff] at hp
      rw [φ.gf p hp.1]; exact hp.2
  unfold cut
  rw [hs, sum_mult_cross es _ _ hdisj]
  congr 1
  apply List.filter_congr
  intro e he
  have h1 : InEnds es e.1 := ⟨e, he, Or.inl rfl⟩
  have h2 : InEnds es e.2 := ⟨e, he, Or.inr rfl⟩
  rw [decide_eq_decide, (m _ h1).1, (m _ h1).2, (m _ h2).1, (m _ h2).2]
  tauto

/-! ## Pieces from sides -/

/-- **Same sides ⇒ same piece.** -/
theorem samePiece_of_sides {G : UMultigraph V} {es : Edges} (φ : Iso G es) {sides : List ℕ}
    (hs : allSides (maskOf es) es = some sides) {u w : ℕ} (hu : InEnds es u) (hw : InEnds es w)
    (hu32 : u < 32) (hw32 : w < 32) (hsame : ∀ X ∈ sides, mem u X = mem w X) :
    SamePieceU G (φ.g u) (φ.g w) := by
  intro X hX hcut
  classical
  rw [cut_eq_cross φ hX] at hcut
  obtain ⟨p, hp, hp2⟩ := mem_splits2_filter _ hcut
  obtain ⟨h1, -⟩ := go_spec hs
  obtain ⟨Xr, hXr, hside⟩ := h1 p.2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
  -- kept bonds do not cross `X`
  have hkept : ∀ e ∈ p.2, ((φ.g e.1 ∈ X) ↔ (φ.g e.2 ∈ X)) := by
    intro e he
    rw [hp2] at he
    have := (List.mem_filter.mp he).2
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
    tauto
  have hconst : ∀ x y, Relation.ReflTransGen (Adj p.2) x y → (φ.g x ∈ X ↔ φ.g y ∈ X) :=
    fun x y h => rtg_const (Q := fun z => φ.g z ∈ X) hkept h
  obtain ⟨⟨s, hsX⟩, hY⟩ := sideOf_spec hside
  have huV : mem u (maskOf es) = true := mem_maskOf.mpr hu
  have hwV : mem w (maskOf es) = true := mem_maskOf.mpr hw
  rcases hY with hY | ⟨⟨t, htY⟩, -⟩
  · -- one side covers everything
    have cov : ∀ v < 32, mem v (maskOf es) = true → mem v Xr = true := by
      intro v hv hvV
      have := hY v hv
      rw [mem_sdiff, hvV, Bool.true_and, Bool.not_eq_false'] at this
      exact this
    rw [← hconst _ _ (hsX u (cov u hu32 huV)), hconst _ _ (hsX w (cov w hw32 hwV))]
  · have hsame' := hsame Xr hXr
    by_cases huX : mem u Xr = true
    · have hwX : mem w Xr = true := hsame' ▸ huX
      rw [← hconst _ _ (hsX u huX), hconst _ _ (hsX w hwX)]
    · have hwX : ¬ mem w Xr = true := hsame' ▸ huX
      have huY : mem u (sdiff (maskOf es) Xr) = true := by simp_all
      have hwY : mem w (sdiff (maskOf es) Xr) = true := by simp_all
      rw [← hconst _ _ (htY u huY), hconst _ _ (htY w hwY)]

/-- **Separated by a side ⇒ different pieces.** -/
theorem not_samePiece_of_side {G : UMultigraph V} {es : Edges} (φ : Iso G es) {sides : List ℕ}
    (hs : allSides (maskOf es) es = some sides) {u w : ℕ} (hu : InEnds es u) (hw : InEnds es w)
    (hu32 : u < 32) (hw32 : w < 32) {Xr : ℕ} (hXr : Xr ∈ sides) (hdiff : mem u Xr ≠ mem w Xr) :
    ¬ SamePieceU G (φ.g u) (φ.g w) := by
  classical
  obtain ⟨-, h2⟩ := go_spec hs
  obtain ⟨r, hr, hside⟩ := h2 Xr hXr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  obtain ⟨hlen, hperm⟩ := splits2_spec hp
  obtain ⟨-, hY⟩ := sideOf_spec hside
  have huV : mem u (maskOf es) = true := mem_maskOf.mpr hu
  have hwV : mem w (maskOf es) = true := mem_maskOf.mpr hw
  rcases hY with hY | ⟨-, hcl⟩
  · exfalso
    have cov : ∀ v < 32, mem v (maskOf es) = true → mem v Xr = true := by
      intro v hv hvV
      have := hY v hv
      rw [mem_sdiff, hvV, Bool.true_and, Bool.not_eq_false'] at this
      exact this
    exact hdiff (by rw [cov u hu32 huV, cov w hw32 hwV])
  · let X : Finset V := G.verts.filter fun v => mem (φ.f v) Xr = true
    have hXG : X ⊆ G.verts := Finset.filter_subset _ _
    have hmemX : ∀ z, InEnds es z → (φ.g z ∈ X ↔ mem z Xr = true) := by
      intro z hz
      simp only [X, Finset.mem_filter, φ.fg z hz]
      exact ⟨fun h => h.2, fun h => ⟨φ.gv z hz, h⟩⟩
    have hcut : cut G X ≤ 2 := by
      rw [cut_eq_cross φ hXG]
      have hP := (hperm.filter (fun e => decide (φ.g e.1 ∈ X ↔ φ.g e.2 ∉ X))).length_eq
      rw [← hP, List.filter_append, List.length_append]
      have hkept : (p.2.filter fun e => decide (φ.g e.1 ∈ X ↔ φ.g e.2 ∉ X)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro e he
        have hees : e ∈ es := hperm.subset (List.mem_append_right _ he)
        have h1 : InEnds es e.1 := ⟨e, hees, Or.inl rfl⟩
        have h2 : InEnds es e.2 := ⟨e, hees, Or.inr rfl⟩
        have hc := List.all_eq_true.mp hcl e he
        rw [beq_iff_eq] at hc
        rw [decide_eq_true_iff, hmemX _ h1, hmemX _ h2, hc]
        tauto
      rw [hkept, List.length_nil]
      have := List.length_filter_le (fun e => decide (φ.g e.1 ∈ X ↔ φ.g e.2 ∉ X)) p.1
      omega
    intro hsp
    have := hsp X hXG hcut
    rw [hmemX _ hu, hmemX _ hw] at this
    exact hdiff (Bool.eq_iff_iff.mpr this)

end WaveTurbulence.TVine.Checker
