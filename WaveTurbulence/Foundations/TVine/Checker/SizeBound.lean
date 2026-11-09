/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.RungLadder

/-!
# N2 Lemma 1.8: `|B| ≤ 11 + 2 D(B)`

N2's proof, on the generated family (`generation`): every double rung of a ladder is a deletable rung of the
block unless a later operation sits on a copy of its double bond. The joints sit on the triple bonds (the block
has no triple bond), so they hit at most one rung (one ladder) or none (two ladders); the second ladder's start
`ℓ'` hits at most one rung of the first ladder; the first rung of the second ladder needs `ℓ'` of multiplicity 2,
and when `ℓ'` is single it is not a rung of the first ladder. In every case `D ≥ k + k' − 3`, while the block has
at most `5 + 2(k + k')` atoms.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine Core

universe u

/-! ## Deletable rungs on the instance side, and their transport -/

/-- `n, n + 1` is a deletable rung of `ofEdges es` with joints `J₁, J₂`. -/
def DelL (es : Edges) (J₁ J₂ n : ℕ) : Prop :=
  ∃ xm xp ym yp Km Kp, RungL es n (n + 1) xm xp ym yp Km Kp ∧ n ≠ J₁ ∧ n ≠ J₂ ∧ n + 1 ≠ J₁ ∧ n + 1 ≠ J₂ ∧
    (∃ z ∈ Km, z ≠ J₁ ∧ z ≠ J₂) ∧ (∃ z ∈ Kp, z ≠ J₁ ∧ z ≠ J₂)

variable {V : Type*} [DecidableEq V]

theorem rtg_lift {α β : Type*} {r : α → α → Prop} {r' : β → β → Prop} (F : α → β)
    (hF : ∀ p q, r p q → r' (F p) (F q)) {a b : α} (h : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen r' (F a) (F b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hF _ _ hbc)

theorem isRungAt_transport {G : UMultigraph V} {es : Edges} (φ : Iso G es) {a b xm xp ym yp : ℕ}
    {Km Kp : Finset ℕ} (h : RungL es a b xm xp ym yp Km Kp) :
    IsRungAt G (φ.g a) (φ.g b) (φ.g xm) (φ.g xp) (φ.g ym) (φ.g yp) (Km.image φ.g) (Kp.image φ.g) := by
  have ends : ∀ z, z ∈ Km ∨ z ∈ Kp → InEnds es z := fun z hz => (RungL.mem_ends h hz).1
  have ae := RungL.a_ends h; have be := RungL.b_ends h
  have gne : ∀ {x y}, InEnds es x → InEnds es y → x ≠ y → φ.g x ≠ φ.g y := fun hx hy hxy => φ.g_ne hx hy hxy
  have mg : ∀ {x y}, InEnds es x → InEnds es y → G.mult s(φ.g x, φ.g y) = (ofEdges es).mult s(x, y) :=
    fun hx hy => by rw [φ.mult_g hx hy, ofEdges_mult]
  have xme := ends xm (Or.inl h.xm_mem); have xpe := ends xp (Or.inr h.xp_mem)
  have yme := ends ym (Or.inl h.ym_mem); have ype := ends yp (Or.inr h.yp_mem)
  have memK : ∀ {K : Finset ℕ}, (∀ z ∈ K, InEnds es z) → ∀ v, v ∈ K.image φ.g ↔ v ∈ G.verts ∧ φ.f v ∈ K := by
    intro K hK v
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨φ.gv z (hK z hz), by rw [φ.fg z (hK z hz)]; exact hz⟩
    · rintro ⟨hv, hz⟩; exact ⟨φ.f v, hz, φ.gf v hv⟩
  have hKm : ∀ z ∈ Km, InEnds es z := fun z hz => ends z (Or.inl hz)
  have hKp : ∀ z ∈ Kp, InEnds es z := fun z hz => ends z (Or.inr hz)
  have conn : ∀ {K : Finset ℕ}, (∀ z ∈ K, InEnds es z) → ConnOn (ofEdges es) K → ConnOn G (K.image φ.g) := by
    intro K hK hc u hu w hw
    rw [memK hK] at hu hw
    have := hc _ hu.2 _ hw.2
    rw [← φ.gf u hu.1, ← φ.gf w hw.1]
    refine rtg_lift φ.g (fun p q hpq => ⟨(memK hK _).mpr ⟨φ.gv p (hK p hpq.1), by rw [φ.fg p (hK p hpq.1)]; exact hpq.1⟩,
      (memK hK _).mpr ⟨φ.gv q (hK q hpq.2.1), by rw [φ.fg q (hK q hpq.2.1)]; exact hpq.2.1⟩,
      by rw [mg (hK p hpq.1) (hK q hpq.2.1)]; exact hpq.2.2⟩) this
  refine ⟨gne ae be h.ne, φ.gv a ae, φ.gv b be, by rw [mg ae be]; exact h.mult_ab, ?_, ?_, conn hKm h.connm,
    conn hKp h.connp, ?_, Finset.mem_image_of_mem _ h.xm_mem, Finset.mem_image_of_mem _ h.xp_mem,
    Finset.mem_image_of_mem _ h.ym_mem, Finset.mem_image_of_mem _ h.yp_mem, by rw [mg ae xme]; exact h.a_xm,
    by rw [mg ae xpe]; exact h.a_xp, by rw [mg be yme]; exact h.b_ym, by rw [mg be ype]; exact h.b_yp, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro v hv hv'
    rw [memK hKm] at hv; rw [memK hKp] at hv'
    exact Finset.disjoint_left.mp h.disj hv.2 hv'.2
  · ext v
    rw [Finset.mem_union, memK hKm, memK hKp]
    simp only [Finset.mem_erase]
    have hu := congrArg (φ.f v ∈ ·) h.union
    simp only [Finset.mem_union, Finset.mem_erase, mem_ofEdges_verts] at hu
    constructor
    · rintro (⟨hv, hz⟩ | ⟨hv, hz⟩)
      · obtain ⟨h1, h2, -⟩ := hu.mp (Or.inl hz)
        exact ⟨fun hh => h1 (by rw [hh, φ.fg b be]), fun hh => h2 (by rw [hh, φ.fg a ae]), hv⟩
      · obtain ⟨h1, h2, -⟩ := hu.mp (Or.inr hz)
        exact ⟨fun hh => h1 (by rw [hh, φ.fg b be]), fun hh => h2 (by rw [hh, φ.fg a ae]), hv⟩
    · rintro ⟨h1, h2, hv⟩
      have h1' : φ.f v ≠ b := fun hh => h1 (by rw [← φ.gf v hv, hh])
      have h2' : φ.f v ≠ a := fun hh => h2 (by rw [← φ.gf v hv, hh])
      rcases hu.mpr ⟨h1', h2', φ.fv v hv⟩ with hz | hz
      · exact Or.inl ⟨hv, hz⟩
      · exact Or.inr ⟨hv, hz⟩
  · intro u hu w hw
    rw [memK hKm] at hu; rw [memK hKp] at hw
    rw [φ.mult_eq u hu.1 w hw.1, ← ofEdges_mult]
    exact h.noBond _ hu.2 _ hw.2
  · intro z h1 h2 h3
    by_cases hz : z ∈ G.verts
    · rw [← φ.gf z hz, mg ae (φ.fv z hz)]
      refine h.a_other _ (fun hh => h1 ?_) (fun hh => h2 ?_) (fun hh => h3 ?_) <;> rw [← φ.gf z hz, hh]
    · exact φ.mult_eq_zero_of_not_mem' hz
  · intro z h1 h2 h3
    by_cases hz : z ∈ G.verts
    · rw [← φ.gf z hz, mg be (φ.fv z hz)]
      refine h.b_other _ (fun hh => h1 ?_) (fun hh => h2 ?_) (fun hh => h3 ?_) <;> rw [← φ.gf z hz, hh]
    · exact φ.mult_eq_zero_of_not_mem' hz

/-- A deletable rung of the instance gives a deletable rung of `G`. -/
theorem isDeletable_of_delL {G : UMultigraph V} {es : Edges} (φ : Iso G es) {j₁ j₂ : V} {J₁ J₂ : ℕ}
    (hj₁ : j₁ ∈ G.verts) (hj₂ : j₂ ∈ G.verts)
    (hJ : (φ.f j₁ = J₁ ∧ φ.f j₂ = J₂) ∨ (φ.f j₁ = J₂ ∧ φ.f j₂ = J₁)) {n : ℕ} (h : DelL es J₁ J₂ n) :
    IsDeletable G j₁ j₂ (φ.g n) (φ.g (n + 1)) := by
  obtain ⟨xm, xp, ym, yp, Km, Kp, hR, n1, n2, n3, n4, ⟨z, hz, z1, z2⟩, ⟨z', hz', z1', z2'⟩⟩ := h
  have hgj : ∀ m, InEnds es m → m ≠ J₁ → m ≠ J₂ → φ.g m ≠ j₁ ∧ φ.g m ≠ j₂ := by
    intro m hm h1 h2
    have e1 := φ.fv j₁ hj₁; have e2 := φ.fv j₂ hj₂
    rcases hJ with ⟨hf1, hf2⟩ | ⟨hf1, hf2⟩
    · exact ⟨fun hh => h1 (by rw [← hf1, ← hh, φ.fg m hm]), fun hh => h2 (by rw [← hf2, ← hh, φ.fg m hm])⟩
    · exact ⟨fun hh => h2 (by rw [← hf1, ← hh, φ.fg m hm]), fun hh => h1 (by rw [← hf2, ← hh, φ.fg m hm])⟩
  have ae := RungL.a_ends hR; have be := RungL.b_ends hR
  refine ⟨_, _, _, _, _, _, ⟨isRungAt_transport φ hR, (hgj n ae n1 n2).1, (hgj n ae n1 n2).2,
    (hgj _ be n3 n4).1, (hgj _ be n3 n4).2⟩, ?_⟩
  rintro (hc | hc)
  · have := hc (Finset.mem_image_of_mem φ.g hz)
    have hz'' := hgj z (RungL.mem_ends hR (Or.inl hz)).1 z1 z2
    simp only [Finset.mem_insert, Finset.mem_singleton] at this; tauto
  · have := hc (Finset.mem_image_of_mem φ.g hz')
    have hz'' := hgj z' (RungL.mem_ends hR (Or.inr hz')).1 z1' z2'
    simp only [Finset.mem_insert, Finset.mem_singleton] at this; tauto

/-- Counting: distinct deletable rungs of the instance bound `D(G)` from below. -/
theorem card_le_deletableCount {G : UMultigraph V} {es : Edges} (φ : Iso G es) {j₁ j₂ : V} {J₁ J₂ : ℕ}
    (hj₁ : j₁ ∈ G.verts) (hj₂ : j₂ ∈ G.verts)
    (hJ : (φ.f j₁ = J₁ ∧ φ.f j₂ = J₂) ∨ (φ.f j₁ = J₂ ∧ φ.f j₂ = J₁)) (T : Finset ℕ)
    (hT : ∀ n ∈ T, DelL es J₁ J₂ n) : T.card ≤ deletableCount G j₁ j₂ := by
  classical
  have ends : ∀ n ∈ T, InEnds es n ∧ InEnds es (n + 1) := by
    intro n hn
    obtain ⟨_, _, _, _, _, _, hR, -⟩ := hT n hn
    exact ⟨RungL.a_ends hR, RungL.b_ends hR⟩
  have hinj : Set.InjOn (fun n => s(φ.g n, φ.g (n + 1))) T := by
    intro n hn m hm hnm
    simp only at hnm
    rw [Sym2.eq_iff] at hnm
    rcases hnm with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact φ.g_injOn (ends n hn).1 (ends m hm).1 h1
    · have := φ.g_injOn (ends n hn).1 (ends m hm).2 h1
      have := φ.g_injOn (ends n hn).2 (ends m hm).1 h2
      omega
  rw [← Finset.card_image_of_injOn hinj]
  unfold deletableCount
  apply Finset.card_le_card
  intro z hz
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
  rw [Finset.mem_filter]
  refine ⟨Finset.mk_mem_sym2_iff.mpr ⟨φ.gv _ (ends n hn).1, φ.gv _ (ends n hn).2⟩, _, _, rfl, ?_⟩
  exact isDeletable_of_delL φ hj₁ hj₂ hJ (hT n hn)

/-- An isomorphism preserves the number of atoms. -/
theorem card_verts_iso {G : UMultigraph V} {es : Edges} (φ : Iso G es) :
    G.verts.card = (ofEdges es).verts.card := by
  have : G.verts.image φ.f = (ofEdges es).verts := by
    ext z
    rw [Finset.mem_image, mem_ofEdges_verts]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact φ.fv v hv
    · intro hz; exact ⟨φ.g z, φ.gv z hz, φ.fg z hz⟩
  rw [← this, Finset.card_image_of_injOn φ.f_injOn]

/-! ## Multiplicities in a block without triple bond -/

theorem multLe2_le {es : Edges} (h : multLe2 es = true) {u v : ℕ} (huv : mult es u v ≠ 0) : mult es u v ≤ 2 := by
  obtain ⟨e, he⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero huv)
  rw [List.mem_filter] at he
  have := List.all_eq_true.mp h e he.1
  have h2 : mult es e.1 e.2 ≤ 2 := by simpa using this
  rwa [mult_eq_count, ← (isPair_iff_sym2 u v e).mp he.2, ← mult_eq_count]

end WaveTurbulence.TVine.Checker
