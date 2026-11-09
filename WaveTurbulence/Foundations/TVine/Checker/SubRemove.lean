/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.SubFacts
public import WaveTurbulence.Foundations.TVine.Checker.Statement

/-!
# Soundness of the removal checks (M4 §8 F4 removal, F5)

* `connected_removeAllN_of_connB`: if the candidates `Cs` of a family `Us` of sub-objects (each member of `Us` has
  a candidate in `Cs` and conversely) pass `connB` after `removeAll`, then `removeAllN G Us` is connected;
* `mem_families`: every pairwise-disjoint sublist of the candidates is one of the enumerated `families`;
* `connected_removeAllN_family`: from `checkB` on every candidate and `familiesB`, every pairwise atom-disjoint
  family of sub-objects of `G` leaves `G` connected after removal (N2's semantics).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine WaveTurbulence.TVine.Core

/-! ## Bond lists -/

theorem mult_filter_sym {es : Edges} {q : ℕ × ℕ → Bool} (hq : ∀ a b, q (a, b) = q (b, a)) (a b : ℕ) :
    mult (es.filter q) a b = if q (a, b) then mult es a b else 0 := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have hp : isPair a b e = true → q e = q (a, b) := by
      intro h
      rcases (isPair_iff a b e).mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]
      · rw [hq, ← h1, ← h2]
    rw [List.filter_cons]
    split <;> rename_i he
    · rw [mult_cons, mult_cons, ih]
      by_cases hP : isPair a b e = true
      · rw [← hp hP, if_pos he, if_pos he]
      · simp [hP]
    · rw [ih, mult_cons]
      by_cases hP : isPair a b e = true
      · have : q (a, b) = false := by rw [← hp hP]; simpa using he
        simp [this]
      · simp [hP]

/-- The removed atoms of a family of candidates. -/
theorem mem_removed (z : ℕ) : ∀ (Cs : List Sub) (acc : ℕ),
    mem z (Cs.foldl (fun acc U => acc ||| sdiff U.S (bit U.k₁ ||| bit U.k₂)) acc) = true ↔
      mem z acc = true ∨ ∃ C ∈ Cs, mem z C.S = true ∧ C.k₁ ≠ z ∧ C.k₂ ≠ z
  | [], acc => by simp
  | C :: Cs, acc => by
    rw [List.foldl_cons, mem_removed z Cs]
    simp only [mem_or, mem_sdiff, mem_bit, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      Bool.or_eq_false_iff, decide_eq_false_iff_not, List.mem_cons, exists_eq_or_imp, ne_eq]
    tauto

theorem removeAll_fst (V : ℕ) (es : Edges) (Cs : List Sub) :
    (removeAll V es Cs).1 = sdiff V (Cs.foldl (fun acc U => acc ||| sdiff U.S (bit U.k₁ ||| bit U.k₂)) 0) := rfl

theorem removeAll_snd (V : ℕ) (es : Edges) (Cs : List Sub) :
    (removeAll V es Cs).2 = es.filter fun e => Cs.all fun U => !(mem e.1 U.S && mem e.2 U.S) := rfl

/-! ## Families -/

theorem mem_families : ∀ {Cs F : List Sub}, F.Sublist Cs →
    F.Pairwise (fun C D => (C.S &&& D.S).beq 0 = true) → F ∈ families Cs
  | [], F, h, _ => by rw [List.sublist_nil.mp h]; simp [families]
  | C :: Cs, F, h, hp => by
    simp only [families, List.mem_append, List.mem_map, List.mem_filter]
    cases h with
    | cons _ h => exact Or.inl (mem_families h hp)
    | cons_cons _ h =>
      rw [List.pairwise_cons] at hp
      exact Or.inr ⟨_, ⟨mem_families h hp.2, List.all_eq_true.mpr fun W hW => hp.1 W hW⟩, rfl⟩

theorem lt_of_mem_subObjects {V : ℕ} {es : Edges} {C : Sub} (h : C ∈ subObjects V es) : C.k₁ < C.k₂ := by
  simp only [subObjects, List.mem_flatMap, List.mem_filter] at h
  obtain ⟨k₁, -, k₂, ⟨-, hlt⟩, m, -, hC⟩ := h
  split at hC
  · simp at hC
  · obtain ⟨hC, -⟩ := List.mem_filter.mp hC
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hC
    simpa using hlt

theorem pairwise_mem_ne {α : Type*} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R → ∀ {a b : α},
    a ∈ l → b ∈ l → a ≠ b → R a b ∨ R b a
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: l, h, a, b, ha, hb, hab => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with h1 | ha <;> rcases List.mem_cons.mp hb with h2 | hb
    · exact absurd (h1.trans h2.symm) hab
    · exact Or.inl (h1 ▸ h.1 b hb)
    · exact Or.inr (h2 ▸ h.1 a ha)
    · exact pairwise_mem_ne h.2 ha hb hab

variable {V : Type*} [DecidableEq V]

theorem innerAll_mem_iff {Us : List (SubObj V)} {v : V} : v ∈ innerAll Us ↔ ∃ U ∈ Us, v ∈ U.inner := by
  induction Us with
  | nil => simp [innerAll]
  | cons U Us ih =>
    show v ∈ U.inner ∪ innerAll Us ↔ _
    rw [Finset.mem_union, ih]; simp

theorem removeAllN_verts (G : UMultigraph V) (Us : List (SubObj V)) :
    (removeAllN G Us).verts = G.verts \ innerAll Us := rfl

theorem removeAllN_mult (G : UMultigraph V) (Us : List (SubObj V)) (e : Sym2 V) :
    (removeAllN G Us).mult e =
      if e ∈ (G.verts \ innerAll Us).sym2 ∧ ∀ U ∈ Us, e ∉ U.atoms.sym2 then G.mult e else 0 := rfl

theorem connected_removeAllN_nil {G : UMultigraph V} (h : Connected G) : Connected (removeAllN G []) := by
  have hv : (removeAllN G []).verts = G.verts := by simp [removeAllN_verts, innerAll]
  intro u hu w hw
  rw [hv] at hu hw
  show Relation.ReflTransGen (AdjIn (removeAllN G []) (removeAllN G []).verts) u w
  rw [hv]
  have step : ∀ a b, AdjIn G G.verts a b → AdjIn (removeAllN G []) G.verts a b := by
    rintro a b ⟨ha, hb, hab⟩
    refine ⟨ha, hb, ?_⟩
    rw [removeAllN_mult, if_pos ⟨by simp [innerAll, Finset.mk_mem_sym2_iff, ha, hb], by simp⟩]
    exact hab
  have gen : ∀ x y, Relation.ReflTransGen (AdjIn G G.verts) x y →
      Relation.ReflTransGen (AdjIn (removeAllN G []) G.verts) x y := by
    intro x y hxy
    induction hxy with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.tail (step _ _ hbc)
  exact gen u w (h u hu w hw)

omit [DecidableEq V] in
/-- Two candidates of the same sub-object (joints in increasing order) are equal. -/
theorem cand_eq {G : UMultigraph V} {es : Edges} {φ : Iso G es} {U : SubObj V} {C D : Sub}
    (hk₁ : U.k₁ ∈ G.verts) (hk₂ : U.k₂ ∈ G.verts) (hne : U.k₁ ≠ U.k₂) (hC : CandOf φ U C)
    (hD : CandOf φ U D) (hCl : C.k₁ < C.k₂) (hDl : D.k₁ < D.k₂) : C = D := by
  have hS : C.S = D.S := Nat.eq_of_testBit_eq fun i =>
    Bool.eq_iff_iff.mpr ((hC.memS i).trans (hD.memS i).symm)
  have hf : φ.f U.k₁ ≠ φ.f U.k₂ := fun h => hne (φ.f_injOn hk₁ hk₂ h)
  have hk : C.k₁ = D.k₁ ∧ C.k₂ = D.k₂ := by
    rcases hC.joints with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hD.joints with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;> omega
  have hh : C.hyper = D.hyper := hC.hyper.trans hD.hyper.symm
  cases C; cases D
  simp only [Sub.mk.injEq]
  exact ⟨hS, hk.1, hk.2, hh⟩

/-! ## Removal -/

/-- **Removal soundness.** -/
theorem connected_removeAllN_of_connB {G : UMultigraph V} {es : Edges} (φ : Iso G es)
    (hdeg : ∀ v ∈ G.verts, Core.deg G v ≤ 4) {Us : List (SubObj V)} (hUs : ∀ U ∈ Us, IsSubObjU G U)
    {Cs : List Sub} (h1 : ∀ U ∈ Us, ∃ C ∈ Cs, CandOf φ U C) (h2 : ∀ C ∈ Cs, ∃ U ∈ Us, CandOf φ U C)
    (hb : connB (removeAll (maskOf es) es Cs).1 (removeAll (maskOf es) es Cs).2 = true) :
    Connected (removeAllN G Us) := by
  have hRv := removeAllN_verts G Us
  -- the kept atoms are kept by the checker
  have hvert : ∀ u ∈ (removeAllN G Us).verts, mem (φ.f u) (removeAll (maskOf es) es Cs).1 = true := by
    intro u hu
    rw [hRv, Finset.mem_sdiff, innerAll_mem_iff] at hu
    obtain ⟨huG, hnot⟩ := hu
    rw [removeAll_fst, mem_sdiff, mem_maskOf.mpr (φ.fv u huG), Bool.true_and, Bool.not_eq_true']
    by_contra hI
    rw [Bool.not_eq_false] at hI
    rcases (mem_removed _ Cs 0).mp hI with h | ⟨C, hC, hm, hk1, hk2⟩
    · simp [mem] at h
    · obtain ⟨U, hU, hCU⟩ := h2 C hC
      apply hnot ⟨U, hU, ?_⟩
      have hm' := (hCU.memS _).mp hm
      rw [φ.gf u huG] at hm'
      simp only [SubObj.inner, Finset.mem_erase]
      refine ⟨fun h => ?_, fun h => ?_, hm'.2⟩
      · subst h
        rcases hCU.joints with ⟨e1, e2⟩ | ⟨e1, e2⟩
        exacts [hk2 e2, hk1 e1]
      · subst h
        rcases hCU.joints with ⟨e1, e2⟩ | ⟨e1, e2⟩
        exacts [hk1 e1, hk2 e2]
  -- the kept bonds are bonds of the removal
  have hedge : ∀ a b, Adj (removeAll (maskOf es) es Cs).2 a b →
      AdjIn (removeAllN G Us) (removeAllN G Us).verts (φ.g a) (φ.g b) := by
    intro a b hab
    unfold Adj at hab
    rw [removeAll_snd, mult_filter_sym (fun x y => by simp only [Bool.and_comm])] at hab
    split_ifs at hab with hq
    · have ha := (inEnds_of_mult_ne_zero hab).1
      have hb' := (inEnds_of_mult_ne_zero hab).2
      have hG : G.mult s(φ.g a, φ.g b) ≠ 0 := by rw [φ.mult_g ha hb']; exact hab
      have hout : ∀ U ∈ Us, ¬ (φ.g a ∈ U.atoms ∧ φ.g b ∈ U.atoms) := by
        rintro U hU ⟨hau, hbu⟩
        obtain ⟨C, hC, hCU⟩ := h1 U hU
        have := List.all_eq_true.mp hq C hC
        rw [(hCU.memS a).mpr ⟨ha, hau⟩, (hCU.memS b).mpr ⟨hb', hbu⟩] at this
        simp at this
      have hnin : ∀ x y, G.mult s(x, y) ≠ 0 → (∀ U ∈ Us, ¬ (x ∈ U.atoms ∧ y ∈ U.atoms)) →
          x ∉ innerAll Us := by
        intro x y hxy hxyU hx
        obtain ⟨U, hU, hxI⟩ := innerAll_mem_iff.mp hx
        have hyU := inner_closed hdeg (hUs U hU) hxI hxy
        have hxU : x ∈ U.atoms := by simp only [SubObj.inner, Finset.mem_erase] at hxI; exact hxI.2.2
        exact hxyU U hU ⟨hxU, hyU⟩
      have haR : φ.g a ∈ (removeAllN G Us).verts := by
        rw [hRv, Finset.mem_sdiff]; exact ⟨φ.gv a ha, hnin _ _ hG hout⟩
      have hbR : φ.g b ∈ (removeAllN G Us).verts := by
        rw [hRv, Finset.mem_sdiff]
        exact ⟨φ.gv b hb', hnin _ (φ.g a) (by rwa [Sym2.eq_swap]) fun U hU h => hout U hU ⟨h.2, h.1⟩⟩
      refine ⟨haR, hbR, ?_⟩
      rw [removeAllN_mult, if_pos ⟨Finset.mk_mem_sym2_iff.mpr ⟨hRv ▸ haR, hRv ▸ hbR⟩,
        fun U hU h => hout U hU (Finset.mk_mem_sym2_iff.mp h)⟩]
      exact hG
    · exact absurd rfl hab
  intro u hu w hw
  have hp := connB_sound hb (hvert u hu) (hvert w hw)
  have gen : ∀ x y, Relation.ReflTransGen (Adj (removeAll (maskOf es) es Cs).2) x y →
      Relation.ReflTransGen (AdjIn (removeAllN G Us) (removeAllN G Us).verts) (φ.g x) (φ.g y) := by
    intro x y hxy
    induction hxy with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.tail (hedge _ _ hbc)
  have key := gen _ _ hp
  have huG : u ∈ G.verts := (Finset.mem_sdiff.mp (hRv ▸ hu)).1
  have hwG : w ∈ G.verts := (Finset.mem_sdiff.mp (hRv ▸ hw)).1
  rwa [φ.gf u huG, φ.gf w hwG] at key

/-- **Families soundness**: every family of pairwise atom-disjoint sub-objects leaves `G` connected. -/
theorem connected_removeAllN_family {G : UMultigraph V} {es : Edges} (φ : Iso G es)
    (hdeg : ∀ v ∈ G.verts, Core.deg G v ≤ 4) (hlt : ∀ z, InEnds es z → z < 32)
    (hok : compsOKAll (maskOf es) es = true) (hconn : Connected G)
    (hsingle : ∀ C ∈ subObjects (maskOf es) es, C.checkB (maskOf es) es = true)
    (hfam : familiesB (maskOf es) es (subObjects (maskOf es) es) = true)
    {Us : List (SubObj V)} (hUs : ∀ U ∈ Us, IsSubObjU G U)
    (hpw : Us.Pairwise (fun U U' => Disjoint U.atoms U'.atoms)) : Connected (removeAllN G Us) := by
  classical
  let P : Sub → Prop := fun C => ∃ U ∈ Us, CandOf φ U C
  obtain ⟨F, hF⟩ : ∃ F, F = ((subObjects (maskOf es) es).filter fun C => decide (P C)).dedup := ⟨_, rfl⟩
  have hFsub : F.Sublist (subObjects (maskOf es) es) := hF ▸ (List.dedup_sublist _).trans List.filter_sublist
  have hmemF : ∀ C, C ∈ F ↔ C ∈ subObjects (maskOf es) es ∧ P C := by
    intro C; rw [hF, List.mem_dedup, List.mem_filter, decide_eq_true_iff]
  have h1 : ∀ U ∈ Us, ∃ C ∈ F, CandOf φ U C := by
    intro U hU
    obtain ⟨C, hC, hCU⟩ := exists_cand φ hdeg hlt hok (hUs U hU)
    exact ⟨C, (hmemF C).mpr ⟨hC, U, hU, hCU⟩, hCU⟩
  have h2 : ∀ C ∈ F, ∃ U ∈ Us, CandOf φ U C := fun C hC => ((hmemF C).mp hC).2
  have hpair : F.Pairwise (fun C D => (C.S &&& D.S).beq 0 = true) := by
    apply (hF ▸ List.nodup_dedup _ : F.Nodup).pairwise_of_forall_ne
    intro C hC D hD hCD
    obtain ⟨hCc, U, hU, hCU⟩ := (hmemF C).mp hC
    obtain ⟨hDc, U', hU', hDU⟩ := (hmemF D).mp hD
    by_cases hUU : U = U'
    · subst hUU
      obtain ⟨hk₁, hk₂, hne, -⟩ := (hUs U hU).2.2
      rw [core_verts] at hk₁ hk₂
      have hsub := (hUs U hU).1.1
      exact absurd (cand_eq (hsub hk₁) (hsub hk₂) hne hCU hDU (lt_of_mem_subObjects hCc)
        (lt_of_mem_subObjects hDc)) hCD
    · have hdisj : Disjoint U.atoms U'.atoms := by
        rcases pairwise_mem_ne hpw hU hU' hUU with h | h
        exacts [h, h.symm]
      rw [nat_beq_eq_decide, decide_eq_true_iff]
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and, Nat.zero_testBit]
      cases hc : C.S.testBit i
      · rfl
      · cases hd : D.S.testBit i
        · rfl
        · exfalso
          have a1 := (hCU.memS i).mp hc
          have a2 := (hDU.memS i).mp hd
          exact Finset.disjoint_left.mp hdisj a1.2 a2.2
  have hmem := mem_families hFsub hpair
  have hb : connB (removeAll (maskOf es) es F).1 (removeAll (maskOf es) es F).2 = true ∨ F = [] := by
    match F, hFsub, hmem with
    | [], _, _ => exact Or.inr rfl
    | [C], hs, _ =>
      left
      have := hsingle C (hs.subset (by simp))
      unfold Sub.checkB at this
      simp only [Bool.and_eq_true] at this
      exact this.2
    | C :: D :: rest, _, hm =>
      left
      have := List.all_eq_true.mp hfam _ hm
      rw [Bool.or_eq_true] at this
      rcases this with h | h
      · simp at h
      · exact h
  rcases hb with hb | hnil
  · exact connected_removeAllN_of_connB φ hdeg hUs h1 h2 hb
  · have : Us = [] := List.eq_nil_iff_forall_not_mem.mpr fun U hU => by
      obtain ⟨C, hC, -⟩ := h1 U hU
      rw [hnil] at hC; simp at hC
    subst this
    exact connected_removeAllN_nil hconn

end WaveTurbulence.TVine.Checker
