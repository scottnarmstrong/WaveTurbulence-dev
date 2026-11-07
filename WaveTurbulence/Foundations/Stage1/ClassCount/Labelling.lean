/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.Irregular
import Mathlib.Tactic

/-!
# CLASSCOUNT: labellings with near regular pairs

From an injective key `V → ℕ × ℕ` (block, position) we get a labelling `V ≃ Fin (card V)` such that atoms of the
same block with positions at distance `≤ 2` have labels at distance `≤ 2`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset

theorem exists_label_near {V : Type*} [Fintype V] (key : V → ℕ × ℕ) (hinj : Function.Injective key) :
    ∃ ℓ : V ≃ Fin (Fintype.card V), ∀ a b, (key a).1 = (key b).1 → (key b).2 ≤ (key a).2 + 2 →
      (key a).2 ≤ (key b).2 + 2 → (ℓ a : ℕ) ≤ ℓ b + 2 ∧ (ℓ b : ℕ) ≤ ℓ a + 2 := by
  classical
  letI : LinearOrder V := LinearOrder.lift' (fun a => toLex (key a)) (fun a b h => hinj (toLex.injective h))
  let ℓo : V ≃o Fin (Fintype.card V) := (Fintype.orderIsoFinOfCardEq V rfl).symm
  have hlt : ∀ a b : V, a < b ↔ toLex (key a) < toLex (key b) := fun a b => Iff.rfl
  have aux : ∀ a b : V, a < b → (key a).1 = (key b).1 → (key b).2 ≤ (key a).2 + 2 →
      (ℓo b : ℕ) ≤ ℓo a + 2 := by
    intro a b hab h1 h2
    by_contra hcon
    push Not at hcon
    have hab' : (ℓo a : ℕ) < ℓo b := ℓo.lt_iff_lt.mpr hab
    let c1 : V := ℓo.symm ⟨(ℓo a : ℕ) + 1, by omega⟩
    let c2 : V := ℓo.symm ⟨(ℓo a : ℕ) + 2, by omega⟩
    have hc : ∀ c : V, a < c → c < b → (key c).1 = (key a).1 ∧ (key c).2 = (key a).2 + 1 := by
      intro c hac hcb
      rw [hlt, Prod.Lex.lt_iff] at hac hcb
      simp only [ofLex_toLex] at hac hcb
      have hsa : (key a).2 < (key b).2 := by
        rcases hab' |>.le |> fun _ => (hlt a b).mp hab |> Prod.Lex.lt_iff.mp with h | h
        · simp only [ofLex_toLex] at h; omega
        · simp only [ofLex_toLex] at h; exact h.2
      rcases hac with hac | hac <;> rcases hcb with hcb | hcb
      · omega
      · omega
      · omega
      · omega
    have e1 : a < c1 := by
      rw [← ℓo.lt_iff_lt]; simp only [c1, OrderIso.apply_symm_apply]; show (ℓo a : ℕ) < (ℓo a : ℕ) + 1; omega
    have e2 : c1 < c2 := by
      rw [← ℓo.lt_iff_lt]; simp only [c1, c2, OrderIso.apply_symm_apply]; show (ℓo a : ℕ) + 1 < (ℓo a : ℕ) + 2; omega
    have e3 : c2 < b := by
      rw [← ℓo.lt_iff_lt]; simp only [c2, OrderIso.apply_symm_apply]; show (ℓo a : ℕ) + 2 < ℓo b; omega
    have k1 := hc c1 e1 (e2.trans e3)
    have k2 := hc c2 (e1.trans e2) e3
    have : c1 = c2 := hinj (Prod.ext (k1.1.trans k2.1.symm) (k1.2.trans k2.2.symm))
    exact absurd this e2.ne
  refine ⟨ℓo.toEquiv, ?_⟩
  intro a b h1 h2 h3
  rcases lt_trichotomy a b with hab | rfl | hab
  · have := aux a b hab h1 h2
    have h : (ℓo a : ℕ) < ℓo b := ℓo.lt_iff_lt.mpr hab
    exact ⟨by simp only [OrderIso.coe_toEquiv]; omega, by simpa using this⟩
  · exact ⟨by omega, by omega⟩
  · have := aux b a hab h1.symm h3
    have h : (ℓo b : ℕ) < ℓo a := ℓo.lt_iff_lt.mpr hab
    exact ⟨by simpa using this, by simp only [OrderIso.coe_toEquiv]; omega⟩


namespace LadderFam
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {ι : Type}
  (F : LadderFam M ι)

/-- The slot `(i, s)` of an atom: `u_j` has slot `(i, 2j)` and `v_j` has slot `(i, 2j + 1)`. -/
def Slot (p : ι × ℕ) (a : V) : Prop :=
  (∃ j : Fin (F.len p.1 + 1), 2 * j.1 = p.2 ∧ F.u p.1 j = a) ∨
  (∃ j : Fin (F.len p.1 + 1), 2 * j.1 + 1 = p.2 ∧ F.v p.1 j = a)

theorem slot_eq {p : ι × ℕ} {a b : V} (ha : F.Slot p a) (hb : F.Slot p b) : a = b := by
  rcases ha with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> rcases hb with ⟨j', hj', rfl⟩ | ⟨j', hj', rfl⟩
  · have : j = j' := Fin.ext (by omega)
    rw [this]
  · omega
  · omega
  · have : j = j' := Fin.ext (by omega)
    rw [this]

theorem slot_unique (hdisj : ∀ i j, i ≠ j → Disjoint (F.atomsOf i) (F.atomsOf j)) {p p' : ι × ℕ} {a : V}
    (h : F.Slot p a) (h' : F.Slot p' a) : p = p' := by
  have mem : ∀ {q : ι × ℕ}, F.Slot q a → a ∈ F.atomsOf q.1 := by
    intro q hq
    unfold atomsOf Molecule.ladderAtoms
    rcases hq with ⟨j, _, rfl⟩ | ⟨j, _, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hi : p.1 = p'.1 := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj _ _ hne) (mem h) (mem h')
  obtain ⟨i, s⟩ := p
  obtain ⟨i', s'⟩ := p'
  simp only at hi
  subst hi
  rcases h with ⟨j, hj, hja⟩ | ⟨j, hj, hja⟩ <;> rcases h' with ⟨j', hj', hja'⟩ | ⟨j', hj', hja'⟩
  · have := congrArg Fin.val (inj_u F i (hja.trans hja'.symm))
    exact Prod.ext rfl (by simp only at hj hj' ⊢; omega)
  · exact absurd (hja.trans hja'.symm) (ne_uv F i _ _)
  · exact absurd (hja'.trans hja.symm) (ne_uv F i _ _)
  · have := congrArg Fin.val (inj_v F i (hja.trans hja'.symm))
    exact Prod.ext rfl (by simp only at hj hj' ⊢; omega)

theorem exists_labelling [Fintype V] [Fintype ι] [DecidableEq ι]
    (hdisj : ∀ i j, i ≠ j → Disjoint (F.atomsOf i) (F.atomsOf j)) :
    ∃ ℓ : V ≃ Fin (Fintype.card V), ∀ a b, F.Reg a b → a ≠ b ∧
      (ℓ a : ℕ) ≤ ℓ b + 2 ∧ (ℓ b : ℕ) ≤ ℓ a + 2 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let idx : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let key : V → ℕ × ℕ := fun a =>
    if h : ∃ p, F.Slot p a then ((e (Classical.choose h).1 : ℕ), (Classical.choose h).2)
    else (Fintype.card ι + 1, (idx a : ℕ))
  have hkey : ∀ p a, F.Slot p a → key a = ((e p.1 : ℕ), p.2) := by
    intro p a hp
    have h : ∃ p, F.Slot p a := ⟨p, hp⟩
    have := F.slot_unique hdisj (Classical.choose_spec h) hp
    simp only [key, dif_pos h, this]
  have hinj : Function.Injective key := by
    intro a b hab
    by_cases ha : ∃ p, F.Slot p a <;> by_cases hb : ∃ p, F.Slot p b
    · obtain ⟨p, hp⟩ := ha
      obtain ⟨p', hp'⟩ := hb
      rw [hkey p a hp, hkey p' b hp'] at hab
      have h1 : p.1 = p'.1 := e.injective (Fin.ext (congrArg Prod.fst hab))
      have h2 : p.2 = p'.2 := by have := congrArg Prod.snd hab; simpa using this
      have : p = p' := Prod.ext h1 h2
      subst this
      exact F.slot_eq hp hp'
    · exfalso
      obtain ⟨p, hp⟩ := ha
      rw [hkey p a hp] at hab
      simp only [key, dif_neg hb] at hab
      have := congrArg Prod.fst hab
      have h3 := (e p.1).2
      simp only at this
      omega
    · exfalso
      obtain ⟨p, hp⟩ := hb
      rw [hkey p b hp] at hab
      simp only [key, dif_neg ha] at hab
      have := congrArg Prod.fst hab
      have h3 := (e p.1).2
      simp only at this
      omega
    · simp only [key, dif_neg ha, dif_neg hb, Prod.mk.injEq, true_and] at hab
      exact idx.injective (Fin.ext hab)
  obtain ⟨ℓ, hℓ⟩ := exists_label_near key hinj
  refine ⟨ℓ, ?_⟩
  rintro a b ⟨i, hreg⟩
  have hne : a ≠ b := by
    rcases hreg with ⟨j, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨j, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ne_uv F i _ _
    · exact (ne_uv F i _ _).symm
    · intro h; have := congrArg Fin.val (inj_u F i h); simp at this
    · intro h; have := congrArg Fin.val (inj_u F i h); simp at this
    · intro h; have := congrArg Fin.val (inj_v F i h); simp at this
    · intro h; have := congrArg Fin.val (inj_v F i h); simp at this
  refine ⟨hne, ?_⟩
  have key2 : (key a).1 = (key b).1 ∧ (key b).2 ≤ (key a).2 + 2 ∧ (key a).2 ≤ (key b).2 + 2 := by
    rcases hreg with ⟨j, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨j, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · rw [hkey (i, 2 * j.1) _ (Or.inl ⟨j, rfl, rfl⟩), hkey (i, 2 * j.1 + 1) _ (Or.inr ⟨j, rfl, rfl⟩)]
      simp only [true_and]; omega
    · rw [hkey (i, 2 * j.1 + 1) _ (Or.inr ⟨j, rfl, rfl⟩), hkey (i, 2 * j.1) _ (Or.inl ⟨j, rfl, rfl⟩)]
      simp only [true_and]; omega
    · rw [hkey (i, 2 * j.castSucc.1) _ (Or.inl ⟨j.castSucc, rfl, rfl⟩),
        hkey (i, 2 * j.succ.1) _ (Or.inl ⟨j.succ, rfl, rfl⟩)]
      simp; omega
    · rw [hkey (i, 2 * j.succ.1) _ (Or.inl ⟨j.succ, rfl, rfl⟩),
        hkey (i, 2 * j.castSucc.1) _ (Or.inl ⟨j.castSucc, rfl, rfl⟩)]
      simp; omega
    · rw [hkey (i, 2 * j.castSucc.1 + 1) _ (Or.inr ⟨j.castSucc, rfl, rfl⟩),
        hkey (i, 2 * j.succ.1 + 1) _ (Or.inr ⟨j.succ, rfl, rfl⟩)]
      simp; omega
    · rw [hkey (i, 2 * j.succ.1 + 1) _ (Or.inr ⟨j.succ, rfl, rfl⟩),
        hkey (i, 2 * j.castSucc.1 + 1) _ (Or.inr ⟨j.castSucc, rfl, rfl⟩)]
      simp; omega
  exact hℓ a b key2.1 key2.2.1 key2.2.2

end LadderFam

end WaveTurbulence.ClassCount
