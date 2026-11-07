/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.CutMain
public import WaveTurbulence.Foundations.LayerCnt.ExitKCut
import Mathlib.Tactic

/-! # Base cuts with two single crossing bonds survive all insertions (TARGET layervine, L1531)

`ExtOK T K0 e₁ e₂` is a decidable check on a base template: the set `K0` of atoms has exactly the two crossing
bond classes `e₁, e₂` (single bonds, not slot bonds) and every slot lies on one side.  Then `K0` is a cut with two
single crossing bonds of every expansion of `T`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence.Vine

theorem fold_mem_bonds (xs : List (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)) :
    ∀ (T : VineTemplate) (e : ℕ × ℕ), e ∈ T.bonds → (∀ sk ∈ xs, e ≠ sk.1.1 ∧ e ≠ sk.1.2) →
      e ∈ (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds := by
  induction xs with
  | nil => intro T e he _; exact he
  | cons sk xs ih =>
    intro T e he hns
    simp only [List.foldl_cons]
    apply ih
    · exact mem_insertRungs_bonds he (hns sk List.mem_cons_self).1 (hns sk List.mem_cons_self).2 _
    · intro sk' h; exact hns sk' (List.mem_cons_of_mem _ h)

theorem insert_symcount_le {T : VineTemplate} {s : (ℕ × ℕ) × (ℕ × ℕ)} {k : ℕ} {e : ℕ × ℕ}
    (he : e.1 < T.n ∧ e.2 < T.n) :
    ((insertRungs T s k).bonds.map (fun p => s(p.1, p.2))).count s(e.1, e.2) ≤
      (T.bonds.map (fun p => s(p.1, p.2))).count s(e.1, e.2) := by
  by_cases hk : k = 0
  · subst hk; rw [insertRungs_zero]
  simp only [insertRungs, hk, ite_false, List.map_append, List.count_append]
  have hnew : ∀ l : List (ℕ × ℕ), (∀ p ∈ l, T.n ≤ p.1 ∨ T.n ≤ p.2) →
      (l.map (fun p => s(p.1, p.2))).count s(e.1, e.2) = 0 := by
    intro l hl
    apply List.count_eq_zero_of_not_mem
    intro hm
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
    have := hl p hp
    rcases Sym2.eq_iff.mp hpe with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have h1 := hnew (railBonds s.1.1 ((List.range k).map (T.n + ·)) s.1.2) (fun p hp =>
    railBonds_has_new (n := T.n) hk (fun j hj => by show T.n ≤ T.n + j; omega) hp)
  have h2 := hnew (railBonds s.2.1 ((List.range k).map (T.n + k + ·)) s.2.2) (fun p hp =>
    railBonds_has_new (n := T.n) hk (fun j hj => by show T.n ≤ T.n + k + j; omega) hp)
  have h3 := hnew ((List.zip ((List.range k).map (T.n + ·)) ((List.range k).map (T.n + k + ·))).flatMap
      (fun p => [p, p])) (by
    intro p hp
    rw [List.mem_flatMap] at hp
    obtain ⟨q, hq, hpq⟩ := hp
    have hpq' : p = q := by simpa using hpq
    subst hpq'
    rw [List.zip_map'] at hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    left; show T.n ≤ T.n + i; omega)
  rw [h1, h2, h3]
  have hsub : ((T.bonds.erase s.1).erase s.2).Sublist T.bonds :=
    (List.erase_sublist).trans List.erase_sublist
  have := (hsub.map (fun p : ℕ × ℕ => s(p.1, p.2))).count_le s(e.1, e.2)
  omega

theorem fold_symcount_le (xs : List (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)) (M : ℕ) :
    ∀ (T : VineTemplate) (e : ℕ × ℕ), e.1 < M → e.2 < M → M ≤ T.n →
      (∀ sk ∈ xs, ∀ v ∈ slotEnds sk.1, v < M) →
      ((xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds.map (fun p => s(p.1, p.2))).count s(e.1, e.2) ≤
        (T.bonds.map (fun p => s(p.1, p.2))).count s(e.1, e.2) := by
  induction xs with
  | nil => intro T e _ _ _ _; exact le_rfl
  | cons sk xs ih =>
    intro T e h1 h2 hM hends
    simp only [List.foldl_cons]
    refine (ih _ e h1 h2 (by rw [insertRungs_atoms]; omega)
      (fun sk' hsk' => hends sk' (List.mem_cons_of_mem _ hsk'))).trans ?_
    exact insert_symcount_le (by omega)

/-- The `{0,2}`-labelling of a set of atoms. -/
@[expose] def kap (K0 : List ℕ) (v : ℕ) : ℕ := if v ∈ K0 then 2 else 0

instance (T : VineTemplate) (e : ℕ × ℕ) : Decidable (SymSingle T e) := by
  unfold SymSingle; infer_instance

/-- Membership part of the base check. -/
@[expose] def ExtA (T : VineTemplate) (K0 : List ℕ) (e1 e2 : ℕ × ℕ) : Prop :=
  (∀ v ∈ K0, 2 ≤ v ∧ v < T.n) ∧
    (e1 ∈ T.bonds ∨ (e1.2, e1.1) ∈ T.bonds) ∧ (e2 ∈ T.bonds ∨ (e2.2, e2.1) ∈ T.bonds) ∧
    s(e1.1, e1.2) ≠ s(e2.1, e2.2) ∧ (e1.1 ∈ K0 ∧ e1.2 ∉ K0) ∧ (e2.1 ∈ K0 ∧ e2.2 ∉ K0)

/-- Crossing part of the base check. -/
@[expose] def ExtB (T : VineTemplate) (K0 : List ℕ) (e1 e2 : ℕ × ℕ) : Prop :=
  (∀ e ∈ T.bonds, e ≠ e1 → e ≠ (e1.2, e1.1) → e ≠ e2 → e ≠ (e2.2, e2.1) → ¬ Crosses (kap K0) e) ∧
    (∀ s ∈ T.slots, Sides2 (kap K0) (slotEnds s))

/-- Slot and bound part of the base check. -/
@[expose] def ExtC (T : VineTemplate) (e1 e2 : ℕ × ℕ) : Prop :=
  (∀ s ∈ T.slots, s.1 ≠ e1 ∧ s.1 ≠ (e1.2, e1.1) ∧ s.2 ≠ e1 ∧ s.2 ≠ (e1.2, e1.1) ∧
      s.1 ≠ e2 ∧ s.1 ≠ (e2.2, e2.1) ∧ s.2 ≠ e2 ∧ s.2 ≠ (e2.2, e2.1)) ∧
    SymSingle T e1 ∧ SymSingle T e2 ∧ (e1.1 < T.n ∧ e1.2 < T.n) ∧ (e2.1 < T.n ∧ e2.2 < T.n)

/-- The decidable check on a base template. -/
@[expose] def ExtOK (T : VineTemplate) (K0 : List ℕ) (e1 e2 : ℕ × ℕ) : Prop :=
  ExtA T K0 e1 e2 ∧ ExtB T K0 e1 e2 ∧ ExtC T e1 e2

instance (T : VineTemplate) (K0 : List ℕ) (e1 e2 : ℕ × ℕ) : Decidable (ExtA T K0 e1 e2) := by
  unfold ExtA; infer_instance
instance (T : VineTemplate) (K0 : List ℕ) (e1 e2 : ℕ × ℕ) : Decidable (ExtB T K0 e1 e2) := by
  unfold ExtB; infer_instance
instance (T : VineTemplate) (e1 e2 : ℕ × ℕ) : Decidable (ExtC T e1 e2) := by
  unfold ExtC; infer_instance
instance (T : VineTemplate) (K0 : List ℕ) (e1 e2 : ℕ × ℕ) : Decidable (ExtOK T K0 e1 e2) := by
  unfold ExtOK; infer_instance


theorem kap_le (K0 : List ℕ) (v : ℕ) : kap K0 v ≤ 2 := by
  unfold kap; split_ifs <;> omega

theorem kap_ne_one (K0 : List ℕ) (v : ℕ) : kap K0 v ≠ 1 := by
  unfold kap; split_ifs <;> omega

theorem kcut_ext (X : VineType) (ks : List ℕ) (hk : ks.length = X.template.slots.length)
    {K0 : List ℕ} {e1 e2 : ℕ × ℕ} (h : ExtOK X.template K0 e1 e2) :
    ∃ K : ℕ → Prop, IsKCut (X.expand ks) K e1 e2 ∧ ∀ v < X.template.n, (K v ↔ v ∈ K0) := by
  obtain ⟨hn2, hbdd, hsl⟩ := baseOK X
  obtain ⟨⟨hrange, hm1, hm2, hne, ho1, ho2⟩, ⟨hcut, hside⟩, ⟨hslot, hs1, hs2, hb1, hb2⟩⟩ := h
  set σ0 := kap K0 with hσ0
  set E : List (ℕ × ℕ) := [e1, (e1.2, e1.1), e2, (e2.2, e2.1)] with hE
  have hmem : ∀ sk ∈ X.template.slots.zip ks, sk.1 ∈ X.template.slots := fun sk hsk =>
    (List.of_mem_zip hsk).1
  have hCutOn : CutOn X.template.bonds E σ0 := by
    intro e he hnE
    apply hcut e he <;> intro h' <;> exact hnE (by simp [hE, h'])
  have hle : ∀ v, σ0 v ≤ 2 := fun v => kap_le K0 v
  obtain ⟨σ', h1', h2', h3', h4'⟩ := fold_ext (X.template.slots.zip ks) X.template.n X.template E σ0 le_rfl
    hbdd (fun sk hsk => ⟨(hsl _ (hmem sk hsk)).2.1, (hsl _ (hmem sk hsk)).2.2⟩)
    (fun sk hsk => ⟨(hsl _ (hmem sk hsk)).1, hside _ (hmem sk hsk)⟩) hCutOn hle
  have hbddF := fold_bdd (X.template.slots.zip ks) X.template.n X.template le_rfl hbdd
    (fun sk hsk => (hsl _ (hmem sk hsk)).1)
  have hnF : X.template.n ≤ (X.expand ks).n := by
    unfold VineType.expand; rw [fold_insertRungs_atoms]; omega
  -- values avoid 1 below the atom count
  have hne1 : ∀ v, v < (X.expand ks).n → σ' v ≠ 1 := by
    intro v hv
    by_cases hv0 : v < X.template.n
    · rw [h1' v hv0]; exact kap_ne_one K0 v
    · exact h3' v (by omega) hv
  refine ⟨fun v => v < (X.expand ks).n ∧ σ' v = 2, ⟨?_, ?_, ?_, ?_, ?_, hne, ?_, ?_, ?_⟩, ?_⟩
  · intro e he hc1 hc2
    have hnE : e ∉ E := by
      intro hE'
      simp only [hE, List.mem_cons, List.not_mem_nil, or_false] at hE'
      rcases hE' with rfl | rfl | rfl | rfl
      · exact hc1 rfl
      · exact hc1 Sym2.eq_swap
      · exact hc2 rfl
      · exact hc2 Sym2.eq_swap
    have hb := hbddF e he
    have hnc := h4' e he hnE
    have h1 := hne1 e.1 hb.1
    have h2 := hne1 e.2 hb.2
    have := h2' e.1
    have := h2' e.2
    unfold Crosses at hnc
    constructor
    · rintro ⟨_, hh⟩; refine ⟨hb.2, ?_⟩; omega
    · rintro ⟨_, hh⟩; refine ⟨hb.1, ?_⟩; omega
  · rcases hm1 with hh | hh
    · left
      exact fold_mem_bonds _ _ _ hh (fun sk hsk => by
        have := hslot sk.1 (hmem sk hsk); exact ⟨this.1.symm, this.2.2.1.symm⟩)
    · right
      exact fold_mem_bonds _ _ _ hh (fun sk hsk => by
        have := hslot sk.1 (hmem sk hsk); exact ⟨this.2.1.symm, this.2.2.2.1.symm⟩)
  · rcases hm2 with hh | hh
    · left
      exact fold_mem_bonds _ _ _ hh (fun sk hsk => by
        have := hslot sk.1 (hmem sk hsk); exact ⟨this.2.2.2.2.1.symm, this.2.2.2.2.2.2.1.symm⟩)
    · right
      exact fold_mem_bonds _ _ _ hh (fun sk hsk => by
        have := hslot sk.1 (hmem sk hsk); exact ⟨this.2.2.2.2.2.1.symm, this.2.2.2.2.2.2.2.symm⟩)
  · exact (fold_symcount_le _ _ _ e1 hb1.1 hb1.2 le_rfl (fun sk hsk => (hsl _ (hmem sk hsk)).1)).trans hs1
  · exact (fold_symcount_le _ _ _ e2 hb2.1 hb2.2 le_rfl (fun sk hsk => (hsl _ (hmem sk hsk)).1)).trans hs2
  · refine ⟨⟨by omega, ?_⟩, ?_⟩
    · rw [h1' _ hb1.1]; simp [hσ0, kap, ho1.1]
    · rintro ⟨_, hh⟩
      rw [h1' _ hb1.2] at hh; simp [hσ0, kap, ho1.2] at hh
  · refine ⟨⟨by omega, ?_⟩, ?_⟩
    · rw [h1' _ hb2.1]; simp [hσ0, kap, ho2.1]
    · rintro ⟨_, hh⟩
      rw [h1' _ hb2.2] at hh; simp [hσ0, kap, ho2.2] at hh
  · rintro v ⟨hv, hv2⟩
    refine ⟨?_, hv⟩
    by_cases hv0 : v < X.template.n
    · rw [h1' v hv0] at hv2
      have : v ∈ K0 := by by_contra hc; simp [hσ0, kap, hc] at hv2
      exact (hrange v this).1
    · omega
  · intro v hv
    show (v < (X.expand ks).n ∧ σ' v = 2) ↔ v ∈ K0
    rw [h1' v hv]
    constructor
    · rintro ⟨_, hh⟩
      by_contra hc; simp [hσ0, kap, hc] at hh
    · intro hvK
      exact ⟨by omega, by simp [hσ0, kap, hvK]⟩

end WaveTurbulence.LayerCnt
