/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineExpansionCounts
import Mathlib.Tactic

/-! # Cut certificates for expanded vine templates (TARGET layervine, L1531: the group chain)

A *cut labelling* `σ : ℕ → ℕ` (values `0`, `1`, `2`: below, the cut, above) of a bond list has no bond joining
side `0` to side `2`.  A group whose atoms are the level-`1` set of a labelling separating the two joints is met
by every path between the joints.  This file proves that cut labellings extend through one rung insertion
(`ext_insert`) and that the inserted rungs of a slot that is a cut of the template are cuts (`rung_cert`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence.Vine

/-- The bond `e` joins side `0` to side `2`. -/
@[expose] def Crosses (σ : ℕ → ℕ) (e : ℕ × ℕ) : Prop :=
  (σ e.1 = 0 ∧ σ e.2 = 2) ∨ (σ e.1 = 2 ∧ σ e.2 = 0)

/-- No bond of `L`, except the exempt ones in `E`, joins side `0` to side `2`. -/
@[expose] def CutOn (L E : List (ℕ × ℕ)) (σ : ℕ → ℕ) : Prop :=
  ∀ e ∈ L, e ∉ E → ¬ Crosses σ e

/-- The atoms of `S` do not lie on both outer sides. -/
@[expose] def Sides2 (σ : ℕ → ℕ) (S : List ℕ) : Prop :=
  ¬ ((∃ v ∈ S, σ v = 0) ∧ ∃ v ∈ S, σ v = 2)

/-- The four endpoints of a slot. -/
@[expose] def slotEnds (s : (ℕ × ℕ) × (ℕ × ℕ)) : List ℕ := [s.1.1, s.1.2, s.2.1, s.2.2]

theorem ne_of_mem_erase_of_count {L : List (ℕ × ℕ)} {a e : ℕ × ℕ} (hc : L.count a ≤ 1)
    (he : e ∈ L.erase a) : e ≠ a := by
  rintro rfl
  have h1 : 0 < L.count e - 1 := by
    have := List.count_erase_self (a := e) (l := L)
    have h2 := List.count_pos_iff.mpr he
    omega
  have := List.count_erase_self (a := e) (l := L)
  omega

theorem mem_insertRungs_cases {T : VineTemplate} {s : (ℕ × ℕ) × (ℕ × ℕ)} {k : ℕ} (hk : k ≠ 0)
    (hc1 : T.bonds.count s.1 ≤ 1) (hc2 : T.bonds.count s.2 ≤ 1) {e : ℕ × ℕ}
    (he : e ∈ (insertRungs T s k).bonds) :
    (e ∈ T.bonds ∧ e ≠ s.1 ∧ e ≠ s.2) ∨
      e ∈ railBonds s.1.1 ((List.range k).map (T.n + ·)) s.1.2 ∨
      e ∈ railBonds s.2.1 ((List.range k).map (T.n + k + ·)) s.2.2 ∨
      ∃ i < k, e = (T.n + i, T.n + k + i) := by
  simp only [insertRungs, hk, ite_false, List.mem_append] at he
  rcases he with ((he | he) | he) | he
  · left
    have h1 : e ≠ s.2 := ne_of_mem_erase_of_count
      (((List.erase_sublist (a := s.1) (l := T.bonds)).count_le s.2).trans hc2) he
    refine ⟨List.mem_of_mem_erase (List.mem_of_mem_erase he), ?_, h1⟩
    exact ne_of_mem_erase_of_count hc1 (List.mem_of_mem_erase he)
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (Or.inl he))
  · right; right; right
    rw [List.mem_flatMap] at he
    obtain ⟨p, hp, hep⟩ := he
    have hep' : e = p := by simpa using hep
    subst hep'
    rw [List.zip_map'] at hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    exact ⟨i, List.mem_range.mp hi, rfl⟩


/-- The labelling extended to the `2k` atoms `n, …, n+2k-1` inserted at a slot: they all get the value `c`. -/
@[expose] def extσ (n k c : ℕ) (σ : ℕ → ℕ) (v : ℕ) : ℕ := if n ≤ v ∧ v < n + 2 * k then c else σ v

/-- The side of the inserted atoms: `2` if some endpoint of the slot is on side `2`, else `0`. -/
@[expose] noncomputable def newSide (σ : ℕ → ℕ) (s : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := by
  classical
  exact if ∃ v ∈ slotEnds s, σ v = 2 then 2 else 0

theorem extσ_old {n k c : ℕ} {σ : ℕ → ℕ} {v : ℕ} (hv : v < n) : extσ n k c σ v = σ v := by
  unfold extσ; rw [if_neg]; omega

theorem extσ_new {n k c : ℕ} {σ : ℕ → ℕ} {v : ℕ} (h1 : n ≤ v) (h2 : v < n + 2 * k) :
    extσ n k c σ v = c := by
  unfold extσ; rw [if_pos ⟨h1, h2⟩]

theorem noCross_ext {T : VineTemplate} {s : (ℕ × ℕ) × (ℕ × ℕ)} {k : ℕ} {σ : ℕ → ℕ}
    (hends : ∀ v ∈ slotEnds s, v < T.n) (hS : Sides2 σ (slotEnds s)) {p q : ℕ}
    (hp : p ∈ slotEnds s ∨ (T.n ≤ p ∧ p < T.n + 2 * k))
    (hq : q ∈ slotEnds s ∨ (T.n ≤ q ∧ q < T.n + 2 * k)) :
    ¬ Crosses (extσ T.n k (newSide σ s) σ) (p, q) := by
  classical
  have key : ∀ v, (v ∈ slotEnds s ∨ (T.n ≤ v ∧ v < T.n + 2 * k)) →
      (extσ T.n k (newSide σ s) σ v = 0 ∨ extσ T.n k (newSide σ s) σ v = 2) ∨
        extσ T.n k (newSide σ s) σ v = σ v := by
    intro v hv
    rcases hv with hv | hv
    · right; exact extσ_old (hends v hv)
    · left; rw [extσ_new hv.1 hv.2]; unfold newSide; split_ifs <;> simp
  -- all relevant values lie on one outer side
  by_cases h2 : ∃ v ∈ slotEnds s, σ v = 2
  · have hc : newSide σ s = 2 := by unfold newSide; rw [if_pos h2]
    have h0 : ∀ v ∈ slotEnds s, σ v ≠ 0 := fun v hv h0 => hS ⟨⟨v, hv, h0⟩, h2⟩
    have hval : ∀ v, (v ∈ slotEnds s ∨ (T.n ≤ v ∧ v < T.n + 2 * k)) →
        extσ T.n k (newSide σ s) σ v ≠ 0 := by
      intro v hv
      rcases hv with hv | hv
      · rw [extσ_old (hends v hv)]; exact h0 v hv
      · rw [extσ_new hv.1 hv.2, hc]; omega
    rintro (⟨h1, _⟩ | ⟨_, h1⟩)
    · exact hval p hp h1
    · exact hval q hq h1
  · have hc : newSide σ s = 0 := by unfold newSide; rw [if_neg h2]
    have h0 : ∀ v ∈ slotEnds s, σ v ≠ 2 := fun v hv h0 => h2 ⟨v, hv, h0⟩
    have hval : ∀ v, (v ∈ slotEnds s ∨ (T.n ≤ v ∧ v < T.n + 2 * k)) →
        extσ T.n k (newSide σ s) σ v ≠ 2 := by
      intro v hv
      rcases hv with hv | hv
      · rw [extσ_old (hends v hv)]; exact h0 v hv
      · rw [extσ_new hv.1 hv.2, hc]; omega
    rintro (⟨_, h1⟩ | ⟨h1, _⟩)
    · exact hval q hq h1
    · exact hval p hp h1

theorem ext_insert {T : VineTemplate} {s : (ℕ × ℕ) × (ℕ × ℕ)} {k : ℕ} (hk : k ≠ 0)
    (hc1 : T.bonds.count s.1 ≤ 1) (hc2 : T.bonds.count s.2 ≤ 1)
    (hends : ∀ v ∈ slotEnds s, v < T.n) (hbdd : ∀ e ∈ T.bonds, e.1 < T.n ∧ e.2 < T.n)
    {E : List (ℕ × ℕ)} {σ : ℕ → ℕ} (hS : Sides2 σ (slotEnds s)) (h : CutOn T.bonds E σ) :
    CutOn (insertRungs T s k).bonds E (extσ T.n k (newSide σ s) σ) := by
  intro e he hE
  have hnew : ∀ {a : ℕ} {ws : List ℕ}, (∀ w ∈ ws, T.n ≤ w ∧ w < T.n + 2 * k) → 
      (a ∈ slotEnds s ∨ (T.n ≤ a ∧ a < T.n + 2 * k)) → ∀ {b : ℕ}, 
      (b ∈ slotEnds s ∨ (T.n ≤ b ∧ b < T.n + 2 * k)) → ∀ {p q : ℕ}, (p, q) ∈ railBonds a ws b → 
      ¬ Crosses (extσ T.n k (newSide σ s) σ) (p, q) := by
    intro a ws hws ha b hb p q hpq
    unfold railBonds at hpq
    obtain ⟨h1, h2⟩ := List.of_mem_zip hpq
    refine noCross_ext hends hS ?_ ?_
    · rcases List.mem_cons.mp h1 with rfl | h1
      · exact ha
      · exact Or.inr (hws _ h1)
    · rcases List.mem_append.mp h2 with h2 | h2
      · exact Or.inr (hws _ h2)
      · rw [List.mem_singleton.mp h2]; exact hb
  rcases mem_insertRungs_cases hk hc1 hc2 he with ⟨he1, h1, h2⟩ | he | he | ⟨i, hi, rfl⟩
  · have hb := hbdd e he1
    unfold Crosses
    rw [extσ_old hb.1, extσ_old hb.2]
    exact h e he1 hE
  · obtain ⟨p, q⟩ := e
    refine hnew ?_ (Or.inl (by simp [slotEnds])) (Or.inl (by simp [slotEnds])) he
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have := List.mem_range.mp hi; omega
  · obtain ⟨p, q⟩ := e
    refine hnew ?_ (Or.inl (by simp [slotEnds])) (Or.inl (by simp [slotEnds])) he
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have := List.mem_range.mp hi; omega
  · exact noCross_ext hends hS (Or.inr ⟨by omega, by omega⟩) (Or.inr ⟨by omega, by omega⟩)

end WaveTurbulence.LayerCnt
