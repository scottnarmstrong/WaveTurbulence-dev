/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DeriveAtt

/-!
# Derivation of the cell decomposition, X: the spine ports

For every spine step `i ≤ r`, the exit region `reg i (hx i)` of `Z i` and the entry region `reg i (he i)` of
`Z (i+1)` are crossed by exactly two bonds: those of `cross (Z i) (Z (i+1))`, together with `α` (exit) or `α'`
(entry) at the (P-b) step. The crossing bonds of the entry region have their outer end in `Z (i+1)`, those of the
exit region their inner end in `Z i`.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract Struct

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V}

namespace Lay

variable (L : Lay M S a b) (hB : M.IsBlock S a b) {att : Att} (A : L.AttData att)
include hB A

omit hB A in
theorem H_zero_empty (hs : L.s = 0) : L.H 0 = ∅ := by
  ext v; simp only [notMem_empty, iff_false]; intro h
  obtain ⟨l, -, hl, -⟩ := (L.mem_H 0 v).mp h; omega

/-- The spine end of an attachment bond determines its block. -/
theorem att_end {e : Bond M S} (he : e ∈ cross (M := M) (S := S) (L.H 0) (S \ L.H 0)) {j : ℕ} (hj : j ≤ L.r + 1)
    (hz : tl e ∈ L.Z j ∨ hd e ∈ L.Z j) (hs : 1 ≤ L.s) :
    (e = A.α ∧ A.x ∈ L.Z j) ∨ (e = A.α' ∧ A.x' ∈ L.Z j) := by
  obtain ⟨-, hset, -, -, hy, hy', hα, hα'⟩ := A.pend hs
  rw [hset, mem_insert, mem_singleton] at he
  have hYZ : ∀ v, v ∈ L.Y 0 → v ∈ L.Z j → False := fun v h1 h2 => L.ZY_disj hB hj (by omega) h2 h1
  rcases he with rfl | rfl
  · left; refine ⟨rfl, ?_⟩
    rcases hα with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hz with h | h
    · rwa [h1] at h
    · rw [h2] at h; exact absurd h (fun h' => hYZ _ hy h')
    · rw [h1] at h; exact absurd h (fun h' => hYZ _ hy h')
    · rwa [h2] at h
  · right; refine ⟨rfl, ?_⟩
    rcases hα' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hz with h | h
    · rwa [h1] at h
    · rw [h2] at h; exact absurd h (fun h' => hYZ _ hy' h')
    · rw [h1] at h; exact absurd h (fun h' => hYZ _ hy' h')
    · rwa [h2] at h

/-- The block index of an outer attachment end. -/
theorem x_block (hs : 1 ≤ L.s) : ∃ jx jx', jx ≤ L.r + 1 ∧ jx' ≤ L.r + 1 ∧ A.x ∈ L.Z jx ∧ A.x' ∈ L.Z jx' ∧
    (match att with
      | .none => False
      | .pa j => jx = j ∧ jx' = j
      | .pb j => jx = j ∧ jx' = j + 1) := by
  have hc := A.case
  cases att with
  | none => exact absurd hc.1 (by omega)
  | pa j => exact ⟨j, j, by omega, by omega, hc.2.2.2.1, hc.2.2.2.2.1, rfl, rfl⟩
  | pb j => exact ⟨j, j + 1, by omega, by omega, hc.2.2.2.1, hc.2.2.2.2, rfl, rfl⟩

/-- **The crossing bonds of a spine region** with flag `h`: the attachment bond crosses iff its spine end index `j`
satisfies `(j ≤ i) ↔ h = false`. -/
theorem portSet_reg {i : ℕ} (hi : i ≤ L.r) (h : Bool) :
    portSet (M := M) (S := S) (L.reg i h) = cross (L.Z i) (L.Z (i + 1)) ∪
      ((if 1 ≤ L.s then ({A.α, A.α'} : Finset (Bond M S)) else ∅).filter fun e =>
        ∃ j, j ≤ L.r + 1 ∧ (tl e ∈ L.Z j ∨ hd e ∈ L.Z j) ∧ (j ≤ i ↔ h = false)) := by
  ext e
  rw [mem_portSet, L.crosses_reg hB hi h e, mem_union, mem_filter]
  by_cases hs : 1 ≤ L.s
  · obtain ⟨-, hset, -⟩ := A.pend hs
    rw [if_pos hs, ← hset]
  · have : L.s = 0 := by omega
    rw [if_neg hs, L.H_zero_empty this]
    simp only [notMem_empty, false_and, or_false]
    have : cross (M := M) (S := S) (∅ : Finset V) (S \ ∅) = ∅ := by ext e; simp [mem_cross]
    rw [this]; simp

/-- The attachment bonds crossing a spine region. -/
theorem mem_attFilter {i : ℕ} (h : Bool) (e : Bond M S) (hs : 1 ≤ L.s) {jx jx' : ℕ} (hjx : jx ≤ L.r + 1)
    (hjx' : jx' ≤ L.r + 1) (hx : A.x ∈ L.Z jx) (hx' : A.x' ∈ L.Z jx') :
    (e ∈ ({A.α, A.α'} : Finset (Bond M S)) ∧
      ∃ j, j ≤ L.r + 1 ∧ (tl e ∈ L.Z j ∨ hd e ∈ L.Z j) ∧ (j ≤ i ↔ h = false)) ↔
      ((e = A.α ∧ (jx ≤ i ↔ h = false)) ∨ (e = A.α' ∧ (jx' ≤ i ↔ h = false))) := by
  obtain ⟨hne, hset, -, -, hy, hy', hα, hα'⟩ := A.pend hs
  have hmem : e ∈ ({A.α, A.α'} : Finset (Bond M S)) → e ∈ cross (M := M) (S := S) (L.H 0) (S \ L.H 0) := by
    intro h; rw [hset]; exact h
  constructor
  · rintro ⟨he, j, hj, hz, hc⟩
    rcases L.att_end hB A (hmem he) hj hz hs with ⟨rfl, hxj⟩ | ⟨rfl, hxj⟩
    · left; refine ⟨rfl, ?_⟩; rwa [L.Z_unique hB hjx hj hx hxj]
    · right; refine ⟨rfl, ?_⟩; rwa [L.Z_unique hB hjx' hj hx' hxj]
  · rintro (⟨rfl, hc⟩ | ⟨rfl, hc⟩)
    · refine ⟨by simp, jx, hjx, ?_, hc⟩
      rcases hα with ⟨h1, -⟩ | ⟨-, h2⟩
      · left; rw [h1]; exact hx
      · right; rw [h2]; exact hx
    · refine ⟨by simp, jx', hjx', ?_, hc⟩
      rcases hα' with ⟨h1, -⟩ | ⟨-, h2⟩
      · left; rw [h1]; exact hx'
      · right; rw [h2]; exact hx'

theorem α_not_ZZ (hs : 1 ≤ L.s) {i : ℕ} (hi : i ≤ L.r) : A.α ∉ cross (M := M) (S := S) (L.Z i) (L.Z (i + 1)) := by
  obtain ⟨-, -, -, -, hy, -, hα, -⟩ := A.pend hs
  rw [mem_cross]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rcases hα with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rw [h4] at h2; exact L.ZY_disj hB (by omega) (by omega) h2 hy
  · rw [h3] at h1; exact L.ZY_disj hB (by omega) (by omega) h1 hy
  · rw [h4] at h2; exact L.ZY_disj hB (by omega) (by omega) h2 hy
  · rw [h3] at h1; exact L.ZY_disj hB (by omega) (by omega) h1 hy

theorem α'_not_ZZ (hs : 1 ≤ L.s) {i : ℕ} (hi : i ≤ L.r) : A.α' ∉ cross (M := M) (S := S) (L.Z i) (L.Z (i + 1)) := by
  obtain ⟨-, -, -, -, -, hy', -, hα'⟩ := A.pend hs
  rw [mem_cross]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rcases hα' with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rw [h4] at h2; exact L.ZY_disj hB (by omega) (by omega) h2 hy'
  · rw [h3] at h1; exact L.ZY_disj hB (by omega) (by omega) h1 hy'
  · rw [h4] at h2; exact L.ZY_disj hB (by omega) (by omega) h2 hy'
  · rw [h3] at h1; exact L.ZY_disj hB (by omega) (by omega) h1 hy'

omit hB A in
theorem flags_pb {i j : ℕ} : (Att.pb j).hx i = decide (j < i) ∧ (Att.pb j).he i = decide (j ≤ i) := ⟨rfl, rfl⟩

/-- **The spine ports.** For the flags `hx` (exit) and `he` (entry): the port is `cross (Z i) (Z (i+1))` plus the extra
attachment bond of the (P-b) step. -/
theorem portSet_flag {i : ℕ} (hi : i ≤ L.r) (hh : Bool) (hflag : hh = att.hx i ∨ hh = att.he i) :
    portSet (M := M) (S := S) (L.reg i hh) = cross (L.Z i) (L.Z (i + 1)) ∪
      (match att with
        | .none => ∅
        | .pa _ => ∅
        | .pb j => if i = j then (if hh then {A.α'} else {A.α}) else ∅) := by
  rw [L.portSet_reg hB A hi hh]
  congr 1
  by_cases hs : 1 ≤ L.s
  · rw [if_pos hs]
    obtain ⟨jx, jx', hjx, hjx', hx, hx', hcase⟩ := L.x_block hB A hs
    ext e
    rw [mem_filter, L.mem_attFilter hB A hh e hs hjx hjx' hx hx']
    cases att with
    | none => exact absurd hcase id
    | pa j =>
      obtain ⟨h1, h2⟩ := hcase
      have hh' : hh = decide (j ≤ i) := by rcases hflag with rfl | rfl <;> rfl
      rw [hh', h1, h2]
      by_cases hj : j ≤ i <;> simp [hj]
    | pb j =>
      obtain ⟨h1, h2⟩ := hcase
      rw [h1, h2]
      rcases hflag with rfl | rfl
      · by_cases hij : i = j
        · rw [hij]; simp [Att.hx]
        · by_cases h3 : j < i <;> simp [Att.hx, hij, h3] <;> omega
      · by_cases hij : i = j
        · rw [hij]; simp [Att.he]
        · by_cases h3 : j ≤ i <;> simp [Att.he, hij, h3] <;> omega
  · rw [if_neg hs, filter_empty]
    cases att with
    | none => rfl
    | pa j => rfl
    | pb j => exact absurd A.case.1 hs

variable (hM : M.IsMolecule)
include hM

/-- **The spine ports have two bonds.** -/
theorem card_flag {i : ℕ} (hi : i ≤ L.r) (hh : Bool) (hflag : hh = att.hx i ∨ hh = att.he i) :
    (portSet (M := M) (S := S) (L.reg i hh)).card = 2 := by
  have heven := portSet_even hM hB (L.reg_sub hB i (by omega) hh)
  have hZ := L.consec i hi
  rw [← card_cross (L.Z_sub hB (by omega)) (L.Z_sub hB (by omega))] at hZ
  rw [L.portSet_flag hB A hi hh hflag] at heven ⊢
  cases att with
  | none =>
    dsimp only at heven ⊢; rw [union_empty] at heven ⊢
    rcases hZ with h | h <;> rw [h] at heven ⊢ <;> simp_all
  | pa j =>
    dsimp only at heven ⊢; rw [union_empty] at heven ⊢
    rcases hZ with h | h <;> rw [h] at heven ⊢ <;> simp_all
  | pb j =>
    dsimp only at heven ⊢
    by_cases hij : i = j
    · have h1 : (cross (M := M) (S := S) (L.Z i) (L.Z (i + 1))).card = 1 := by
        rw [card_cross (L.Z_sub hB (by omega)) (L.Z_sub hB (by omega)), hij]; exact A.case.2.2.1
      have hs := A.case.1
      rw [if_pos hij]
      cases hh
      · simp only [Bool.false_eq_true, ite_false]
        rw [card_union_of_disjoint (disjoint_singleton_right.mpr (L.α_not_ZZ hB A hs hi)), h1, card_singleton]
      · simp only [ite_true]
        rw [card_union_of_disjoint (disjoint_singleton_right.mpr (L.α'_not_ZZ hB A hs hi)), h1, card_singleton]
    · rw [if_neg hij, union_empty] at heven ⊢
      rcases hZ with h | h <;> rw [h] at heven ⊢ <;> simp_all

omit hM in
/-- The outer ends of the entry port of `Z (i+1)` lie in `Z (i+1)`. -/
theorem entry_outer {i : ℕ} (hi : i ≤ L.r) (e : Bond M S)
    (he : e ∈ portSet (M := M) (S := S) (L.reg i (att.he i))) :
    (tl e ∈ L.reg i (att.he i) ∧ hd e ∈ L.Z (i + 1)) ∨ (hd e ∈ L.reg i (att.he i) ∧ tl e ∈ L.Z (i + 1)) := by
  rw [L.portSet_flag hB A hi _ (Or.inr rfl), mem_union] at he
  have hZi : ∀ v, v ∈ L.Z i → v ∈ L.reg i (att.he i) := fun v hv =>
    (L.mem_reg_Z hB (by omega) (by omega) hv).mpr le_rfl
  rcases he with he | he
  · rw [mem_cross] at he
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hZi _ h1, h2⟩
    · exact Or.inr ⟨hZi _ h2, h1⟩
  · cases att with
    | none => exact absurd he (notMem_empty _)
    | pa j => exact absurd he (notMem_empty _)
    | pb j =>
      dsimp only at he
      by_cases hij : i = j
      · rw [if_pos hij] at he
        have hflag : (Att.pb j).he i = true := by simp [Att.he, hij]
        rw [hflag, if_pos rfl, mem_singleton] at he
        subst he
        have hs := A.case.1
        obtain ⟨-, -, -, -, -, hy', -, hα'⟩ := A.pend hs
        have hx' : A.x' ∈ L.Z (i + 1) := by rw [hij]; exact A.case.2.2.2.2
        have hy'r : A.y' ∈ L.reg i ((Att.pb j).he i) := by
          rw [hflag]; exact (L.mem_reg_Y hB (by omega) (by omega) hy').mpr rfl
        rcases hα' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · right; rw [h1, h2]; exact ⟨hy'r, hx'⟩
        · left; rw [h1, h2]; exact ⟨hy'r, hx'⟩
      · rw [if_neg hij] at he; exact absurd he (notMem_empty _)

omit hM in
/-- The inner ends of the exit port of `Z i` lie in `Z i`. -/
theorem exit_inner {i : ℕ} (hi : i ≤ L.r) (e : Bond M S)
    (he : e ∈ portSet (M := M) (S := S) (L.reg i (att.hx i))) :
    (tl e ∈ L.Z i ∧ hd e ∉ L.reg i (att.hx i)) ∨ (hd e ∈ L.Z i ∧ tl e ∉ L.reg i (att.hx i)) := by
  rw [L.portSet_flag hB A hi _ (Or.inl rfl), mem_union] at he
  have hZi1 : ∀ v, v ∈ L.Z (i + 1) → v ∉ L.reg i (att.hx i) := fun v hv h => by
    have := (L.mem_reg_Z hB (by omega) (by omega) hv).mp h; omega
  rcases he with he | he
  · rw [mem_cross] at he
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, hZi1 _ h2⟩
    · exact Or.inr ⟨h2, hZi1 _ h1⟩
  · cases att with
    | none => exact absurd he (notMem_empty _)
    | pa j => exact absurd he (notMem_empty _)
    | pb j =>
      dsimp only at he
      by_cases hij : i = j
      · rw [if_pos hij] at he
        have hflag : (Att.pb j).hx i = false := by simp [Att.hx, hij]
        simp only [hflag, Bool.false_eq_true, ite_false, mem_singleton] at he
        subst he
        have hs := A.case.1
        obtain ⟨-, -, -, -, hy, -, hα, -⟩ := A.pend hs
        have hx : A.x ∈ L.Z i := by rw [hij]; exact A.case.2.2.2.1
        have hyr : A.y ∉ L.reg i ((Att.pb j).hx i) := by
          rw [hflag]; intro h; have := (L.mem_reg_Y hB (by omega) (by omega) hy).mp h; simp at this
        rcases hα with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; rw [h1, h2]; exact ⟨hx, hyr⟩
        · right; rw [h1, h2]; exact ⟨hx, hyr⟩
      · rw [if_neg hij] at he; exact absurd he (notMem_empty _)

end Lay

end WaveTurbulence.TVine.Chart
