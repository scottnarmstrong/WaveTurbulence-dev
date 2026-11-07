/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.KCutExt
import Mathlib.Tactic

/-! # Rail-position cuts of an inserted ladder (TARGET layervine, L1531)

Cutting the two rails of an inserted ladder between positions `j` and `j + 1` (`0 ≤ j ≤ k`, position `0` the entry end,
`k + 1` the exit end) gives a cut with two single crossing bonds: the two rail bonds at position `j`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence.Vine

/-- The labelling of the inserted template for the cut at position `j`: positions `≤ j` get `c₀`, later ones `c₁`. -/
@[expose] def posσ (n k j c₀ c₁ : ℕ) (τ : ℕ → ℕ) (v : ℕ) : ℕ :=
  if v < n ∨ n + 2 * k ≤ v then τ v else
    let m := if v < n + k then v - n + 1 else v - n - k + 1
    if m ≤ j then c₀ else c₁

theorem posσ_old {n k j c₀ c₁ : ℕ} {τ : ℕ → ℕ} {v : ℕ} (hv : v < n) : posσ n k j c₀ c₁ τ v = τ v := by
  unfold posσ; rw [if_pos (Or.inl hv)]

theorem posσ_u {n k j c₀ c₁ : ℕ} {τ : ℕ → ℕ} {i : ℕ} (hi : i < k) :
    posσ n k j c₀ c₁ τ (n + i) = if i + 1 ≤ j then c₀ else c₁ := by
  unfold posσ
  rw [if_neg (by omega)]
  simp only [show n + i < n + k by omega, ite_true, show n + i - n + 1 = i + 1 by omega]

theorem posσ_v {n k j c₀ c₁ : ℕ} {τ : ℕ → ℕ} {i : ℕ} (hi : i < k) :
    posσ n k j c₀ c₁ τ (n + k + i) = if i + 1 ≤ j then c₀ else c₁ := by
  unfold posσ
  rw [if_neg (by omega)]
  simp only [show ¬ (n + k + i < n + k) by omega, ite_false, show n + k + i - n - k + 1 = i + 1 by omega]

/-- The position value along a rail. -/
@[expose] def posVal (j c₀ c₁ m : ℕ) : ℕ := if m ≤ j then c₀ else c₁

theorem railSeq_posVal {n k j c₀ c₁ : ℕ} {τ : ℕ → ℕ} {a b : ℕ} {g : ℕ → ℕ}
    (hg : ∀ i < k, posσ n k j c₀ c₁ τ (g i) = posVal j c₀ c₁ (i + 1))
    (ha : posσ n k j c₀ c₁ τ a = c₀) (hb : posσ n k j c₀ c₁ τ b = c₁) (hj : j ≤ k) {m : ℕ} (hm : m ≤ k + 1) :
    posσ n k j c₀ c₁ τ (railSeq a b k g m) = posVal j c₀ c₁ m := by
  unfold railSeq posVal
  by_cases h0 : m = 0
  · subst h0; simp [ha]
  · by_cases h1 : m ≤ k
    · rw [if_neg h0, if_pos h1, hg _ (by omega)]
      unfold posVal; congr 1 <;> simp [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)]
    · rw [if_neg h0, if_neg h1, hb]
      have : m = k + 1 := by omega
      subst this
      rw [if_neg (by omega)]

/-- The two rail bonds at position `j`. -/
@[expose] def railEdge (a b k : ℕ) (g : ℕ → ℕ) (j : ℕ) : ℕ × ℕ := (railSeq a b k g j, railSeq a b k g (j + 1))

theorem pos_cuton {T : VineTemplate} {s : (ℕ × ℕ) × (ℕ × ℕ)} {k j : ℕ} (hj : j ≤ k) (hk : k ≠ 0)
    (hc1 : T.bonds.count s.1 ≤ 1) (hc2 : T.bonds.count s.2 ≤ 1)
    (hbdd : ∀ e ∈ T.bonds, e.1 < T.n ∧ e.2 < T.n) (hends : ∀ v ∈ slotEnds s, v < T.n)
    {τ : ℕ → ℕ} {c₀ c₁ : ℕ} (hc : (c₀ = 0 ∧ c₁ = 2) ∨ (c₀ = 2 ∧ c₁ = 0))
    (hx : τ s.1.1 = c₀ ∧ τ s.2.1 = c₀) (hy : τ s.1.2 = c₁ ∧ τ s.2.2 = c₁)
    (hτ : CutOn T.bonds [s.1, s.2] τ) :
    CutOn (insertRungs T s k).bonds
      [railEdge s.1.1 s.1.2 k (fun i => T.n + i) j, (railSeq s.1.1 s.1.2 k (fun i => T.n + i) (j + 1),
          railSeq s.1.1 s.1.2 k (fun i => T.n + i) j),
        railEdge s.2.1 s.2.2 k (fun i => T.n + k + i) j, (railSeq s.2.1 s.2.2 k (fun i => T.n + k + i) (j + 1),
          railSeq s.2.1 s.2.2 k (fun i => T.n + k + i) j)] (posσ T.n k j c₀ c₁ τ) := by
  have hxn : s.1.1 < T.n := hends _ (by simp [slotEnds])
  have hyn : s.1.2 < T.n := hends _ (by simp [slotEnds])
  have hxn' : s.2.1 < T.n := hends _ (by simp [slotEnds])
  have hyn' : s.2.2 < T.n := hends _ (by simp [slotEnds])
  intro e he hnE
  rcases mem_insertRungs_cases hk hc1 hc2 he with ⟨he1, h1, h2⟩ | he | he | ⟨i, hi, rfl⟩
  · have hb := hbdd e he1
    unfold Crosses
    rw [posσ_old hb.1, posσ_old hb.2]
    exact hτ e he1 (by simp [h1, h2])
  · obtain ⟨m, hm, rfl⟩ := mem_railBonds_range he
    have hv := fun m' (hm' : m' ≤ k + 1) => railSeq_posVal (n := T.n) (τ := τ) (c₀ := c₀) (c₁ := c₁)
      (j := j) (g := fun i => T.n + i) (a := s.1.1) (b := s.1.2) (fun i hi => by
        rw [posσ_u hi]; unfold posVal; rfl)
      (by rw [posσ_old hxn]; exact hx.1) (by rw [posσ_old hyn]; exact hy.1) hj hm'
    unfold Crosses
    simp only
    rw [hv m (by omega), hv (m + 1) (by omega)]
    intro hcr
    by_cases hmj : m = j
    · subst hmj; exact hnE (by simp [railEdge])
    · unfold posVal at hcr; split_ifs at hcr <;> omega
  · obtain ⟨m, hm, rfl⟩ := mem_railBonds_range he
    have hv := fun m' (hm' : m' ≤ k + 1) => railSeq_posVal (n := T.n) (τ := τ) (c₀ := c₀) (c₁ := c₁)
      (j := j) (g := fun i => T.n + k + i) (a := s.2.1) (b := s.2.2) (fun i hi => by
        rw [posσ_v hi]; unfold posVal; rfl)
      (by rw [posσ_old hxn']; exact hx.2) (by rw [posσ_old hyn']; exact hy.2) hj hm'
    unfold Crosses
    simp only
    rw [hv m (by omega), hv (m + 1) (by omega)]
    intro hcr
    by_cases hmj : m = j
    · subst hmj; exact hnE (by simp [railEdge])
    · unfold posVal at hcr; split_ifs at hcr <;> omega
  · unfold Crosses
    simp only
    rw [posσ_u hi, posσ_v hi]
    split_ifs <;> omega

end WaveTurbulence.LayerCnt
