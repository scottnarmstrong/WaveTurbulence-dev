/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.CutCert
import Mathlib.Tactic

/-! # The inserted rungs of a cut slot are cuts (TARGET layervine, L1531)

If the two slot bonds form a cut of the template (a labelling `τ` into `{0, 2}` whose only crossing bonds are the
two slot bonds, with the slot ends `x, x'` on one side and `y, y'` on the other), then the `i`-th inserted rung
is the level-`1` set of a cut labelling of the inserted template.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence.Vine

/-- The `m`-th atom along a rail `a, g 0, …, g (k-1), b`. -/
@[expose] def railSeq (a b k : ℕ) (g : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j = 0 then a else if j ≤ k then g (j - 1) else b

theorem mem_railBonds_range {a b k : ℕ} {g : ℕ → ℕ} {e : ℕ × ℕ}
    (h : e ∈ railBonds a ((List.range k).map g) b) :
    ∃ m ≤ k, e = (railSeq a b k g m, railSeq a b k g (m + 1)) := by
  unfold railBonds at h
  rw [List.mem_iff_getElem] at h
  obtain ⟨i, hi, rfl⟩ := h
  have hi' : i < k + 1 := by simpa using hi
  refine ⟨i, by omega, ?_⟩
  simp only [List.getElem_zip]
  congr 1
  · cases i with
    | zero => simp [railSeq]
    | succ j =>
      simp only [railSeq, List.getElem_cons_succ, List.getElem_map, List.getElem_range]
      rw [if_neg (by omega), if_pos (by omega)]
      simp
  · simp only [railSeq, List.getElem_append, List.getElem_map, List.getElem_range]
    by_cases hik : i < k
    · rw [dif_pos (by simpa using hik), if_neg (by omega), if_pos (by omega)]; rfl
    · rw [dif_neg (by simpa using hik), if_neg (by omega), if_neg (by omega)]
      simp

/-- The labelling of the inserted template for the `i`-th rung (`1 ≤ i ≤ k`): rail positions before the rung get
`c₀`, the rung gets `1`, later positions get `c₁`. -/
@[expose] def rungσ (n k i c₀ c₁ : ℕ) (τ : ℕ → ℕ) (v : ℕ) : ℕ :=
  if v < n ∨ n + 2 * k ≤ v then τ v else
    let j := if v < n + k then v - n + 1 else v - n - k + 1
    if j < i then c₀ else if j = i then 1 else c₁

theorem rungσ_old {n k i c₀ c₁ : ℕ} {τ : ℕ → ℕ} {v : ℕ} (hv : v < n) : rungσ n k i c₀ c₁ τ v = τ v := by
  unfold rungσ; rw [if_pos (Or.inl hv)]

theorem rungσ_u {n k i c₀ c₁ : ℕ} {τ : ℕ → ℕ} {j : ℕ} (hj : j < k) :
    rungσ n k i c₀ c₁ τ (n + j) = if j + 1 < i then c₀ else if j + 1 = i then 1 else c₁ := by
  unfold rungσ
  rw [if_neg (by omega)]
  simp only [show n + j < n + k by omega, ite_true, show n + j - n + 1 = j + 1 by omega]

theorem rungσ_v {n k i c₀ c₁ : ℕ} {τ : ℕ → ℕ} {j : ℕ} (hj : j < k) :
    rungσ n k i c₀ c₁ τ (n + k + j) = if j + 1 < i then c₀ else if j + 1 = i then 1 else c₁ := by
  unfold rungσ
  rw [if_neg (by omega)]
  simp only [show ¬ (n + k + j < n + k) by omega, ite_false, show n + k + j - n - k + 1 = j + 1 by omega]

/-- The rung level of a rail position (`0` is the entry end, `k + 1` the exit end). -/
def railVal (k i c₀ c₁ : ℕ) (m : ℕ) : ℕ := if m < i then c₀ else if m = i then 1 else c₁

theorem railSeq_val {n k i c₀ c₁ : ℕ} {τ : ℕ → ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) {a b : ℕ}
    {g : ℕ → ℕ} (hg : ∀ j < k, rungσ n k i c₀ c₁ τ (g j) = railVal k i c₀ c₁ (j + 1))
    (ha : rungσ n k i c₀ c₁ τ a = c₀) (hb : rungσ n k i c₀ c₁ τ b = c₁) {m : ℕ} (hm : m ≤ k + 1) :
    rungσ n k i c₀ c₁ τ (railSeq a b k g m) = railVal k i c₀ c₁ m := by
  unfold railSeq railVal
  by_cases h0 : m = 0
  · subst h0; simp [ha]; omega
  · by_cases h1 : m ≤ k
    · rw [if_neg h0, if_pos h1, hg _ (by omega)]
      unfold railVal; congr 1 <;> simp [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)]
    · rw [if_neg h0, if_neg h1, hb]
      have : m = k + 1 := by omega
      subst this
      rw [if_neg (by omega), if_neg (by omega)]

theorem railVal_noCross {k i c₀ c₁ m : ℕ} (hc : (c₀ = 0 ∧ c₁ = 2) ∨ (c₀ = 2 ∧ c₁ = 0)) (hi : 1 ≤ i)
    (hm : m < k + 1) : ¬ (((railVal k i c₀ c₁ m = 0 ∧ railVal k i c₀ c₁ (m + 1) = 2)) ∨
      (railVal k i c₀ c₁ m = 2 ∧ railVal k i c₀ c₁ (m + 1) = 0)) := by
  unfold railVal
  rcases hc with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> subst h0 <;> subst h1 <;> split_ifs <;> simp_all <;> omega

theorem rung_cert {T : VineTemplate} {s : (ℕ × ℕ) × (ℕ × ℕ)} {k i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k)
    (hc1 : T.bonds.count s.1 ≤ 1) (hc2 : T.bonds.count s.2 ≤ 1)
    (hbdd : ∀ e ∈ T.bonds, e.1 < T.n ∧ e.2 < T.n) (hends : ∀ v ∈ slotEnds s, v < T.n)
    {τ : ℕ → ℕ} {c₀ c₁ : ℕ} (hc : (c₀ = 0 ∧ c₁ = 2) ∨ (c₀ = 2 ∧ c₁ = 0))
    (hx : τ s.1.1 = c₀ ∧ τ s.2.1 = c₀) (hy : τ s.1.2 = c₁ ∧ τ s.2.2 = c₁)
    (hτ : CutOn T.bonds [s.1, s.2] τ) :
    CutOn (insertRungs T s k).bonds [] (rungσ T.n k i c₀ c₁ τ) := by
  have hk : k ≠ 0 := by omega
  have hxn : s.1.1 < T.n := hends _ (by simp [slotEnds])
  have hyn : s.1.2 < T.n := hends _ (by simp [slotEnds])
  have hxn' : s.2.1 < T.n := hends _ (by simp [slotEnds])
  have hyn' : s.2.2 < T.n := hends _ (by simp [slotEnds])
  intro e he _
  rcases mem_insertRungs_cases hk hc1 hc2 he with ⟨he1, h1, h2⟩ | he | he | ⟨j, hj, rfl⟩
  · have hb := hbdd e he1
    unfold Crosses
    rw [rungσ_old hb.1, rungσ_old hb.2]
    exact hτ e he1 (by simp [h1, h2])
  · obtain ⟨m, hm, rfl⟩ := mem_railBonds_range he
    have hv := fun m' (hm' : m' ≤ k + 1) => railSeq_val (n := T.n) (τ := τ) (c₀ := c₀) (c₁ := c₁) hi1 hik
      (g := fun j => T.n + j) (a := s.1.1) (b := s.1.2) (fun j hj => by
        rw [rungσ_u hj]; unfold railVal; rfl)
      (by rw [rungσ_old hxn]; exact hx.1) (by rw [rungσ_old hyn]; exact hy.1) hm'
    unfold Crosses
    simp only
    rw [hv m (by omega), hv (m + 1) (by omega)]
    exact railVal_noCross hc hi1 (by omega)
  · obtain ⟨m, hm, rfl⟩ := mem_railBonds_range he
    have hv := fun m' (hm' : m' ≤ k + 1) => railSeq_val (n := T.n) (τ := τ) (c₀ := c₀) (c₁ := c₁) hi1 hik
      (g := fun j => T.n + k + j) (a := s.2.1) (b := s.2.2) (fun j hj => by
        rw [rungσ_v hj]; unfold railVal; rfl)
      (by rw [rungσ_old hxn']; exact hx.2) (by rw [rungσ_old hyn']; exact hy.2) hm'
    unfold Crosses
    simp only
    rw [hv m (by omega), hv (m + 1) (by omega)]
    exact railVal_noCross hc hi1 (by omega)
  · unfold Crosses
    simp only
    rw [rungσ_u hj, rungσ_v hj]
    split_ifs <;> omega

end WaveTurbulence.LayerCnt
