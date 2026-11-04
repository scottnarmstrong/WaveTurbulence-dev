/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.RegularHeldOut

/-!
# DH21 Lemma 6.6 (`auxlem`) and its weighted form (packet C2)

For a ternary tree `𝒯` of order `n`, let `μ_𝔫` be the number of leaves below `𝔫` and `μ°_𝔫` the
second largest of the values `μ_𝔪` over the children `𝔪` of `𝔫`. Then (DH21 Lemma 6.6, L1659–L1664)
`∏_{𝔫 ∈ 𝒩} μ°_𝔫 ≤ 3^n / (2n+1)`.

The weighted form (used in DH23 Lemma A.4 (2), L2116–L2127): with leaf weights `w_ℓ ≥ 1` and
`μ_𝔫 = ∑_{ℓ below 𝔫} w_ℓ`, `∏_{𝔫} μ°_𝔫 ≤ 3^n ∏_ℓ w_ℓ / ∑_ℓ w_ℓ` (`auxProd_mul_wsum_le`).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree

/-- The second largest of three reals. -/
def secondMax (a b c : ℝ) : ℝ := max (min a b) (min (max a b) c)

theorem secondMax_mul_sum_le {a b c : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    secondMax a b c * (a + b + c) ≤ 3 * (a * b * c) := by
  unfold secondMax
  rcases le_total a b with h1 | h1 <;> rcases le_total b c with h2 | h2 <;>
    rcases le_total a c with h3 | h3 <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h1, h2, h3] <;>
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ c),
      mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1) (by linarith : (0 : ℝ) ≤ b - 1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1) (by linarith : (0 : ℝ) ≤ c - 1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ b - 1) (by linarith : (0 : ℝ) ≤ c - 1),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ a) (by linarith : (0 : ℝ) ≤ b))
        (by linarith : (0 : ℝ) ≤ c - 1),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ a) (by linarith : (0 : ℝ) ≤ c))
        (by linarith : (0 : ℝ) ≤ b - 1),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ b) (by linarith : (0 : ℝ) ≤ c))
        (by linarith : (0 : ℝ) ≤ a - 1)]

theorem secondMax_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : 0 ≤ c) :
    0 ≤ secondMax a b c :=
  le_max_of_le_left (le_min ha hb)

/-- Weights below the `i`-th child. -/
def shiftW (w : Path → ℝ) (i : Fin 3) : Path → ℝ := fun p => w (i :: p)

/-- `μ`: the total weight of the leaves of `t` (leaf `p` has weight `w p`). -/
def wsum : TTree → (Path → ℝ) → ℝ
  | .leaf, w => w []
  | .node l m r, w => wsum l (shiftW w 0) + wsum m (shiftW w 1) + wsum r (shiftW w 2)

/-- `∏_ℓ w_ℓ` over the leaves of `t`. -/
def wprod : TTree → (Path → ℝ) → ℝ
  | .leaf, w => w []
  | .node l m r, w => wprod l (shiftW w 0) * wprod m (shiftW w 1) * wprod r (shiftW w 2)

/-- `∏_{𝔫 ∈ 𝒩} μ°_𝔫`. -/
def auxProd : TTree → (Path → ℝ) → ℝ
  | .leaf, _ => 1
  | .node l m r, w =>
    secondMax (wsum l (shiftW w 0)) (wsum m (shiftW w 1)) (wsum r (shiftW w 2)) *
      auxProd l (shiftW w 0) * auxProd m (shiftW w 1) * auxProd r (shiftW w 2)

/-- Weights `≥ 1` at every leaf of `t`. -/
def WeightsGeOne (t : TTree) (w : Path → ℝ) : Prop := ∀ p ∈ t.leaves, 1 ≤ w p

theorem weightsGeOne_child {l m r : TTree} {w : Path → ℝ} (h : WeightsGeOne (.node l m r) w) :
    WeightsGeOne l (shiftW w 0) ∧ WeightsGeOne m (shiftW w 1) ∧ WeightsGeOne r (shiftW w 2) := by
  refine ⟨fun p hp => h _ ?_, fun p hp => h _ ?_, fun p hp => h _ ?_⟩ <;>
    simp [TTree.leaves, TTree.pre, hp]

theorem one_le_wsum : ∀ (t : TTree) (w : Path → ℝ), WeightsGeOne t w → 1 ≤ wsum t w
  | .leaf, w, h => h [] (by simp [TTree.leaves])
  | .node l m r, w, h => by
    obtain ⟨h₁, h₂, h₃⟩ := weightsGeOne_child h
    have := one_le_wsum l _ h₁; have := one_le_wsum m _ h₂; have := one_le_wsum r _ h₃
    simp only [wsum]; linarith

theorem one_le_wprod : ∀ (t : TTree) (w : Path → ℝ), WeightsGeOne t w → 1 ≤ wprod t w
  | .leaf, w, h => h [] (by simp [TTree.leaves])
  | .node l m r, w, h => by
    obtain ⟨h₁, h₂, h₃⟩ := weightsGeOne_child h
    have a := one_le_wprod l _ h₁; have b := one_le_wprod m _ h₂; have c := one_le_wprod r _ h₃
    simp only [wprod]
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr

theorem auxProd_nonneg : ∀ (t : TTree) (w : Path → ℝ), WeightsGeOne t w → 0 ≤ auxProd t w
  | .leaf, _, _ => zero_le_one
  | .node l m r, w, h => by
    obtain ⟨h₁, h₂, h₃⟩ := weightsGeOne_child h
    simp only [auxProd]
    have := secondMax_nonneg (le_trans zero_le_one (one_le_wsum l _ h₁))
      (le_trans zero_le_one (one_le_wsum m _ h₂)) (le_trans zero_le_one (one_le_wsum r _ h₃))
    have := auxProd_nonneg l _ h₁; have := auxProd_nonneg m _ h₂; have := auxProd_nonneg r _ h₃
    positivity

/-- **Weighted `auxlem`** (DH21 Lemma 6.6; DH23 Lemma A.4 (2)): for leaf weights `≥ 1`,
`(∏_{𝔫} μ°_𝔫) · ∑_ℓ w_ℓ ≤ 3^n ∏_ℓ w_ℓ`. -/
theorem auxProd_mul_wsum_le : ∀ (t : TTree) (w : Path → ℝ), WeightsGeOne t w →
    auxProd t w * wsum t w ≤ 3 ^ t.order * wprod t w
  | .leaf, w, _ => by simp [auxProd, wsum, wprod, TTree.order]
  | .node l m r, w, h => by
    obtain ⟨h₁, h₂, h₃⟩ := weightsGeOne_child h
    have i₁ := auxProd_mul_wsum_le l _ h₁
    have i₂ := auxProd_mul_wsum_le m _ h₂
    have i₃ := auxProd_mul_wsum_le r _ h₃
    have s₁ := one_le_wsum l _ h₁; have s₂ := one_le_wsum m _ h₂; have s₃ := one_le_wsum r _ h₃
    have a₁ := auxProd_nonneg l _ h₁; have a₂ := auxProd_nonneg m _ h₂
    have a₃ := auxProd_nonneg r _ h₃
    set S₁ := wsum l (shiftW w 0); set S₂ := wsum m (shiftW w 1); set S₃ := wsum r (shiftW w 2)
    set A₁ := auxProd l (shiftW w 0); set A₂ := auxProd m (shiftW w 1)
    set A₃ := auxProd r (shiftW w 2)
    have key := secondMax_mul_sum_le s₁ s₂ s₃
    have hsm := secondMax_nonneg (by linarith : (0 : ℝ) ≤ S₁) (by linarith : (0 : ℝ) ≤ S₂)
      (by linarith : (0 : ℝ) ≤ S₃)
    simp only [auxProd, wsum, wprod, TTree.order]
    calc secondMax S₁ S₂ S₃ * A₁ * A₂ * A₃ * (S₁ + S₂ + S₃)
        = (secondMax S₁ S₂ S₃ * (S₁ + S₂ + S₃)) * (A₁ * A₂ * A₃) := by ring
      _ ≤ (3 * (S₁ * S₂ * S₃)) * (A₁ * A₂ * A₃) := by gcongr
      _ = 3 * ((A₁ * S₁) * (A₂ * S₂) * (A₃ * S₃)) := by ring
      _ ≤ 3 * ((3 ^ l.order * wprod l (shiftW w 0)) * (3 ^ m.order * wprod m (shiftW w 1)) *
            (3 ^ r.order * wprod r (shiftW w 2))) := by
          have hP₁ : 0 ≤ 3 ^ l.order * wprod l (shiftW w 0) :=
            mul_nonneg (by positivity) (le_trans zero_le_one (one_le_wprod l _ h₁))
          have hP₂ : 0 ≤ 3 ^ m.order * wprod m (shiftW w 1) :=
            mul_nonneg (by positivity) (le_trans zero_le_one (one_le_wprod m _ h₂))
          exact mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul i₁ i₂
            (mul_nonneg a₂ (by linarith)) hP₁) i₃ (mul_nonneg a₃ (by linarith))
            (mul_nonneg hP₁ hP₂)) (by norm_num)
      _ = _ := by ring

/-- The number of leaves of `t` (`μ` with unit weights) is `2n + 1`. -/
theorem wsum_one : ∀ t : TTree, wsum t (fun _ => 1) = 2 * t.order + 1
  | .leaf => by simp [wsum, TTree.order]
  | .node l m r => by
    have e : ∀ i, shiftW (fun _ : Path => (1 : ℝ)) i = fun _ => 1 := fun _ => rfl
    simp only [wsum, e, TTree.order]
    rw [wsum_one l, wsum_one m, wsum_one r]
    push_cast; ring

theorem wprod_one : ∀ t : TTree, wprod t (fun _ => 1) = 1
  | .leaf => by simp [wprod]
  | .node l m r => by
    have e : ∀ i, shiftW (fun _ : Path => (1 : ℝ)) i = fun _ => 1 := fun _ => rfl
    simp only [wprod, e]; rw [wprod_one l, wprod_one m, wprod_one r]; ring

/-- **DH21 Lemma 6.6** (`auxlem`, L1659–L1664): `∏_{𝔫 ∈ 𝒩} μ°_𝔫 ≤ 3^n / (2n+1)`, in the form
`(∏_{𝔫} μ°_𝔫) (2n+1) ≤ 3^n`, where `μ_𝔫` counts the leaves below `𝔫` and `μ°_𝔫` is the second
largest of the `μ` of the children of `𝔫`. -/
theorem auxlem (t : TTree) : auxProd t (fun _ => 1) * (2 * t.order + 1) ≤ 3 ^ t.order := by
  have h := auxProd_mul_wsum_le t (fun _ => 1) (fun _ _ => le_rfl)
  rw [wsum_one, wprod_one, mul_one] at h
  exact h

end WaveTurbulence.Links
