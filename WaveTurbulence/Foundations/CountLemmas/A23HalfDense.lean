/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.CountLemmas.A23HalfFibers
public import WaveTurbulence.Foundations.Counting.EstcrossBalls

/-!
# The anti-parallel form `ζ = x − v`: dense fibers (estcross and a layer-cake sum)

* `card_dense_ysF_le`: DH23 `estcross` (landed `Counting.card_dense_dot_product_strips_in_balls_le`), rescaled to the
  unit-scale fibers: `#{x : N_y(x) ≥ L^{d-1}/θ} ≤ K(ρ^d + L^{d-2}ρ²θ²(1 + log L)²)`, `ρ = τL²`;
* `sum_mul_card_le_layer`: the layer-cake identity `∑_x f(x) = ∑_{k ≥ 1} #{x : f(x) ≥ k}`;
* **`sum_dense_card_ysF_le`**: `∑_{x : N_y(x) ≥ k₀} N_y(x) ≤ k₀ E(θ₀) + M K(ρ^d + L^{d-2}ρ²lg²) + K L^{3d-4}ρ²lg²/k₀`,
  with `θ₀ = max(1, L^{d-1}/k₀)`, `M` a bound for `N_y` (referee §4.3(iv)(B), the dyadic `θ` replaced by the
  layer-cake sum over `k = L^{d-1}/θ`).
-/

public section

open Finset Set

namespace WaveTurbulence.CountLemmas

variable {d : ℕ}

/-- The estcross constant for dimension `n + 3`. -/
@[expose] noncomputable def estcrossConst (n : ℕ) : ℝ := (5 : ℝ) ^ (n + 3) + (n + 3) * 129600 * ((3 : ℝ) ^ (n + 1)) ^ 3

theorem estcrossConst_nonneg (n : ℕ) : 0 ≤ estcrossConst n := by unfold estcrossConst; positivity

theorem latticePoint_one_eq_smul {L : ℝ} (hL : 0 < L) (X : Fin d → ℤ) :
    latticePoint 1 X = L • latticePoint L X := by
  ext i
  simp only [latticePoint, PiLp.smul_apply, smul_eq_mul, div_one]
  field_simp

/-- **Estcross for the unit-scale fibers** (`d = n + 3`). -/
theorem card_dense_ysF_le {n : ℕ} {L τ θ : ℝ} (hL : 0 < L) (hτ : 0 ≤ τ) (hθ : 1 ≤ θ)
    (hscale : 16 * ((3 : ℝ) ^ (n + 1) * θ) ≤ τ * L ^ 2) (hρL : τ * L ^ 2 ≤ L)
    (a b : Mom (n + 3)) (α : ℝ) :
    (((nearFinset L a).filter fun X => L ^ (n + 2) / θ ≤ ((ysF L b α τ X).card : ℝ)).card : ℝ) ≤
      estcrossConst n * ((τ * L ^ 2) ^ (n + 3) + L ^ (n + 1) * (τ * L ^ 2) ^ 2 * θ ^ 2 *
        (1 + Real.log L) ^ 2) := by
  classical
  refine Counting.card_dense_dot_product_strips_in_balls_le _ (L • a) (by positivity) hθ hscale hρL
    (fun X hX => ?_) (fun X hX => ?_)
  · have hX := (mem_nearFinset hL a X).mp (Finset.mem_filter.mp hX).1
    rw [latticePoint_one_eq_smul hL, ← smul_sub, norm_smul, Real.norm_of_nonneg hL.le]
    simpa using mul_le_mul_of_nonneg_left hX hL.le
  · refine ⟨ysF L b α τ X, L • b, L ^ 2 * α, fun Y hY => ?_, fun Y hY => ?_, (Finset.mem_filter.mp hX).2⟩
    · have hY := (mem_nearFinset hL b Y).mp (Finset.mem_filter.mp hY).1
      rw [latticePoint_one_eq_smul hL, ← smul_sub, norm_smul, Real.norm_of_nonneg hL.le]
      simpa using mul_le_mul_of_nonneg_left hY hL.le
    · have hs := (Finset.mem_filter.mp hY).2
      rw [latticePoint_one_eq_smul hL, latticePoint_one_eq_smul hL, inner_smul_left, inner_smul_right]
      simp only [RCLike.conj_to_real]
      have he : L * (L * inner ℝ (latticePoint L X) (latticePoint L Y)) - L ^ 2 * α =
          L ^ 2 * (inner ℝ (latticePoint L X) (latticePoint L Y) - α) := by ring
      rw [he, abs_mul, abs_of_nonneg (sq_nonneg L)]
      exact mul_le_mul_of_nonneg_left hs (sq_nonneg L) |>.trans (by rw [mul_comm])

/-- The layer-cake identity for natural-valued functions bounded by `M`. -/
theorem sum_eq_sum_card_ge {α : Type*} (s : Finset α) (f : α → ℕ) (M : ℕ) (hf : ∀ x ∈ s, f x ≤ M) :
    ∑ x ∈ s, (f x : ℝ) = ∑ k ∈ Finset.Icc 1 M, ((s.filter fun x => k ≤ f x).card : ℝ) := by
  classical
  have h1 : ∀ x ∈ s, (f x : ℝ) = ∑ k ∈ Finset.Icc 1 M, if k ≤ f x then (1 : ℝ) else 0 := by
    intro x hx
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (Finset.Icc 1 M).filter (fun k => k ≤ f x) = Finset.Icc 1 (f x) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans (hf x hx)⟩, h2⟩
    rw [this, Nat.card_Icc]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.card_filter]
  push_cast
  rfl

theorem sum_inv_sq_Ioc_le_aux {k₀ : ℕ} (hk : 1 ≤ k₀) : ∀ M : ℕ,
    ∑ k ∈ Finset.Ioc k₀ M, ((k : ℝ) ^ 2)⁻¹ ≤ (k₀ : ℝ)⁻¹ - ((max k₀ M : ℕ) : ℝ)⁻¹
  | 0 => by simp
  | M + 1 => by
    by_cases hM : k₀ ≤ M
    · rw [Finset.sum_Ioc_succ_top (by omega)]
      have ih := sum_inv_sq_Ioc_le_aux hk M
      rw [max_eq_right hM] at ih
      rw [max_eq_right (by omega : k₀ ≤ M + 1)]
      have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
      have hstep : (((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ (M : ℝ)⁻¹ - ((M + 1 : ℕ) : ℝ)⁻¹ := by
        push_cast
        rw [inv_sub_inv hMp.ne' (by positivity), show (M : ℝ) + 1 - M = 1 by ring, one_div]
        apply inv_anti₀ (by positivity)
        nlinarith
      linarith
    · have hk' : max k₀ (M + 1) = k₀ := max_eq_left (by omega)
      have hIoc : Finset.Ioc k₀ (M + 1) = ∅ := by
        ext k; simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false]; omega
      rw [hIoc, hk']
      simp

/-- `∑_{k₀ < k ≤ M} k^{-2} ≤ 1/k₀`. -/
theorem sum_inv_sq_Ioc_le {k₀ : ℕ} (hk : 1 ≤ k₀) (M : ℕ) :
    ∑ k ∈ Finset.Ioc k₀ M, ((k : ℝ) ^ 2)⁻¹ ≤ (k₀ : ℝ)⁻¹ := by
  refine (sum_inv_sq_Ioc_le_aux hk M).trans ?_
  have : (0 : ℝ) ≤ ((max k₀ M : ℕ) : ℝ)⁻¹ := by positivity
  linarith

/-- **The dense fibers**: `∑_{x ∈ t, k₀ ≤ N_y(x)} N_y(x)` (`d = n + 3`). -/
theorem sum_dense_card_ysF_le {n : ℕ} {L τ : ℝ} (hL : 1 ≤ L) (hτ : 0 ≤ τ) {k₀ M : ℕ} (hk : 1 ≤ k₀)
    (hscale : 16 * ((3 : ℝ) ^ (n + 1) * max 1 (L ^ (n + 2) / k₀)) ≤ τ * L ^ 2) (hρL : τ * L ^ 2 ≤ L)
    (a b : Mom (n + 3)) (α : ℝ) (t : Finset (Fin (n + 3) → ℤ)) (ht : t ⊆ nearFinset L a)
    (hM : ∀ X ∈ t, (ysF L b α τ X).card ≤ M) :
    ∑ X ∈ t.filter (fun X => k₀ ≤ (ysF L b α τ X).card), ((ysF L b α τ X).card : ℝ) ≤
      k₀ * (estcrossConst n * ((τ * L ^ 2) ^ (n + 3) + L ^ (n + 1) * (τ * L ^ 2) ^ 2 *
          max 1 (L ^ (n + 2) / k₀) ^ 2 * (1 + Real.log L) ^ 2)) +
      M * (estcrossConst n * ((τ * L ^ 2) ^ (n + 3) + L ^ (n + 1) * (τ * L ^ 2) ^ 2 * (1 + Real.log L) ^ 2)) +
      estcrossConst n * L ^ (n + 1) * (τ * L ^ 2) ^ 2 * (1 + Real.log L) ^ 2 * (L ^ (n + 2)) ^ 2 * (k₀ : ℝ)⁻¹ := by
  classical
  have hLp : 0 < L := by linarith
  set N := fun X => (ysF L b α τ X).card
  set t' := t.filter (fun X => k₀ ≤ N X)
  set K := estcrossConst n
  set ρ := τ * L ^ 2
  set lg := (1 + Real.log L) ^ 2
  have hlg : 0 ≤ lg := sq_nonneg _
  have hK := estcrossConst_nonneg n
  -- estcross at `θ = max 1 (L^{n+2}/k)` for `k ≥ k₀`
  have hE : ∀ k : ℕ, k₀ ≤ k → ((nearFinset L a).filter fun X => k ≤ N X).card ≤
      K * (ρ ^ (n + 3) + L ^ (n + 1) * ρ ^ 2 * max 1 (L ^ (n + 2) / k) ^ 2 * lg) := by
    intro k hk'
    have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hθ : max 1 (L ^ (n + 2) / k) ≤ max 1 (L ^ (n + 2) / k₀) :=
      max_le_max le_rfl (div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hk)
        (by exact_mod_cast hk'))
    have hsc : 16 * ((3 : ℝ) ^ (n + 1) * max 1 (L ^ (n + 2) / k)) ≤ ρ :=
      le_trans (by gcongr) hscale
    have hsub : ((nearFinset L a).filter fun X => k ≤ N X) ⊆
        (nearFinset L a).filter fun X => L ^ (n + 2) / max 1 (L ^ (n + 2) / k) ≤ ((ysF L b α τ X).card : ℝ) := by
      intro X hX
      obtain ⟨hX1, hX2⟩ := Finset.mem_filter.mp hX
      refine Finset.mem_filter.mpr ⟨hX1, ?_⟩
      have h1 : L ^ (n + 2) / max 1 (L ^ (n + 2) / k) ≤ k := by
        rw [div_le_iff₀ (by positivity)]
        calc L ^ (n + 2) = k * (L ^ (n + 2) / k) := by field_simp
          _ ≤ k * max 1 (L ^ (n + 2) / k) := mul_le_mul_of_nonneg_left (le_max_right _ _) hkp.le
      exact h1.trans (by exact_mod_cast hX2)
    have hc := card_dense_ysF_le hLp hτ (le_max_left _ _) hsc hρL a b α
    exact (by exact_mod_cast Finset.card_le_card hsub : (((nearFinset L a).filter fun X => k ≤ N X).card : ℝ) ≤
      _).trans hc
  have hMt' : ∀ X ∈ t', N X ≤ M := fun X hX => hM X (Finset.mem_filter.mp hX).1
  rw [sum_eq_sum_card_ge t' N M hMt']
  -- split the layers at `k₀`
  have hsplit : ∀ k ∈ Finset.Icc 1 M, ((t'.filter fun X => k ≤ N X).card : ℝ) ≤
      (if k ≤ k₀ then K * (ρ ^ (n + 3) + L ^ (n + 1) * ρ ^ 2 * max 1 (L ^ (n + 2) / k₀) ^ 2 * lg) else
        K * (ρ ^ (n + 3) + L ^ (n + 1) * ρ ^ 2 * lg) + K * L ^ (n + 1) * ρ ^ 2 * lg * (L ^ (n + 2)) ^ 2 *
          ((k : ℝ) ^ 2)⁻¹) := by
    intro k hk'
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk').1
    split_ifs with hkk
    · have hsub : t'.filter (fun X => k ≤ N X) ⊆ (nearFinset L a).filter fun X => k₀ ≤ N X := by
        intro X hX
        have hX' := Finset.mem_filter.mp (Finset.mem_filter.mp hX).1
        exact Finset.mem_filter.mpr ⟨ht hX'.1, hX'.2⟩
      exact (by exact_mod_cast Finset.card_le_card hsub : ((t'.filter fun X => k ≤ N X).card : ℝ) ≤ _).trans
        (hE k₀ le_rfl)
    · have hsub : t'.filter (fun X => k ≤ N X) ⊆ (nearFinset L a).filter fun X => k ≤ N X := by
        intro X hX
        have hX' := Finset.mem_filter.mp hX
        exact Finset.mem_filter.mpr ⟨ht (Finset.mem_filter.mp hX'.1).1, hX'.2⟩
      refine (by exact_mod_cast Finset.card_le_card hsub : ((t'.filter fun X => k ≤ N X).card : ℝ) ≤ _).trans
        ((hE k (by omega)).trans ?_)
      have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hθ2 : max 1 (L ^ (n + 2) / k) ^ 2 ≤ 1 + (L ^ (n + 2)) ^ 2 * ((k : ℝ) ^ 2)⁻¹ := by
        rcases le_total 1 (L ^ (n + 2) / k) with h | h
        · rw [max_eq_right h, div_pow, div_eq_mul_inv]; linarith [show (0 : ℝ) ≤ 1 from zero_le_one]
        · rw [max_eq_left h]; nlinarith [show (0 : ℝ) ≤ (L ^ (n + 2)) ^ 2 * ((k : ℝ) ^ 2)⁻¹ by positivity]
      have hA : 0 ≤ K * L ^ (n + 1) * ρ ^ 2 * lg := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hθ2 hA]
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [Finset.sum_ite]
  have hlow : ((Finset.Icc 1 M).filter fun k => k ≤ k₀).card ≤ k₀ := by
    calc _ ≤ (Finset.Icc 1 k₀).card := Finset.card_le_card (fun k hk => by
          simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢; omega)
      _ = k₀ := by simp
  have hhigh : (Finset.Icc 1 M).filter (fun k => ¬ k ≤ k₀) = Finset.Ioc k₀ M := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [Finset.sum_const, nsmul_eq_mul, hhigh, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum]
  have hIoc : ((Finset.Ioc k₀ M).card : ℝ) ≤ M := by
    rw [Nat.card_Ioc]
    exact_mod_cast Nat.sub_le M k₀
  have hE0 : 0 ≤ K * (ρ ^ (n + 3) + L ^ (n + 1) * ρ ^ 2 * max 1 (L ^ (n + 2) / k₀) ^ 2 * lg) := by positivity
  have hE1 : 0 ≤ K * (ρ ^ (n + 3) + L ^ (n + 1) * ρ ^ 2 * lg) := by positivity
  have hE2 : 0 ≤ K * L ^ (n + 1) * ρ ^ 2 * lg * (L ^ (n + 2)) ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_right (show (((Finset.Icc 1 M).filter fun k => k ≤ k₀).card : ℝ) ≤ k₀ by
    exact_mod_cast hlow) hE0
  have h2 := mul_le_mul_of_nonneg_right hIoc hE1
  have h3 := mul_le_mul_of_nonneg_left (sum_inv_sq_Ioc_le hk M) hE2
  linarith

end WaveTurbulence.CountLemmas
