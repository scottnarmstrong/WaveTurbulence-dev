/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.SchwartzValued
public import WaveTurbulence.Frozen.Defs.IsWKESolution
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniqueness of Schwartz solutions of (WKE)

`isWKESolution_unique`: two Schwartz-class solutions (`IsWKESolution`) with the same data agree
on `[0, τ★]` (the uniqueness part of TARGET Prop `wkelwp`, L598–L601; Appendix C, L2526).

The proof: continuity into `𝓢` gives a uniform bound `|φ(τ, y)| ≤ R (1 + |y|)^{-s}`, `s = 2d + 1`,
on `[0, τ★]`; the weighted-sup trilinear estimate makes `𝒦` Lipschitz,
`(1 + |k|)^s |𝒦(a,a,a)(k) - 𝒦(b,b,b)(k)| ≤ K sup_y (1 + |y|)^s |a(y) - b(y)|`; on a time step of
length `h` with `K h ≤ 1/2` the mean value inequality halves any weighted bound of the
difference, so the difference vanishes; finitely many steps cover `[0, τ★]`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace SchwartzMap

namespace WaveTurbulence.WKE

variable {d : ℕ}

/-! ### Uniform weighted bounds from continuity into `𝓢` -/

theorem one_add_pow_le_two_pow_mul (a : ℝ) (ha : 0 ≤ a) (N : ℕ) :
    (1 + a) ^ N ≤ 2 ^ N * (1 + a ^ N) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ N ≤ (1 + 1) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * 1 := by norm_num
      _ ≤ 2 ^ N * (1 + a ^ N) := by
          have := pow_nonneg ha N
          gcongr; linarith
  · calc (1 + a) ^ N ≤ (a + a) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * a ^ N := by rw [← two_mul, mul_pow]
      _ ≤ 2 ^ N * (1 + a ^ N) := by gcongr; linarith

theorem exists_uniform_decayBound {φ : ℝ → 𝓢(Mom d, ℝ)} {T : ℝ} (hφ : ContinuousOn φ (Icc 0 T))
    (N : ℕ) : ∃ R, 0 ≤ R ∧ ∀ τ ∈ Icc 0 T, DecayBound R (N : ℝ) (φ τ) := by
  have hc := fun k : ℕ => ((schwartz_withSeminorms ℝ (Mom d) ℝ).continuous_seminorm
    (k, 0)).comp_continuousOn hφ
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 0)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc N)
  refine ⟨2 ^ N * (max A 0 + max B 0), by positivity, fun τ hτ y => ?_⟩
  have hA' : SchwartzMap.seminorm ℝ 0 0 (φ τ) ≤ max A 0 := by
    have := hA τ hτ
    simp only [Function.comp_apply, SchwartzMap.schwartzSeminormFamily_apply, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hB' : SchwartzMap.seminorm ℝ N 0 (φ τ) ≤ max B 0 := by
    have := hB τ hτ
    simp only [Function.comp_apply, SchwartzMap.schwartzSeminormFamily_apply, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have s0 := SchwartzMap.le_seminorm ℝ 0 0 (φ τ) y
  have sN := SchwartzMap.le_seminorm ℝ N 0 (φ τ) y
  rw [norm_iteratedFDeriv_zero, pow_zero, one_mul] at s0
  rw [norm_iteratedFDeriv_zero] at sN
  have hp : 0 < 1 + ‖y‖ := by positivity
  rw [Real.rpow_neg hp.le, Real.rpow_natCast, ← Real.norm_eq_abs, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  calc ‖(φ τ) y‖ * (1 + ‖y‖) ^ N ≤ ‖(φ τ) y‖ * (2 ^ N * (1 + ‖y‖ ^ N)) :=
        mul_le_mul_of_nonneg_left (one_add_pow_le_two_pow_mul _ (norm_nonneg y) N)
          (norm_nonneg _)
    _ = 2 ^ N * (‖(φ τ) y‖ + ‖y‖ ^ N * ‖(φ τ) y‖) := by ring
    _ ≤ 2 ^ N * (max A 0 + max B 0) := by gcongr <;> linarith

/-! ### Lipschitz bound for `𝒦` in the weighted sup norm -/

/-- `(1 + |k|)^s |𝒦(a,a,a)(k) - 𝒦(b,b,b)(k)| ≤ 36 C(d) R² D`, `s = 2d + 1`. -/
theorem abs_collisionOp_sub_le (hd : 2 ≤ d) (a b : 𝓢(Mom d, ℝ)) {R D : ℝ}
    (ha : DecayBound R (2 * d + 1) a) (hb : DecayBound R (2 * d + 1) b)
    (hab : DecayBound D (2 * d + 1) (fun y => a y - b y)) (k : Mom d) :
    (1 + ‖k‖) ^ (2 * (d : ℝ) + 1) * |collisionOp a a a k - collisionOp b b b k| ≤
      36 * tameConst d (2 * d + 1) * 3 ^ (2 * (d : ℝ) + 1) * R ^ 2 * D := by
  set s : ℝ := 2 * d + 1
  have hs : 2 * (d : ℝ) < s := by simp only [s]; linarith
  obtain ⟨Ca, hCa⟩ := collisionInputs_of_schwartz a a a hs
  obtain ⟨Cb, hCb⟩ := collisionInputs_of_schwartz b b b hs
  rw [collisionOp_eq_sum hCa hd k, collisionOp_eq_sum hCb hd k]
  have Sa := admissible_schwartz a s
  have Sb := admissible_schwartz b s
  have T := fun j => collisionTerm_telescope hd hs Sa Sa Sa Sb Sb Sb j k
  have hR := ha.C_nonneg
  have hD := hab.C_nonneg
  have B := fun j => abs_collisionTerm_le hd hs hab ha ha j k
  have B' := fun j => abs_collisionTerm_le hd hs hb hab ha j k
  have B'' := fun j => abs_collisionTerm_le hd hs hb hb hab j k
  have hw : 0 ≤ (1 + ‖k‖) ^ s := by positivity
  have hj : ∀ j : Fin 4, (1 + ‖k‖) ^ s *
      |collisionTerm j a a a k - collisionTerm j b b b k| ≤
      9 * tameConst d s * 3 ^ s * R ^ 2 * D := by
    intro j
    rw [T j]
    have t := abs_add3_le (collisionTerm j (fun y => a y - b y) a a k)
      (collisionTerm j b (fun y => a y - b y) a k) (collisionTerm j b b (fun y => a y - b y) k)
    calc (1 + ‖k‖) ^ s * |_| ≤ (1 + ‖k‖) ^ s *
          (|collisionTerm j (fun y => a y - b y) a a k|
            + |collisionTerm j b (fun y => a y - b y) a k|
            + |collisionTerm j b b (fun y => a y - b y) k|) := mul_le_mul_of_nonneg_left t hw
      _ ≤ 3 * tameConst d s * 3 ^ s * (D * R * R) + 3 * tameConst d s * 3 ^ s * (R * D * R)
            + 3 * tameConst d s * 3 ^ s * (R * R * D) := by
          have := B j; have := B' j; have := B'' j
          nlinarith
      _ = 9 * tameConst d s * 3 ^ s * R ^ 2 * D := by ring
  have e : collisionTerm 0 a a a k - collisionTerm 1 a a a k + collisionTerm 2 a a a k
      - collisionTerm 3 a a a k - (collisionTerm 0 b b b k - collisionTerm 1 b b b k
        + collisionTerm 2 b b b k - collisionTerm 3 b b b k) =
      (collisionTerm 0 a a a k - collisionTerm 0 b b b k)
        - (collisionTerm 1 a a a k - collisionTerm 1 b b b k)
        + (collisionTerm 2 a a a k - collisionTerm 2 b b b k)
        - (collisionTerm 3 a a a k - collisionTerm 3 b b b k) := by ring
  rw [e]
  have t := abs_sub_add_sub_le (collisionTerm 0 a a a k - collisionTerm 0 b b b k)
    (collisionTerm 1 a a a k - collisionTerm 1 b b b k)
    (collisionTerm 2 a a a k - collisionTerm 2 b b b k)
    (collisionTerm 3 a a a k - collisionTerm 3 b b b k)
  have := hj 0; have := hj 1; have := hj 2; have := hj 3
  nlinarith

/-! ### The bootstrap -/

/-- **Uniqueness of Schwartz solutions of (WKE)** (TARGET Prop `wkelwp`, L598–L601, uniqueness;
Appendix C L2526), for `d ≥ 2`. -/
theorem isWKESolution_unique (hd : 2 ≤ d) {φin : 𝓢(Mom d, ℝ)} {T : ℝ}
    {φ ψ : ℝ → 𝓢(Mom d, ℝ)} (hφ : IsWKESolution φin T φ) (hψ : IsWKESolution φin T ψ) :
    ∀ τ ∈ Icc 0 T, φ τ = ψ τ := by
  set s : ℝ := 2 * d + 1
  set N : ℕ := 2 * d + 1
  have hNs : (N : ℝ) = s := by simp [N, s]
  obtain ⟨R₁, hR₁, b₁⟩ := exists_uniform_decayBound hφ.1 N
  obtain ⟨R₂, hR₂, b₂⟩ := exists_uniform_decayBound hψ.1 N
  rw [hNs] at b₁ b₂
  set R := R₁ + R₂
  have hR : 0 ≤ R := by positivity
  have bφ : ∀ τ ∈ Icc 0 T, DecayBound R s (φ τ) := fun τ hτ =>
    (b₁ τ hτ).mono_C (by simp only [R]; linarith)
  have bψ : ∀ τ ∈ Icc 0 T, DecayBound R s (ψ τ) := fun τ hτ =>
    (b₂ τ hτ).mono_C (by simp only [R]; linarith)
  set K := 36 * tameConst d s * 3 ^ s * R ^ 2
  have hK : 0 ≤ K := by have := tameConst_nonneg d s; positivity
  set h : ℝ := 1 / (2 * (K + 1))
  have hh : 0 < h := by positivity
  have hKh : K * h ≤ 1 / 2 := by
    simp only [h]
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  set u : ℝ → Mom d → ℝ := fun τ k => φ τ k - ψ τ k
  have hder : ∀ τ ∈ Icc 0 T, ∀ k, HasDerivWithinAt (fun σ => u σ k)
      (collisionOp (φ τ) (φ τ) (φ τ) k - collisionOp (ψ τ) (ψ τ) (ψ τ) k) (Icc 0 T) τ :=
    fun τ hτ k => (hφ.2.2 τ hτ k).sub (hψ.2.2 τ hτ k)
  have step : ∀ τ₀ ∈ Icc 0 T, (∀ k, u τ₀ k = 0) →
      ∀ σ ∈ Icc τ₀ (min (τ₀ + h) T), ∀ k, u σ k = 0 := by
    intro τ₀ hτ₀ h0
    set τ₁ := min (τ₀ + h) T
    have hsub : Icc τ₀ τ₁ ⊆ Icc 0 T := Icc_subset_Icc hτ₀.1 (min_le_right _ _)
    have halve : ∀ n : ℕ, ∀ σ ∈ Icc τ₀ τ₁, DecayBound (2 * R / 2 ^ n) s (u σ) := by
      intro n
      induction n with
      | zero =>
        intro σ hσ y
        have e1 := bφ σ (hsub hσ) y; have e2 := bψ σ (hsub hσ) y
        calc |u σ y| = |φ σ y - ψ σ y| := rfl
          _ ≤ |φ σ y| + |ψ σ y| := abs_sub _ _
          _ ≤ 2 * R / 2 ^ 0 * (1 + ‖y‖) ^ (-s) := by linarith
      | succ n ih =>
        intro σ hσ k
        set c := 2 * R / 2 ^ n
        have hc : 0 ≤ c := by positivity
        have hw := wt_nonneg s k
        have hbound : ∀ x ∈ Ico τ₀ τ₁, ‖collisionOp (φ x) (φ x) (φ x) k
            - collisionOp (ψ x) (ψ x) (ψ x) k‖ ≤ K * c * wt s k := by
          intro x hx
          have hx' := Ico_subset_Icc_self hx
          have L := abs_collisionOp_sub_le hd (φ x) (ψ x) (bφ x (hsub hx')) (bψ x (hsub hx'))
            (ih x hx') k
          rw [Real.norm_eq_abs]
          have e : |collisionOp (φ x) (φ x) (φ x) k - collisionOp (ψ x) (ψ x) (ψ x) k| =
              wt s k * ((1 + ‖k‖) ^ s * |collisionOp (φ x) (φ x) (φ x) k
                - collisionOp (ψ x) (ψ x) (ψ x) k|) := by
            rw [← mul_assoc, wt_mul_rpow, one_mul]
          rw [e]
          calc wt s k * ((1 + ‖k‖) ^ s * _) ≤ wt s k * (K * c) :=
                mul_le_mul_of_nonneg_left (by simpa only [K, mul_assoc] using L) hw
            _ = K * c * wt s k := by ring
        have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun σ => u σ k)
          (fun x hx => (hder x (hsub hx) k).mono hsub) hbound σ hσ
        rw [h0 k, sub_zero, Real.norm_eq_abs] at hmv
        have hlen : σ - τ₀ ≤ h := by linarith [hσ.2, min_le_left (τ₀ + h) T]
        have hσ0 : 0 ≤ σ - τ₀ := by linarith [hσ.1]
        calc |u σ k| ≤ K * c * wt s k * (σ - τ₀) := hmv
          _ ≤ K * c * wt s k * h := by gcongr
          _ = (K * h) * c * wt s k := by ring
          _ ≤ (1 / 2) * c * wt s k := by gcongr
          _ = 2 * R / 2 ^ (n + 1) * (1 + ‖k‖) ^ (-s) := by
              simp only [c, wt, pow_succ]; ring
    intro σ hσ k
    by_contra hne
    have hpos : 0 < |u σ k| := abs_pos.mpr hne
    set W := 2 * R * wt s k + 1
    have hW : 0 < W := by have := wt_nonneg s k; positivity
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hpos hW) (by norm_num : (1 / 2 : ℝ) < 1)
    have hb := halve n σ hσ k
    have : |u σ k| ≤ W * (1 / 2) ^ n := by
      calc |u σ k| ≤ 2 * R / 2 ^ n * (1 + ‖k‖) ^ (-s) := hb
        _ = 2 * R * wt s k * (1 / 2) ^ n := by simp only [wt, div_eq_mul_inv, one_mul, inv_pow]; ring
        _ ≤ W * (1 / 2) ^ n := by gcongr; simp only [W]; linarith
    rw [lt_div_iff₀ hW] at hn
    linarith
  have glob : ∀ n : ℕ, ∀ σ ∈ Icc 0 (min (n * h) T), ∀ k, u σ k = 0 := by
    intro n
    induction n with
    | zero =>
      intro σ hσ k
      have hσ0 : σ = 0 := le_antisymm (by simpa using hσ.2.trans (min_le_left _ _)) hσ.1
      simp [u, hσ0, hφ.2.1, hψ.2.1]
    | succ n ih =>
      intro σ hσ k
      by_cases hle : σ ≤ min (n * h) T
      · exact ih σ ⟨hσ.1, hle⟩ k
      · replace hle := not_le.mp hle
        set τ₀ := min (n * h) T
        have hσT : σ ≤ T := hσ.2.trans (min_le_right _ _)
        have hτ₀0 : 0 ≤ τ₀ := le_min (by positivity) (hσ.1.trans hσT)
        have hτ₀ : τ₀ ∈ Icc 0 T := ⟨hτ₀0, min_le_right _ _⟩
        have hτ₀eq : τ₀ = n * h := by
          rcases min_choice (n * h) T with e | e
          · exact e
          · exfalso; rw [show τ₀ = T from e] at hle; linarith
        refine step τ₀ hτ₀ (fun k => ih τ₀ ⟨hτ₀0, le_rfl⟩ k) σ ⟨hle.le, ?_⟩ k
        rw [hτ₀eq]
        refine le_min ?_ hσT
        have := hσ.2.trans (min_le_left _ _)
        push_cast at this
        linarith
  intro τ hτ
  obtain ⟨n, hn⟩ := exists_nat_ge (T / h)
  have hTn : T ≤ n * h := by rwa [div_le_iff₀ hh] at hn
  have hmin : min (n * h) T = T := min_eq_right hTn
  ext k
  have := glob n τ ⟨hτ.1, by rw [hmin]; exact hτ.2⟩ k
  exact sub_eq_zero.mp this

end WaveTurbulence.WKE
