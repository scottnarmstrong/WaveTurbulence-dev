/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.TaylorCoeff
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Series tools for the power-series solution of (WKE)

* `tsum_tsum_eq_tsum_sum_antidiagonal`: `Σ'ₐ Σ'_b G(a, b) = Σ'ₘ Σ_{a+b=m} G(a, b)` for summable
  `G : ℕ × ℕ → ℝ` (regrouping by total degree);
* `summable_two_mul_add_one_pow_mul_geometric`: `Σ (2n+1)^p qⁿ < ∞` for `0 ≤ q < 1`;
* `collisionOp_add_left` etc.: additivity of `collisionOp` in each slot on Schwartz inputs, and
  `abs_collisionOp_le_sup`: `|𝒦(f,g,h)(k)| ≤ opConst d · C_f C_g C_h` in the weight `s₀ = 2d+1`;
* `tsum_of_bounded_additive`: a bounded additive functional commutes with a series converging in
  the weighted sup norm.
-/

public section

open MeasureTheory Set Filter Topology Finset
open scoped InnerProductSpace SchwartzMap

namespace WaveTurbulence.WKE

variable {d : ℕ}

/-! ### Regrouping double series by total degree -/

theorem tsum_tsum_eq_tsum_sum_antidiagonal {G : ℕ × ℕ → ℝ} (hG : Summable G) :
    ∑' a, ∑' b, G (a, b) = ∑' m, ∑ p ∈ antidiagonal m, G p := by
  conv_rhs => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  rw [← hG.tsum_prod' (fun a => hG.prod_factor a),
    ← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq]
  have hs : Summable (fun c => G (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd c)) :=
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff).mpr hG
  exact hs.tsum_sigma' (fun m => (hasSum_fintype _).summable)

/-! ### Polynomial times geometric -/

theorem two_mul_add_one_pow_le (n p : ℕ) : ((2 * n + 1 : ℕ) : ℝ) ^ p ≤ 3 ^ p * (n : ℝ) ^ p + 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have h1 : ((2 * n + 1 : ℕ) : ℝ) ≤ 3 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast h
      push_cast; linarith
    calc ((2 * n + 1 : ℕ) : ℝ) ^ p ≤ (3 * (n : ℝ)) ^ p := pow_le_pow_left₀ (by positivity) h1 p
      _ = 3 ^ p * (n : ℝ) ^ p := mul_pow _ _ _
      _ ≤ _ := le_add_of_nonneg_right zero_le_one

theorem summable_two_mul_add_one_pow_mul_geometric (p : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) :
    Summable (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ) ^ p * q ^ n) := by
  have h1 : Summable (fun n : ℕ => (n : ℝ) ^ p * q ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one p (by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])
  have h2 : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((h1.mul_left (3 ^ p)).add h2)
  calc ((2 * n + 1 : ℕ) : ℝ) ^ p * q ^ n ≤ (3 ^ p * (n : ℝ) ^ p + 1) * q ^ n :=
        mul_le_mul_of_nonneg_right (two_mul_add_one_pow_le n p) (by positivity)
    _ = 3 ^ p * ((n : ℝ) ^ p * q ^ n) + q ^ n := by ring

/-! ### `collisionOp` on Schwartz inputs: slot additivity and a crude bound -/

theorem deltaIntegrable_collisionIntegrand_schwartz (hd : 2 ≤ d) (f g h : 𝓢(Mom d, ℝ))
    (k : Mom d) : DeltaIntegrable (collisionIntegrand f g h k) := by
  obtain ⟨C, hC⟩ := collisionInputs_of_schwartz f g h (by linarith : 2 * (d : ℝ) < 2 * d + 1)
  exact ⟨fun ℓ hℓ => integrable_collisionIntegrand_perp hC hd k hℓ,
    integrable_collisionOp_outer hC hd k⟩

theorem collisionOp_add_left (hd : 2 ≤ d) (f f' g h : 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionOp ⇑(f + f') g h k = collisionOp f g h k + collisionOp f' g h k := by
  simp only [collisionOp_eq_deltaInt]
  rw [← (deltaIntegrable_collisionIntegrand_schwartz hd f g h k).deltaInt_add
    (deltaIntegrable_collisionIntegrand_schwartz hd f' g h k) (by omega)]
  exact deltaInt_congr fun ℓ x => by simp only [collisionIntegrand, add_apply]; ring

theorem collisionOp_add_mid (hd : 2 ≤ d) (f g g' h : 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionOp f ⇑(g + g') h k = collisionOp f g h k + collisionOp f g' h k := by
  simp only [collisionOp_eq_deltaInt]
  rw [← (deltaIntegrable_collisionIntegrand_schwartz hd f g h k).deltaInt_add
    (deltaIntegrable_collisionIntegrand_schwartz hd f g' h k) (by omega)]
  exact deltaInt_congr fun ℓ x => by simp only [collisionIntegrand, add_apply]; ring

theorem collisionOp_add_right (hd : 2 ≤ d) (f g h h' : 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionOp f g ⇑(h + h') k = collisionOp f g h k + collisionOp f g h' k := by
  simp only [collisionOp_eq_deltaInt]
  rw [← (deltaIntegrable_collisionIntegrand_schwartz hd f g h k).deltaInt_add
    (deltaIntegrable_collisionIntegrand_schwartz hd f g h' k) (by omega)]
  exact deltaInt_congr fun ℓ x => by simp only [collisionIntegrand, add_apply]; ring

theorem collisionOp_smul_left (c : ℝ) (f : 𝓢(Mom d, ℝ)) (g h : Mom d → ℝ) (k : Mom d) :
    collisionOp ⇑(c • f) g h k = c * collisionOp f g h k := by
  simp only [collisionOp_eq_deltaInt]
  rw [← deltaInt_smul]
  exact deltaInt_congr fun ℓ x => by simp only [collisionIntegrand, smul_apply, smul_eq_mul]; ring

theorem collisionOp_smul_mid (c : ℝ) (g : 𝓢(Mom d, ℝ)) (f h : Mom d → ℝ) (k : Mom d) :
    collisionOp f ⇑(c • g) h k = c * collisionOp f g h k := by
  simp only [collisionOp_eq_deltaInt]
  rw [← deltaInt_smul]
  exact deltaInt_congr fun ℓ x => by simp only [collisionIntegrand, smul_apply, smul_eq_mul]; ring

theorem collisionOp_smul_right (c : ℝ) (h : 𝓢(Mom d, ℝ)) (f g : Mom d → ℝ) (k : Mom d) :
    collisionOp f g ⇑(c • h) k = c * collisionOp f g h k := by
  simp only [collisionOp_eq_deltaInt]
  rw [← deltaInt_smul]
  exact deltaInt_congr fun ℓ x => by simp only [collisionIntegrand, smul_apply, smul_eq_mul]; ring

/-- The crude sup bound constant. -/
@[expose] noncomputable def opConst (d : ℕ) : ℝ :=
  12 * tameConst d (2 * d + 1) * 3 ^ (2 * (d : ℝ) + 1)

theorem opConst_nonneg (d : ℕ) : 0 ≤ opConst d := by
  unfold opConst; have := tameConst_nonneg d (2 * d + 1); positivity

theorem abs_collisionOp_le_sup (hd : 2 ≤ d) {f g h : Mom d → ℝ} {C₁ C₂ C₃ : ℝ}
    (h₁ : DecayBound C₁ (2 * d + 1) f) (h₂ : DecayBound C₂ (2 * d + 1) g)
    (h₃ : DecayBound C₃ (2 * d + 1) h) (k : Mom d) :
    |collisionOp f g h k| ≤ opConst d * (C₁ * C₂ * C₃) := by
  have hs : 2 * (d : ℝ) < 2 * d + 1 := by linarith
  have h0 : 0 ≤ 2 * (d : ℝ) + 1 := by positivity
  have key := abs_collisionOp_le_tame hd hs h0 h₁ h₂ h₃ h₁ h₂ h₃ k
  have h1 : 1 ≤ (1 + ‖k‖) ^ (2 * (d : ℝ) + 1) :=
    Real.one_le_rpow (by linarith [norm_nonneg k]) h0
  have : |collisionOp f g h k| ≤ (1 + ‖k‖) ^ (2 * (d : ℝ) + 1) * |collisionOp f g h k| :=
    le_mul_of_one_le_left (abs_nonneg _) h1
  have e : 4 * (tameConst d (2 * d + 1) * 3 ^ (2 * (d : ℝ) + 1) * (C₁ * C₂ * C₃ + C₁ * C₂ * C₃
      + C₁ * C₂ * C₃)) = opConst d * (C₁ * C₂ * C₃) := by unfold opConst; ring
  linarith

/-! ### A bounded additive functional commutes with weighted-sup series -/

theorem _root_.WaveTurbulence.DecayBound.of_tsum {f : ℕ → 𝓢(Mom d, ℝ)} {C : ℕ → ℝ} {N : ℝ}
    (hf : ∀ n, DecayBound (C n) N (f n)) (hC : Summable C) {F : 𝓢(Mom d, ℝ)}
    (hF : ∀ y, F y = ∑' n, f n y) (M : ℕ) :
    DecayBound (∑' n, C (n + M)) N (F - ∑ n ∈ range M, f n) := by
  intro y
  have hsy : Summable (fun n => f n y) :=
    Summable.of_norm_bounded (hC.mul_right ((1 + ‖y‖) ^ (-N)))
      (fun n => by rw [Real.norm_eq_abs]; exact hf n y)
  have e : (F - ∑ n ∈ range M, f n) y = ∑' n, f (n + M) y := by
    rw [sub_apply, hF y, _root_.sum_apply, ← hsy.sum_add_tsum_nat_add M]; ring
  rw [e]
  have hsy' : Summable (fun n => |f (n + M) y|) :=
    (summable_nat_add_iff M).mpr hsy.abs
  calc |∑' n, f (n + M) y| ≤ ∑' n, |f (n + M) y| := by
        rw [← Real.norm_eq_abs]
        refine (norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hsy')).trans ?_
        simp [Real.norm_eq_abs]
    _ ≤ ∑' n, C (n + M) * (1 + ‖y‖) ^ (-N) :=
        hsy'.tsum_le_tsum (fun n => hf (n + M) y)
          (((summable_nat_add_iff M).mpr hC).mul_right _)
    _ = (∑' n, C (n + M)) * (1 + ‖y‖) ^ (-N) := tsum_mul_right

/-- If `L` is additive on `𝓢` with `|L f| ≤ K · C` whenever `DecayBound C N f`, then `L` commutes
with series converging in the weighted sup norm. -/
theorem tsum_of_bounded_additive (L : 𝓢(Mom d, ℝ) →+ ℝ) {K N : ℝ} (hK : 0 ≤ K)
    (hL : ∀ (f : 𝓢(Mom d, ℝ)) (C : ℝ), DecayBound C N f → |L f| ≤ K * C)
    {f : ℕ → 𝓢(Mom d, ℝ)} {C : ℕ → ℝ} (hf : ∀ n, DecayBound (C n) N (f n)) (hC : Summable C)
    {F : 𝓢(Mom d, ℝ)} (hF : ∀ y, F y = ∑' n, f n y) :
    L F = ∑' n, L (f n) ∧ Summable (fun n => L (f n)) := by
  have hsum : Summable (fun n => L (f n)) :=
    Summable.of_norm_bounded (hC.mul_left K) (fun n => by rw [Real.norm_eq_abs]; exact hL _ _ (hf n))
  refine ⟨?_, hsum⟩
  have h1 : Tendsto (fun M => ∑ n ∈ range M, L (f n)) atTop (𝓝 (∑' n, L (f n))) :=
    hsum.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun M => ∑ n ∈ range M, L (f n)) atTop (𝓝 (L F)) := by
    have htail : Tendsto (fun M => ∑' n, C (n + M)) atTop (𝓝 0) := tendsto_sum_nat_add C
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M₀, hM₀⟩ := Metric.tendsto_atTop.mp htail (ε / (K + 1)) (by positivity)
    refine ⟨M₀, fun M hM => ?_⟩
    rw [Real.dist_eq]
    have hdiff := hL _ _ (DecayBound.of_tsum hf hC hF M)
    have e : L (F - ∑ n ∈ range M, f n) = L F - ∑ n ∈ range M, L (f n) := by
      rw [map_sub, map_sum]
    rw [e] at hdiff
    have ht := hM₀ M hM
    rw [Real.dist_eq, sub_zero] at ht
    have htn : 0 ≤ ∑' n, C (n + M) :=
      tsum_nonneg fun n => (hf (n + M)).C_nonneg
    rw [abs_of_nonneg htn] at ht
    rw [abs_sub_comm]
    calc |L F - ∑ n ∈ range M, L (f n)| ≤ K * ∑' n, C (n + M) := hdiff
      _ ≤ (K + 1) * ∑' n, C (n + M) := by nlinarith
      _ < (K + 1) * (ε / (K + 1)) := by
          exact mul_lt_mul_of_pos_left ht (by positivity)
      _ = ε := by field_simp
  exact tendsto_nhds_unique h2 h1

end WaveTurbulence.WKE
