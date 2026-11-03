/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.AkUnique

/-!
# Persistence of regularity for the `a`-system

For a solution `a` of (akeqn)–(akeqn2) on `[0, 𝔇]` in the class `Z^{d+1}` and any `s : ℕ`:

* `IsAkSolution.tsum_weight_le`: if `∑ (1 + ‖n‖)^s |cₙ| < ∞` then
  `∑ (1 + ‖n‖)^s |aₙ(t)| ≤ (∑ (1 + ‖n‖)^s |cₙ|) e^{Kt}` on `[0, 𝔇]`, with `K` depending only on `s`
  and the `ℓ¹` size of `a`;
* `IsAkSolution.exists_uniform_decay`: rapidly decreasing data give coefficients decaying faster
  than any power of `1 + ‖n‖`, uniformly in `t ∈ [0, 𝔇]`.

The proof runs the weighted Gronwall estimate `tsum_weighted_le_exp` with the truncated weights
`min((1 + ‖n‖)^s, M)` (which satisfy the tame inequality with a constant independent of `M`) and
lets `M → ∞`. This is the persistence statement of packet NLS goal 5 in the weighted `ℓ¹` scale;
it turns the paper's solution with polynomial decay into one with rapid decay (FINDINGS F8).
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped ENNReal

namespace WaveTurbulence

variable {d : ℕ}

/-! ### General weights -/

theorem tsum_weight_mul_tripleAbs (w : (Fin d → ℤ) → ℝ≥0∞) (f g h : (Fin d → ℤ) → ℂ) :
    ∑' n, w n * tripleAbs f g h n =
      ∑' n₁, ∑' n₂, ∑' n₃, w (n₁ - n₂ + n₃) * (‖f n₁‖ₑ * ‖g n₂‖ₑ * ‖h n₃‖ₑ) := by
  simp only [tripleAbs, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm, ENNReal.tsum_prod']
  refine tsum_congr fun n₁ => tsum_congr fun n₂ => ?_
  rw [← (Equiv.addRight (n₁ - n₂)).tsum_eq]
  refine tsum_congr fun n₃ => ?_
  simp only [Equiv.coe_addRight]
  have h1 : n₃ + (n₁ - n₂) - n₁ + n₂ = n₃ := by abel
  have h2 : n₃ + (n₁ - n₂) = n₁ - n₂ + n₃ := by abel
  rw [h1, h2]

/-- The tame bound for any weight with the tame property. -/
theorem tsum_weight_mul_tripleAbs_le_tame (w : (Fin d → ℤ) → ℝ≥0∞) {A : ℝ≥0∞}
    (hw : ∀ n₁ n₂ n₃, w (n₁ - n₂ + n₃) ≤ A * (w n₁ + w n₂ + w n₃)) (f g h : (Fin d → ℤ) → ℂ) :
    ∑' n, w n * tripleAbs f g h n ≤
      A * ((∑' n, w n * ‖f n‖ₑ) * wnorm 0 g * wnorm 0 h +
        wnorm 0 f * (∑' n, w n * ‖g n‖ₑ) * wnorm 0 h +
        wnorm 0 f * wnorm 0 g * (∑' n, w n * ‖h n‖ₑ)) := by
  rw [tsum_weight_mul_tripleAbs]
  calc ∑' n₁, ∑' n₂, ∑' n₃, w (n₁ - n₂ + n₃) * (‖f n₁‖ₑ * ‖g n₂‖ₑ * ‖h n₃‖ₑ)
      ≤ ∑' n₁, ∑' n₂, ∑' n₃, A *
          ((w n₁ * ‖f n₁‖ₑ) * ‖g n₂‖ₑ * ‖h n₃‖ₑ + ‖f n₁‖ₑ * (w n₂ * ‖g n₂‖ₑ) * ‖h n₃‖ₑ +
            ‖f n₁‖ₑ * ‖g n₂‖ₑ * (w n₃ * ‖h n₃‖ₑ)) := by
        refine ENNReal.tsum_le_tsum fun n₁ => ENNReal.tsum_le_tsum fun n₂ =>
          ENNReal.tsum_le_tsum fun n₃ => ?_
        calc w (n₁ - n₂ + n₃) * (‖f n₁‖ₑ * ‖g n₂‖ₑ * ‖h n₃‖ₑ)
            ≤ (A * (w n₁ + w n₂ + w n₃)) * (‖f n₁‖ₑ * ‖g n₂‖ₑ * ‖h n₃‖ₑ) := by
              gcongr
              exact hw n₁ n₂ n₃
          _ = _ := by ring
    _ = _ := by
        simp only [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_right,
          wnorm_zero_eq]

/-! ### Truncated polynomial weights -/

theorem one_add_norm_sub_add_pow_le (s : ℕ) (n₁ n₂ n₃ : Fin d → ℤ) :
    (1 + ‖n₁ - n₂ + n₃‖) ^ s ≤ 3 ^ s * ((1 + ‖n₁‖) ^ s + (1 + ‖n₂‖) ^ s + (1 + ‖n₃‖) ^ s) := by
  set M := max (max (1 + ‖n₁‖) (1 + ‖n₂‖)) (1 + ‖n₃‖)
  have hM : 1 + ‖n₁ - n₂ + n₃‖ ≤ 3 * M := by
    have h := one_add_norm_sub_add_le n₁ n₂ n₃
    have h1 : 1 + ‖n₁‖ ≤ M := le_max_of_le_left (le_max_left _ _)
    have h2 : 1 + ‖n₂‖ ≤ M := le_max_of_le_left (le_max_right _ _)
    have h3 : 1 + ‖n₃‖ ≤ M := le_max_right _ _
    linarith [norm_nonneg n₁, norm_nonneg n₂, norm_nonneg n₃]
  have hMs : M ^ s ≤ (1 + ‖n₁‖) ^ s + (1 + ‖n₂‖) ^ s + (1 + ‖n₃‖) ^ s := by
    have p1 : 0 ≤ (1 + ‖n₁‖) ^ s := by positivity
    have p2 : 0 ≤ (1 + ‖n₂‖) ^ s := by positivity
    have p3 : 0 ≤ (1 + ‖n₃‖) ^ s := by positivity
    rcases max_cases (max (1 + ‖n₁‖) (1 + ‖n₂‖)) (1 + ‖n₃‖) with ⟨h, -⟩ | ⟨h, -⟩ <;>
      simp only [M, h]
    · rcases max_cases (1 + ‖n₁‖) (1 + ‖n₂‖) with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h'] <;> linarith
    · linarith
  calc (1 + ‖n₁ - n₂ + n₃‖) ^ s ≤ (3 * M) ^ s := pow_le_pow_left₀ (by positivity) hM s
    _ = 3 ^ s * M ^ s := mul_pow _ _ _
    _ ≤ _ := by gcongr

/-- The truncated weight `min((1 + ‖n‖)^s, M)`. -/
def truncWeight (s : ℕ) (M : ℝ) (n : Fin d → ℤ) : ℝ := min ((1 + ‖n‖) ^ s) M

theorem truncWeight_nonneg (s : ℕ) {M : ℝ} (hM : 0 ≤ M) (n : Fin d → ℤ) :
    0 ≤ truncWeight s M n :=
  le_min (by positivity) hM

theorem truncWeight_le (s : ℕ) (M : ℝ) (n : Fin d → ℤ) : truncWeight s M n ≤ M :=
  min_le_right _ _

theorem truncWeight_tame (s : ℕ) {M : ℝ} (hM : 0 ≤ M) (n₁ n₂ n₃ : Fin d → ℤ) :
    truncWeight s M (n₁ - n₂ + n₃) ≤
      3 ^ s * (truncWeight s M n₁ + truncWeight s M n₂ + truncWeight s M n₃) := by
  have h3 : (1 : ℝ) ≤ 3 ^ s := one_le_pow₀ (by norm_num)
  have w1 := truncWeight_nonneg s hM n₁
  have w2 := truncWeight_nonneg s hM n₂
  have w3 := truncWeight_nonneg s hM n₃
  by_cases hbig : M ≤ (1 + ‖n₁‖) ^ s ∨ M ≤ (1 + ‖n₂‖) ^ s ∨ M ≤ (1 + ‖n₃‖) ^ s
  · have hsum : M ≤ truncWeight s M n₁ + truncWeight s M n₂ + truncWeight s M n₃ := by
      rcases hbig with h | h | h
      · have : truncWeight s M n₁ = M := min_eq_right h
        linarith
      · have : truncWeight s M n₂ = M := min_eq_right h
        linarith
      · have : truncWeight s M n₃ = M := min_eq_right h
        linarith
    calc truncWeight s M (n₁ - n₂ + n₃) ≤ M := truncWeight_le s M _
      _ ≤ 1 * (truncWeight s M n₁ + truncWeight s M n₂ + truncWeight s M n₃) := by linarith
      _ ≤ _ := by gcongr
  · simp only [not_or, not_le] at hbig
    obtain ⟨h1, h2, h3'⟩ := hbig
    have e1 : truncWeight s M n₁ = (1 + ‖n₁‖) ^ s := min_eq_left h1.le
    have e2 : truncWeight s M n₂ = (1 + ‖n₂‖) ^ s := min_eq_left h2.le
    have e3 : truncWeight s M n₃ = (1 + ‖n₃‖) ^ s := min_eq_left h3'.le
    rw [e1, e2, e3]
    exact (min_le_left _ _).trans (one_add_norm_sub_add_pow_le s n₁ n₂ n₃)

/-! ### Persistence -/

section Solutions

variable {L γ δ 𝔇 : ℝ} {c : (Fin d → ℤ) → ℂ} {a : ℝ → (Fin d → ℤ) → ℂ}

theorem IsAkSolution.exists_wnorm_bound (hL : 0 < L) (ha : IsAkSolution L γ δ 𝔇 c a) :
    ∃ R, 0 ≤ R ∧ ∀ t ∈ Icc 0 𝔇, ∑' m, ‖a t m‖ ≤ R := by
  obtain ⟨C, hC0, hC⟩ := ha.2.1.exists_norm_le hL
  refine ⟨C * ∑' m : Fin d → ℤ, ((1 + ‖m‖) ^ (d + 1))⁻¹,
    mul_nonneg hC0 (tsum_nonneg fun m => by positivity), fun t ht => ?_⟩
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun m => hC t ht m) (ha.summable_norm hL ht)
    (summable_inv_one_add_norm_pow.mul_left C)

/-- The truncated-weight estimate with a constant independent of the truncation. -/
theorem IsAkSolution.tsum_truncWeight_le (hL : 0 < L) (ha : IsAkSolution L γ δ 𝔇 c a)
    (s : ℕ) : ∃ K, 0 ≤ K ∧ ∀ M : ℝ, 0 ≤ M → ∀ t ∈ Icc 0 𝔇,
      ∑' n, truncWeight s M n * ‖a t n‖ ≤
        (∑' n, truncWeight s M n * ‖c n‖) * Real.exp (K * t) := by
  obtain ⟨C, hC0, hC⟩ := ha.2.1.exists_norm_le hL
  obtain ⟨Q, hQ, hQ'⟩ := ha.exists_aNonlin_majorant hL
  obtain ⟨R, hR0, hR⟩ := ha.exists_wnorm_bound hL
  set κ := |δ / (2 * L ^ ((d : ℝ) - γ))|
  have hκ0 : 0 ≤ κ := abs_nonneg _
  refine ⟨κ * 3 ^ s * (3 * R ^ 2), by positivity, fun M hM t₀ ht₀ => ?_⟩
  have key := tsum_weighted_le_exp (ψ := fun n t => a t n)
    (G := fun n s' => aNonlin L γ δ 1 s' (a s') (fun m => (starRingEnd ℂ) (a s' m)) (a s') n)
    (w := truncWeight s M) (T := 𝔇) (K := κ * 3 ^ s * (3 * R ^ 2)) (by positivity)
    (truncWeight_nonneg s hM) (fun n => ha.continuousOn n)
    (fun n => ha.continuousOn_aNonlin hL n)
    (fun n t ht => by rw [ha.eq_add_integral hL ht n, congrFun ha.1 n])
    (P := fun n => M * (C * ((1 + ‖n‖) ^ (d + 1))⁻¹)) (Q := fun n => M * Q n)
    ((summable_inv_one_add_norm_pow.mul_left C).mul_left M) (hQ.mul_left M)
    (fun n t ht => mul_le_mul (truncWeight_le s M n) (hC t ht n) (norm_nonneg _) hM)
    (fun n t ht => mul_le_mul (truncWeight_le s M n) (hQ' n t ht) (norm_nonneg _) hM)
    (fun t ht => ?_) t₀ ht₀
  · simpa [congrFun ha.1] using key
  -- the tame bound at time `t`
  have hsa := ha.summable_norm hL ht
  set we : (Fin d → ℤ) → ℝ≥0∞ := fun n => ENNReal.ofReal (truncWeight s M n)
  have hwe : ∀ n₁ n₂ n₃, we (n₁ - n₂ + n₃) ≤ 3 ^ s * (we n₁ + we n₂ + we n₃) := by
    intro n₁ n₂ n₃
    simp only [we]
    rw [← ENNReal.ofReal_add (truncWeight_nonneg s hM _) (truncWeight_nonneg s hM _),
      ← ENNReal.ofReal_add (by linarith [truncWeight_nonneg s hM n₁, truncWeight_nonneg s hM n₂])
        (truncWeight_nonneg s hM _),
      show (3 : ℝ≥0∞) ^ s = ENNReal.ofReal (3 ^ s) by rw [ENNReal.ofReal_pow (by norm_num)]; simp,
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (truncWeight_tame s hM n₁ n₂ n₃)
  have hsw : Summable fun n => truncWeight s M n * ‖a t n‖ :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (truncWeight_nonneg s hM n) (norm_nonneg _))
      (fun n => mul_le_mul_of_nonneg_right (truncWeight_le s M n) (norm_nonneg _))
      (hsa.mul_left M)
  have hWe : ∑' n, we n * ‖a t n‖ₑ = ENNReal.ofReal (∑' n, truncWeight s M n * ‖a t n‖) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (truncWeight_nonneg s hM n)
      (norm_nonneg _)) hsw]
    refine tsum_congr fun n => ?_
    rw [ENNReal.ofReal_mul (truncWeight_nonneg s hM n), ofReal_norm]
  have hconj : ∀ n, ‖(starRingEnd ℂ) (a t n)‖ = ‖a t n‖ := fun n => Complex.norm_conj _
  have hW0 : wnorm 0 (a t) = ENNReal.ofReal (∑' m, ‖a t m‖) := wnorm_zero_eq_ofReal hsa
  have hW0c : wnorm 0 (fun m => (starRingEnd ℂ) (a t m)) = ENNReal.ofReal (∑' m, ‖a t m‖) := by
    rw [wnorm_zero_eq_ofReal (by simpa [hconj] using hsa)]
    simp
  have hWec : ∑' n, we n * ‖(starRingEnd ℂ) (a t n)‖ₑ = ∑' n, we n * ‖a t n‖ₑ := by
    refine tsum_congr fun n => ?_
    rw [← ofReal_norm, ← ofReal_norm, hconj]
  have hE : ∑' n, ENNReal.ofReal (truncWeight s M n) *
      ‖aNonlin L γ δ 1 t (a t) (fun m => (starRingEnd ℂ) (a t m)) (a t) n‖ₑ ≤
      ENNReal.ofReal κ * (3 ^ s * (3 * (ENNReal.ofReal (∑' n, truncWeight s M n * ‖a t n‖) *
        ENNReal.ofReal (∑' m, ‖a t m‖) ^ 2))) := by
    calc _ ≤ ∑' n, we n * (ENNReal.ofReal κ *
          tripleAbs (a t) (fun m => (starRingEnd ℂ) (a t m)) (a t) n) :=
          ENNReal.tsum_le_tsum fun n => by gcongr; exact enorm_aNonlin_le L γ δ t _ _ _ n
      _ = ENNReal.ofReal κ * ∑' n, we n *
          tripleAbs (a t) (fun m => (starRingEnd ℂ) (a t m)) (a t) n := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun n => by ring
      _ ≤ ENNReal.ofReal κ * (3 ^ s * ((∑' n, we n * ‖a t n‖ₑ) *
          wnorm 0 (fun m => (starRingEnd ℂ) (a t m)) * wnorm 0 (a t) +
          wnorm 0 (a t) * (∑' n, we n * ‖(starRingEnd ℂ) (a t n)‖ₑ) * wnorm 0 (a t) +
          wnorm 0 (a t) * wnorm 0 (fun m => (starRingEnd ℂ) (a t m)) *
            (∑' n, we n * ‖a t n‖ₑ))) := by
          gcongr
          exact tsum_weight_mul_tripleAbs_le_tame we hwe _ _ _
      _ = _ := by
          rw [hWec, hWe, hW0, hW0c]
          ring
  have hfin : ENNReal.ofReal κ * (3 ^ s * (3 * (ENNReal.ofReal (∑' n, truncWeight s M n *
      ‖a t n‖) * ENNReal.ofReal (∑' m, ‖a t m‖) ^ 2))) ≠ ∞ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top
      (by norm_num)) (ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))))
  have h1 := ENNReal.toReal_mono hfin hE
  rw [ENNReal.tsum_toReal_eq (fun n => ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top)]
    at h1
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (truncWeight_nonneg s hM _), toReal_enorm,
    ENNReal.toReal_ofReal hκ0, ENNReal.toReal_pow, ENNReal.toReal_ofReal (tsum_nonneg fun n =>
      mul_nonneg (truncWeight_nonneg s hM n) (norm_nonneg (a t n))),
    ENNReal.toReal_ofReal (tsum_nonneg fun m => norm_nonneg (a t m))] at h1
  have hA := hR t ht
  have hA0 : 0 ≤ ∑' m, ‖a t m‖ := tsum_nonneg fun _ => norm_nonneg _
  have hT0 : 0 ≤ ∑' n, truncWeight s M n * ‖a t n‖ :=
    tsum_nonneg fun n => mul_nonneg (truncWeight_nonneg s hM n) (norm_nonneg _)
  refine h1.trans ?_
  norm_num
  have : (∑' m, ‖a t m‖) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hA0 hA 2
  nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg (mul_nonneg hκ0 (pow_nonneg
    (by norm_num : (0 : ℝ) ≤ 3) s)) hT0)]

/-- **Persistence of regularity** (packet NLS goal 5, weighted `ℓ¹` scale): the weighted norm
`∑ (1 + ‖n‖)^s |aₙ(t)|` stays finite and grows at most exponentially on `[0, 𝔇]`. -/
theorem IsAkSolution.tsum_weight_le (hL : 0 < L) (ha : IsAkSolution L γ δ 𝔇 c a) (s : ℕ)
    (hc : Summable fun n => (1 + ‖n‖) ^ s * ‖c n‖) :
    ∃ K, 0 ≤ K ∧ ∀ t ∈ Icc 0 𝔇, Summable (fun n => (1 + ‖n‖) ^ s * ‖a t n‖) ∧
      ∑' n, (1 + ‖n‖) ^ s * ‖a t n‖ ≤ (∑' n, (1 + ‖n‖) ^ s * ‖c n‖) * Real.exp (K * t) := by
  obtain ⟨K, hK0, hK⟩ := ha.tsum_truncWeight_le hL s
  refine ⟨K, hK0, fun t ht => ?_⟩
  set B := (∑' n, (1 + ‖n‖) ^ s * ‖c n‖) * Real.exp (K * t)
  have hM : ∀ M : ℝ, 0 ≤ M → ∑' n, truncWeight s M n * ‖a t n‖ ≤ B := by
    intro M hM0
    refine (hK M hM0 t ht).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    refine Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (min_le_left _ _)
      (norm_nonneg _)) ?_ hc
    exact Summable.of_nonneg_of_le (fun n => mul_nonneg (truncWeight_nonneg s hM0 n)
      (norm_nonneg _)) (fun n => mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)) hc
  have hfin : ∀ S : Finset (Fin d → ℤ), ∑ n ∈ S, (1 + ‖n‖) ^ s * ‖a t n‖ ≤ B := by
    intro S
    set M := ∑ n ∈ S, (1 + ‖n‖) ^ s
    have hM0 : 0 ≤ M := Finset.sum_nonneg fun n _ => by positivity
    have hsw : Summable fun n => truncWeight s M n * ‖a t n‖ :=
      Summable.of_nonneg_of_le (fun n => mul_nonneg (truncWeight_nonneg s hM0 n) (norm_nonneg _))
        (fun n => mul_le_mul_of_nonneg_right (truncWeight_le s M n) (norm_nonneg _))
        ((ha.summable_norm hL ht).mul_left M)
    calc ∑ n ∈ S, (1 + ‖n‖) ^ s * ‖a t n‖ = ∑ n ∈ S, truncWeight s M n * ‖a t n‖ := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [truncWeight, min_eq_left (Finset.single_le_sum (f := fun n => (1 + ‖n‖) ^ s)
            (fun i _ => by positivity) hn)]
      _ ≤ ∑' n, truncWeight s M n * ‖a t n‖ :=
          hsw.sum_le_tsum S (fun n _ => mul_nonneg (truncWeight_nonneg s hM0 n) (norm_nonneg _))
      _ ≤ B := hM M hM0
  have hsum : Summable fun n => (1 + ‖n‖) ^ s * ‖a t n‖ :=
    summable_of_sum_le (fun n => by positivity) hfin
  exact ⟨hsum, hsum.tsum_le_of_sum_le hfin⟩

/-- Rapidly decreasing data give a solution that decays faster than any power of `1 + ‖n‖`,
uniformly on `[0, 𝔇]` (packet NLS goal 5; FINDINGS F8). -/
theorem IsAkSolution.exists_uniform_decay (hL : 0 < L) (ha : IsAkSolution L γ δ 𝔇 c a)
    (hc : IsRapidDecay c) (N : ℕ) :
    ∃ C, ∀ t ∈ Icc 0 𝔇, ∀ n, ‖a t n‖ ≤ C * (1 + ‖n‖) ^ (-(N : ℤ)) := by
  have hcN : Summable fun n => (1 + ‖n‖) ^ N * ‖c n‖ :=
    (hc.summable_norm_mul_pow N).congr fun n => mul_comm _ _
  obtain ⟨K, hK0, hK⟩ := ha.tsum_weight_le hL N hcN
  set A := ∑' n, (1 + ‖n‖) ^ N * ‖c n‖
  have hA0 : 0 ≤ A := tsum_nonneg fun n => by positivity
  refine ⟨A * Real.exp (K * max 𝔇 0), fun t ht n => ?_⟩
  obtain ⟨hs, hle⟩ := hK t ht
  have hpos : 0 < (1 + ‖n‖) ^ N := by positivity
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  calc (1 + ‖n‖) ^ N * ‖a t n‖ ≤ ∑' m, (1 + ‖m‖) ^ N * ‖a t m‖ :=
        hs.le_tsum n (fun m _ => by positivity)
    _ ≤ A * Real.exp (K * t) := hle
    _ ≤ A * Real.exp (K * max 𝔇 0) := by
        gcongr
        exact ht.2.trans (le_max_left _ _)

end Solutions

end WaveTurbulence
