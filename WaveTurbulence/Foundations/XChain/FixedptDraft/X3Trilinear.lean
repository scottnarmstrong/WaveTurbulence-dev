/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3KernelNorm

/-!
# X3: the trilinear bound in weighted `ℓ^∞` (T L2337–L2338)

Write `w(k) = ⟨k⟩^{−Λ}` with `Λ ≥ d + 1`, `L ≥ 1` and `T = ∑_m ⟨m/L⟩^{−(d+1)}`.
- `weighted_triple_le`: `∑_{q₁,q₂} w(q₁) w(q₂) w(n−q₁+q₂) ≤ 3^{Λ+1} T² w(n)`. The proof uses
  `⟨n⟩^Λ ≤ 3^Λ(⟨q₁⟩^Λ + ⟨q₂⟩^Λ + ⟨r⟩^Λ)` and reindexes each of the three resulting sums.
- `norm_aNonlin_le_weight`: if `|f|, |g|, |h| ≤ A w, B w, C w`, then
  `|𝒞(f, g, h)_n| ≤ |δ/(2L^{d−γ})| · A B C · 3^{Λ+1} T² · w(n)`.

This is TARGET's "easily established" `‖ℒ₃(b,b,b)‖_Z ≤ L^{30d}‖b‖_Z³`. Here the constant is
`|c| 3^{Λ+1} T²`, absorbed later by `e^{−N_{p+1}}`.
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open Set
open scoped ENNReal

variable {d : ℕ}

theorem jbr_ge_norm (x : Mom d) : ‖x‖ ≤ jbr x :=
  Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖x‖])

theorem one_le_jbr (x : Mom d) : 1 ≤ jbr x := Real.one_le_sqrt.2 (by nlinarith [sq_nonneg ‖x‖])

/-- `⟨a − b + c⟩ ≤ ⟨a⟩ + ⟨b⟩ + ⟨c⟩`. -/
theorem jbr_sub_add_le (a b c : Mom d) : jbr (a - b + c) ≤ jbr a + jbr b + jbr c := by
  have hb := jbr_ge_norm b
  have hc := jbr_ge_norm c
  have hx : ‖a - b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have h1 : jbr (a - b + c) ≤ jbr a + ‖b‖ + ‖c‖ := by
    have hsq : jbr (a - b + c) ^ 2 ≤ (jbr a + ‖b‖ + ‖c‖) ^ 2 := by
      rw [jbr_sq, add_sq, add_sq, jbr_sq]
      have ha := jbr_ge_norm a
      have hx2 : ‖a - b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
      nlinarith [mul_le_mul_of_nonneg_right ha (norm_nonneg b), mul_le_mul_of_nonneg_right ha (norm_nonneg c),
        norm_nonneg b, norm_nonneg c]
    exact (pow_le_pow_iff_left₀ (jbr_pos'' _).le (by have := (jbr_pos'' a).le; positivity) two_ne_zero).1 hsq
  linarith

theorem rpow_add3_le {u v w Λ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hΛ : 0 ≤ Λ) :
    (u + v + w) ^ Λ ≤ 3 ^ Λ * (u ^ Λ + v ^ Λ + w ^ Λ) := by
  have h1 := le_max_left u (max v w)
  have h2 := le_trans (le_max_left v w) (le_max_right u (max v w))
  have h3 := le_trans (le_max_right v w) (le_max_right u (max v w))
  have hM : u + v + w ≤ 3 * max u (max v w) := by linarith
  have hM0 : 0 ≤ max u (max v w) := le_trans hu h1
  have hu' := Real.rpow_nonneg hu Λ; have hv' := Real.rpow_nonneg hv Λ; have hw' := Real.rpow_nonneg hw Λ
  have hMΛ : max u (max v w) ^ Λ ≤ u ^ Λ + v ^ Λ + w ^ Λ := by
    rcases le_total u (max v w) with h | h
    · rw [max_eq_right h]
      rcases le_total v w with h' | h'
      · rw [max_eq_right h']; linarith
      · rw [max_eq_left h']; linarith
    · rw [max_eq_left h]; linarith
  calc (u + v + w) ^ Λ ≤ (3 * max u (max v w)) ^ Λ := Real.rpow_le_rpow (by positivity) hM hΛ
    _ = 3 ^ Λ * max u (max v w) ^ Λ := Real.mul_rpow (by norm_num) hM0
    _ ≤ 3 ^ Λ * (u ^ Λ + v ^ Λ + w ^ Λ) := by gcongr

/-- The weight `w(k) = ⟨k/L⟩^{−Λ}`. -/
noncomputable def wt (L Λ : ℝ) (k : Fin d → ℤ) : ℝ := jbr (latticePoint L k) ^ (-Λ)

theorem wt_pos (L Λ : ℝ) (k : Fin d → ℤ) : 0 < wt L Λ k := Real.rpow_pos_of_pos (jbr_pos'' _) _

theorem wt_le {L Λ : ℝ} (hΛ : (d : ℝ) + 1 ≤ Λ) (k : Fin d → ℤ) :
    wt L Λ k ≤ jbr (latticePoint L k) ^ (-((d : ℝ) + 1)) :=
  Real.rpow_le_rpow_of_exponent_le (one_le_jbr _) (by linarith)

theorem latticePoint_sub_add (L : ℝ) (a b c : Fin d → ℤ) :
    latticePoint L (a - b + c) = latticePoint L a - latticePoint L b + latticePoint L c := by
  ext j
  simp [latticePoint, add_div, sub_div]

/-- `w(q₁) w(q₂) w(r) ≤ 3^Λ w(n) (w(q₂)w(r) + w(q₁)w(r) + w(q₁)w(q₂))` for `n = q₁ − q₂ + r`. -/
theorem wt_triple_le {L Λ : ℝ} (hΛ : 0 ≤ Λ) (n q₁ q₂ : Fin d → ℤ) :
    wt L Λ q₁ * wt L Λ q₂ * wt L Λ (n - q₁ + q₂) ≤
      3 ^ Λ * wt L Λ n * (wt L Λ q₂ * wt L Λ (n - q₁ + q₂) + wt L Λ q₁ * wt L Λ (n - q₁ + q₂) +
        wt L Λ q₁ * wt L Λ q₂) := by
  set r := n - q₁ + q₂
  have hn : n = q₁ - q₂ + r := by simp [r]
  have hb : jbr (latticePoint L n) ≤ jbr (latticePoint L q₁) + jbr (latticePoint L q₂) + jbr (latticePoint L r) := by
    rw [hn, latticePoint_sub_add]
    exact jbr_sub_add_le _ _ _
  have hJ := rpow_add3_le (jbr_pos'' (latticePoint L q₁)).le (jbr_pos'' (latticePoint L q₂)).le
    (jbr_pos'' (latticePoint L r)).le hΛ
  have hnΛ : jbr (latticePoint L n) ^ Λ ≤ 3 ^ Λ * (jbr (latticePoint L q₁) ^ Λ + jbr (latticePoint L q₂) ^ Λ +
      jbr (latticePoint L r) ^ Λ) :=
    (Real.rpow_le_rpow (jbr_pos'' _).le hb hΛ).trans hJ
  have e : ∀ k : Fin d → ℤ, jbr (latticePoint L k) ^ Λ * wt L Λ k = 1 := fun k => by
    unfold wt
    rw [← Real.rpow_add (jbr_pos'' _), add_neg_cancel, Real.rpow_zero]
  have h1 := e q₁; have h2 := e q₂; have h3 := e r; have h4 := e n
  have w1 := wt_pos L Λ q₁; have w2 := wt_pos L Λ q₂; have w3 := wt_pos L Λ r; have w4 := wt_pos L Λ n
  have hprod := mul_pos (mul_pos w1 w2) w3
  -- multiply `hnΛ` by `w(n) w₁ w₂ w₃`
  have := mul_le_mul_of_nonneg_left hnΛ (mul_pos w4 hprod).le
  set J1 := jbr (latticePoint L q₁) ^ Λ
  set J2 := jbr (latticePoint L q₂) ^ Λ
  set J3 := jbr (latticePoint L r) ^ Λ
  set J4 := jbr (latticePoint L n) ^ Λ
  calc wt L Λ q₁ * wt L Λ q₂ * wt L Λ r = (J4 * wt L Λ n) * (wt L Λ q₁ * wt L Λ q₂ * wt L Λ r) := by
        rw [h4, one_mul]
    _ = wt L Λ n * (wt L Λ q₁ * wt L Λ q₂ * wt L Λ r) * J4 := by ring
    _ ≤ wt L Λ n * (wt L Λ q₁ * wt L Λ q₂ * wt L Λ r) * (3 ^ Λ * (J1 + J2 + J3)) := this
    _ = 3 ^ Λ * wt L Λ n * ((J2 * wt L Λ q₂) * (wt L Λ q₁ * wt L Λ r) * 0 +
          wt L Λ q₂ * wt L Λ r * (J1 * wt L Λ q₁) + wt L Λ q₁ * wt L Λ r * (J2 * wt L Λ q₂) +
          wt L Λ q₁ * wt L Λ q₂ * (J3 * wt L Λ r)) := by ring
    _ = 3 ^ Λ * wt L Λ n * (wt L Λ q₂ * wt L Λ r + wt L Λ q₁ * wt L Λ r + wt L Λ q₁ * wt L Λ q₂) := by
        rw [h1, h2, h3]; ring

/-- **The weighted triple sum.** -/
theorem weighted_triple_le {L Λ : ℝ} (hL : 1 ≤ L) (hΛ : (d : ℝ) + 1 ≤ Λ) (n : Fin d → ℤ) :
    ∑' q : (Fin d → ℤ) × (Fin d → ℤ),
      ENNReal.ofReal (wt L Λ q.1 * wt L Λ q.2 * wt L Λ (n - q.1 + q.2)) ≤
      ENNReal.ofReal (3 ^ (Λ + 1) * latSum d L ^ 2 * wt L Λ n) := by
  have hΛ0 : 0 ≤ Λ := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  set S : ℝ≥0∞ := ∑' m : Fin d → ℤ, ENNReal.ofReal (wt L Λ m)
  have hS : S ≤ ENNReal.ofReal (latSum d L) := by
    rw [latSum, ENNReal.ofReal_tsum_of_nonneg (fun _ => Real.rpow_nonneg (jbr_pos'' _).le _)
      (summable_jbr_rpow_neg hL)]
    exact ENNReal.tsum_le_tsum fun m => ENNReal.ofReal_le_ofReal (wt_le hΛ m)
  -- the three reindexed sums
  have hshift : ∀ q₂ : Fin d → ℤ, ∑' q₁ : Fin d → ℤ, ENNReal.ofReal (wt L Λ (n - q₁ + q₂)) = S := fun q₂ =>
    (Equiv.tsum_eq (⟨fun q₁ => n - q₁ + q₂, fun m => n - m + q₂, fun q => by ext j; simp only [Pi.add_apply, Pi.sub_apply]; ring,
        fun m => by ext j; simp only [Pi.add_apply, Pi.sub_apply]; ring⟩ :
      (Fin d → ℤ) ≃ (Fin d → ℤ)) fun m => ENNReal.ofReal (wt L Λ m))
  have hshift' : ∀ q₁ : Fin d → ℤ, ∑' q₂ : Fin d → ℤ, ENNReal.ofReal (wt L Λ (n - q₁ + q₂)) = S := fun q₁ =>
    (Equiv.tsum_eq (⟨fun q₂ => n - q₁ + q₂, fun m => m - n + q₁, fun q => by ext j; simp only [Pi.add_apply, Pi.sub_apply]; ring,
        fun m => by ext j; simp only [Pi.add_apply, Pi.sub_apply]; ring⟩ :
      (Fin d → ℤ) ≃ (Fin d → ℤ)) fun m => ENNReal.ofReal (wt L Λ m))
  have A1 : ∑' q : (Fin d → ℤ) × (Fin d → ℤ), ENNReal.ofReal (wt L Λ q.2 * wt L Λ (n - q.1 + q.2)) = S * S := by
    rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    simp_rw [ENNReal.ofReal_mul (wt_pos L Λ _).le, ENNReal.tsum_mul_left, hshift, ENNReal.tsum_mul_right]
    rfl
  have A2 : ∑' q : (Fin d → ℤ) × (Fin d → ℤ), ENNReal.ofReal (wt L Λ q.1 * wt L Λ (n - q.1 + q.2)) = S * S := by
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.ofReal_mul (wt_pos L Λ _).le, ENNReal.tsum_mul_left, hshift', ENNReal.tsum_mul_right]
    rfl
  have A3 : ∑' q : (Fin d → ℤ) × (Fin d → ℤ), ENNReal.ofReal (wt L Λ q.1 * wt L Λ q.2) = S * S := by
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.ofReal_mul (wt_pos L Λ _).le, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    rfl
  set c := 3 ^ Λ * wt L Λ n
  have hc : 0 ≤ c := mul_nonneg (by positivity) (wt_pos L Λ n).le
  calc ∑' q : (Fin d → ℤ) × (Fin d → ℤ), ENNReal.ofReal (wt L Λ q.1 * wt L Λ q.2 * wt L Λ (n - q.1 + q.2))
      ≤ ∑' q : (Fin d → ℤ) × (Fin d → ℤ), ENNReal.ofReal c *
          (ENNReal.ofReal (wt L Λ q.2 * wt L Λ (n - q.1 + q.2)) +
            ENNReal.ofReal (wt L Λ q.1 * wt L Λ (n - q.1 + q.2)) + ENNReal.ofReal (wt L Λ q.1 * wt L Λ q.2)) := by
        refine ENNReal.tsum_le_tsum fun q => ?_
        have p1 := (wt_pos L Λ q.1).le
        have p2 := (wt_pos L Λ q.2).le
        have p3 := (wt_pos L Λ (n - q.1 + q.2)).le
        rw [← ENNReal.ofReal_add (mul_nonneg p2 p3) (mul_nonneg p1 p3),
          ← ENNReal.ofReal_add (add_nonneg (mul_nonneg p2 p3) (mul_nonneg p1 p3)) (mul_nonneg p1 p2),
          ← ENNReal.ofReal_mul hc]
        exact ENNReal.ofReal_le_ofReal (wt_triple_le hΛ0 n q.1 q.2)
    _ = ENNReal.ofReal c * (S * S + S * S + S * S) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_add, A1, A2, A3]
    _ ≤ ENNReal.ofReal c * (3 * ENNReal.ofReal (latSum d L) ^ 2) := by
        gcongr
        calc S * S + S * S + S * S = 3 * (S * S) := by ring
          _ ≤ 3 * (ENNReal.ofReal (latSum d L) * ENNReal.ofReal (latSum d L)) := by gcongr
          _ = 3 * ENNReal.ofReal (latSum d L) ^ 2 := by ring
    _ = ENNReal.ofReal (3 ^ (Λ + 1) * latSum d L ^ 2 * wt L Λ n) := by
        have hT : 0 ≤ latSum d L := tsum_nonneg fun _ => Real.rpow_nonneg (jbr_pos'' _).le _
        rw [← ENNReal.ofReal_pow hT, show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hc, Real.rpow_add (by norm_num),
          Real.rpow_one]
        congr 1
        ring

/-- The `𝒞₊` of the snapshot is dominated by the absolute cubic sum (as `NLS.enorm_aNonlin_le` for the landed
nonlinearity). -/
theorem enorm_aNonlin_le' (L γ δ t : ℝ) (f g h : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) :
    ‖aNonlin L γ δ 1 t f g h n‖ₑ ≤ ENNReal.ofReal |δ / (2 * L ^ ((d : ℝ) - γ))| * NLS.tripleAbs f g h n := by
  rw [SysAPI.aNonlin_eq_tsum_aNonlinTerm, enorm_mul, enorm_mul]
  have hI : ‖Complex.I * (((1 : ℤ) : ℂ))‖ₑ = 1 := by simp [← ofReal_norm]
  rw [hI, mul_one]
  gcongr
  · rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
  · refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun q => ?_)
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (SysAPI.norm_aNonlinTerm_le L γ δ 1 t f g h n q)

/-- **The pointwise trilinear bound.** -/
theorem norm_aNonlin_le_weight (L γ δ : ℝ) {Λ : ℝ} (hL : 1 ≤ L) (hΛ : (d : ℝ) + 1 ≤ Λ) (t : ℝ)
    {f g h : (Fin d → ℤ) → ℂ} {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hf : ∀ k, ‖f k‖ ≤ A * wt L Λ k) (hg : ∀ k, ‖g k‖ ≤ B * wt L Λ k) (hh : ∀ k, ‖h k‖ ≤ C * wt L Λ k)
    (n : Fin d → ℤ) :
    ‖aNonlin L γ δ 1 t f g h n‖ ≤
      |δ / (2 * L ^ ((d : ℝ) - γ))| * (A * B * C) * (3 ^ (Λ + 1) * latSum d L ^ 2 * wt L Λ n) := by
  have h1 := enorm_aNonlin_le' L γ δ t f g h n
  have htr : NLS.tripleAbs f g h n ≤ ENNReal.ofReal (A * B * C) *
      ENNReal.ofReal (3 ^ (Λ + 1) * latSum d L ^ 2 * wt L Λ n) := by
    unfold NLS.tripleAbs
    calc ∑' q : (Fin d → ℤ) × (Fin d → ℤ), ‖f q.1‖ₑ * ‖g q.2‖ₑ * ‖h (n - q.1 + q.2)‖ₑ
        ≤ ∑' q : (Fin d → ℤ) × (Fin d → ℤ), ENNReal.ofReal (A * B * C) *
            ENNReal.ofReal (wt L Λ q.1 * wt L Λ q.2 * wt L Λ (n - q.1 + q.2)) := by
          refine ENNReal.tsum_le_tsum fun q => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          have e : A * B * C * (wt L Λ q.1 * wt L Λ q.2 * wt L Λ (n - q.1 + q.2)) =
              (A * wt L Λ q.1) * (B * wt L Λ q.2) * (C * wt L Λ (n - q.1 + q.2)) := by ring
          rw [e, ENNReal.ofReal_mul (by have := wt_pos L Λ q.1; have := wt_pos L Λ q.2; positivity),
            ENNReal.ofReal_mul (by have := wt_pos L Λ q.1; positivity)]
          gcongr
          · rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hf _)
          · rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hg _)
          · rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hh _)
      _ = ENNReal.ofReal (A * B * C) * ∑' q : (Fin d → ℤ) × (Fin d → ℤ),
            ENNReal.ofReal (wt L Λ q.1 * wt L Λ q.2 * wt L Λ (n - q.1 + q.2)) := ENNReal.tsum_mul_left
      _ ≤ _ := by gcongr; exact weighted_triple_le hL hΛ n
  have hT : 0 ≤ latSum d L := tsum_nonneg fun _ => Real.rpow_nonneg (jbr_pos'' _).le _
  have hw := (wt_pos L Λ n).le
  have hABC : 0 ≤ A * B * C := by positivity
  have hX : 0 ≤ 3 ^ (Λ + 1) * latSum d L ^ 2 * wt L Λ n := by positivity
  have h2 := h1.trans (by gcongr : ENNReal.ofReal |δ / (2 * L ^ ((d : ℝ) - γ))| * NLS.tripleAbs f g h n ≤
    ENNReal.ofReal |δ / (2 * L ^ ((d : ℝ) - γ))| * (ENNReal.ofReal (A * B * C) *
      ENNReal.ofReal (3 ^ (Λ + 1) * latSum d L ^ 2 * wt L Λ n)))
  rw [← ENNReal.ofReal_mul hABC, ← ENNReal.ofReal_mul (abs_nonneg _), ← ofReal_norm] at h2
  have h3 := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (abs_nonneg _) (mul_nonneg hABC hX))).1 h2
  calc ‖aNonlin L γ δ 1 t f g h n‖ ≤ _ := h3
    _ = _ := by ring

end WaveTurbulence.Fixedpt
