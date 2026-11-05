/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Neumann
public import WaveTurbulence.Foundations.XChain.FlowerDraft.Kernel
public import WaveTurbulence.Foundations.NLS.AkClass
public import WaveTurbulence.Foundations.NLS.FourierEquation

/-!
# X3: the kernel operator on `Z` (T L2316)

`norm_kernelOp_le`: suppose `∫_p^t |𝒦^ζ_{kk'}(t,s)| ds ≤ B ⟨k − ζk'⟩^{−A}` with `A ≥ Λ + d + 1` and `L ≥ 1`. Then
`|(𝒦b)_k(t)| ≤ ⟨k⟩^{−Λ} · 2 · 2^{Λ/2} · B · S · ‖b‖_Z`, where `S = ∑_m ⟨m/L⟩^{−(d+1)} ≤ (√2 L)^{d+1} S₀(d)`.

TARGET states `‖𝒦‖_{Z→Z} ≤ L^d ‖𝒦‖_𝔑` with `‖𝒦‖_𝔑 = sup ⟨k−ζk'⟩^{(3/2)Λ_{p+1}} |𝒦(t,s)|`. Here the `s`-integral
replaces the supremum in `s` (X3-DESIGN, "the `(t,s)` supremum"), and the constant `2·2^{Λ/2}·S` replaces `L^d`.
The losses are absorbed later by `e^{−N_{p+1}}`.
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-! ## Brackets -/

theorem jbr_pos'' (x : Mom d) : 0 < jbr x := Real.sqrt_pos.2 (by positivity)

theorem jbr_sq (x : Mom d) : jbr x ^ 2 = 1 + ‖x‖ ^ 2 := Real.sq_sqrt (by positivity)

/-- Peetre: `⟨x + y⟩ ≤ √2 ⟨x⟩ ⟨y⟩`. -/
theorem jbr_add_le (x y : Mom d) : jbr (x + y) ≤ Real.sqrt 2 * jbr x * jbr y := by
  have h1 : jbr (x + y) ^ 2 ≤ (Real.sqrt 2 * jbr x * jbr y) ^ 2 := by
    rw [jbr_sq, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), jbr_sq, jbr_sq]
    have := norm_add_le x y
    have hx := norm_nonneg x
    have hy := norm_nonneg y
    have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖y‖)]
  have h0 : 0 ≤ Real.sqrt 2 * jbr x * jbr y :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (jbr_pos'' x).le) (jbr_pos'' y).le
  exact (pow_le_pow_iff_left₀ (jbr_pos'' _).le h0 two_ne_zero).1 h1

theorem jbr_rpow_add_le {Λ : ℝ} (hΛ : 0 ≤ Λ) (x y : Mom d) :
    jbr (x + y) ^ Λ ≤ 2 ^ (Λ / 2) * jbr x ^ Λ * jbr y ^ Λ := by
  have h := Real.rpow_le_rpow (jbr_pos'' _).le (jbr_add_le x y) hΛ
  have e : (Real.sqrt 2 * jbr x * jbr y) ^ Λ = 2 ^ (Λ / 2) * jbr x ^ Λ * jbr y ^ Λ := by
    rw [Real.mul_rpow (mul_nonneg (Real.sqrt_nonneg 2) (jbr_pos'' x).le) (jbr_pos'' y).le,
      Real.mul_rpow (Real.sqrt_nonneg 2) (jbr_pos'' x).le, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
    congr 3
    ring
  rw [e] at h
  exact h

theorem jbr_neg (x : Mom d) : jbr (-x) = jbr x := by simp [jbr]

theorem jbr_units_smul (ζ : ℤˣ) (x : Mom d) : jbr ((ζ : ℤ) • x) = jbr x := by
  rcases Int.units_eq_one_or ζ with h | h <;> simp [h, jbr_neg]

/-! ## Lattice sums -/

theorem one_add_norm_le_jbr {L : ℝ} (hL : 1 ≤ L) (n : Fin d → ℤ) :
    1 + ‖n‖ ≤ Real.sqrt 2 * L * jbr (latticePoint L n) := by
  have hLpos : 0 < L := by linarith
  have hcoord : ‖n‖ / L ≤ ‖latticePoint L n‖ := by
    rw [div_le_iff₀ hLpos]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    have h2 : |(n j : ℝ) / L| ^ 2 ≤ ‖latticePoint L n‖ ^ 2 := by
      rw [sq_abs, NLS.norm_latticePoint_sq]
      exact Finset.single_le_sum (f := fun j => ((n j : ℝ) / L) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    have h3 : |(n j : ℝ) / L| ≤ ‖latticePoint L n‖ :=
      (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
    rw [abs_div, abs_of_pos hLpos, div_le_iff₀ hLpos] at h3
    rw [Int.norm_eq_abs]
    exact h3
  have hj : 1 + ‖latticePoint L n‖ ≤ Real.sqrt 2 * jbr (latticePoint L n) := by
    have h1 : (1 + ‖latticePoint L n‖) ^ 2 ≤ (Real.sqrt 2 * jbr (latticePoint L n)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num), jbr_sq]
      nlinarith [sq_nonneg (‖latticePoint L n‖ - 1)]
    exact (pow_le_pow_iff_left₀ (by positivity)
      (mul_nonneg (Real.sqrt_nonneg 2) (jbr_pos'' _).le) two_ne_zero).1 h1
  calc 1 + ‖n‖ ≤ L * (1 + ‖latticePoint L n‖) := by
        have := mul_le_mul_of_nonneg_left hcoord hLpos.le
        rw [mul_div_cancel₀ _ hLpos.ne'] at this
        nlinarith
    _ ≤ L * (Real.sqrt 2 * jbr (latticePoint L n)) := mul_le_mul_of_nonneg_left hj hLpos.le
    _ = Real.sqrt 2 * L * jbr (latticePoint L n) := by ring

/-- `⟨m/L⟩^{−(d+1)} ≤ (√2 L)^{d+1} (1 + |m|)^{−(d+1)}`. -/
theorem jbr_rpow_neg_le {L : ℝ} (hL : 1 ≤ L) (m : Fin d → ℤ) :
    jbr (latticePoint L m) ^ (-((d : ℝ) + 1)) ≤ (Real.sqrt 2 * L) ^ (d + 1) * ((1 + ‖m‖) ^ (d + 1))⁻¹ := by
  have hj := jbr_pos'' (latticePoint L m)
  have h1 := one_add_norm_le_jbr hL m
  have hpos : 0 < 1 + ‖m‖ := by positivity
  have hs2L : 0 < Real.sqrt 2 * L := mul_pos (by positivity) (by linarith)
  rw [Real.rpow_neg hj.le, show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  calc (jbr (latticePoint L m) ^ (d + 1))⁻¹
      = (Real.sqrt 2 * L) ^ (d + 1) * ((Real.sqrt 2 * L * jbr (latticePoint L m)) ^ (d + 1))⁻¹ := by
        rw [mul_pow (Real.sqrt 2 * L), mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hs2L.ne'), one_mul]
    _ ≤ (Real.sqrt 2 * L) ^ (d + 1) * ((1 + ‖m‖) ^ (d + 1))⁻¹ := by
        gcongr

theorem summable_jbr_rpow_neg {L : ℝ} (hL : 1 ≤ L) :
    Summable fun m : Fin d → ℤ => jbr (latticePoint L m) ^ (-((d : ℝ) + 1)) :=
  Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (jbr_pos'' _).le _) (jbr_rpow_neg_le hL)
    (NLS.summable_inv_one_add_norm_pow.mul_left _)

/-- The lattice sum `S = ∑_m ⟨m/L⟩^{−(d+1)}`. -/
noncomputable def latSum (d : ℕ) (L : ℝ) : ℝ := ∑' m : Fin d → ℤ, jbr (latticePoint L m) ^ (-((d : ℝ) + 1))

theorem latSum_le {L : ℝ} (hL : 1 ≤ L) :
    latSum d L ≤ (Real.sqrt 2 * L) ^ (d + 1) * ∑' m : Fin d → ℤ, ((1 + ‖m‖) ^ (d + 1))⁻¹ := by
  rw [← tsum_mul_left]
  exact (summable_jbr_rpow_neg hL).tsum_le_tsum (jbr_rpow_neg_le hL)
    (NLS.summable_inv_one_add_norm_pow.mul_left _)

theorem latticePoint_sub_smul (L : ℝ) (k k' : Fin d → ℤ) (ζ : ℤˣ) :
    latticePoint L k - (ζ : ℤ) • latticePoint L k' = latticePoint L (k - (ζ : ℤ) • k') := by
  ext j
  simp [latticePoint, sub_div, mul_div_assoc]

/-- The shift `k' ↦ k − ζk'` is a bijection of `ℤ^d`. -/
noncomputable def shiftEquiv (k : Fin d → ℤ) (ζ : ℤˣ) : (Fin d → ℤ) ≃ (Fin d → ℤ) where
  toFun k' := k - (ζ : ℤ) • k'
  invFun m := (ζ : ℤ) • (k - m)
  left_inv k' := by
    simp only [sub_sub_cancel, smul_smul]
    rcases Int.units_eq_one_or ζ with h | h <;> simp [h]
  right_inv m := by
    simp only [smul_smul]
    rcases Int.units_eq_one_or ζ with h | h <;> simp [h]

theorem summable_shift {L : ℝ} (hL : 1 ≤ L) (k : Fin d → ℤ) (ζ : ℤˣ) :
    Summable fun k' : Fin d → ℤ =>
      jbr (latticePoint L k - (ζ : ℤ) • latticePoint L k') ^ (-((d : ℝ) + 1)) := by
  simp_rw [latticePoint_sub_smul]
  exact (shiftEquiv k ζ).summable_iff.2 (summable_jbr_rpow_neg hL)

theorem tsum_shift {L : ℝ} (k : Fin d → ℤ) (ζ : ℤˣ) :
    ∑' k' : Fin d → ℤ, jbr (latticePoint L k - (ζ : ℤ) • latticePoint L k') ^ (-((d : ℝ) + 1)) = latSum d L := by
  simp_rw [latticePoint_sub_smul]
  exact (shiftEquiv k ζ).tsum_eq (fun m => jbr (latticePoint L m) ^ (-((d : ℝ) + 1)))

/-! ## The kernel operator -/

theorem norm_le_of_mem_ZSpace {p : ℕ} {L Λ : ℝ} {b : SysAPI.ArrI p d} (hb : b ∈ ZSpace L Λ p)
    (t : Icc (p : ℝ) (p + 1)) (n : Fin d → ℤ) :
    ‖b t n‖ ≤ jbr (latticePoint L n) ^ (-Λ) * (ZNorm L Λ b).toReal := by
  have h : jbr (latticePoint L n) ^ Λ * ‖b t n‖ ≤ (ZNorm L Λ b).toReal := zSpace_weighted_bound hb t n
  have hw : 0 < jbr (latticePoint L n) ^ Λ := zWeight_pos L Λ n
  rw [Real.rpow_neg (jbr_pos'' _).le, ← div_eq_inv_mul, le_div_iff₀ hw, mul_comm]
  exact h

/-- **The kernel operator on `Z`.** -/
theorem norm_kernelOp_le {p : ℕ} {L Λ A B : ℝ} (hL : 1 ≤ L) (hΛ : 0 ≤ Λ) (hA : Λ + (d + 1) ≤ A) (hB : 0 ≤ B)
    {K : ℤˣ → ℝ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℂ} {b : SysAPI.ArrI p d} (hb : b ∈ ZSpace L Λ p)
    (hKint : ∀ (ζ : ℤˣ) (t : Icc (p : ℝ) (p + 1)) k k',
      IntervalIntegrable (fun s => ‖K ζ t s k k'‖) volume p t)
    (hK : ∀ (ζ : ℤˣ) (t : Icc (p : ℝ) (p + 1)) k k',
      ∫ s in (p : ℝ)..t, ‖K ζ t s k k'‖ ≤ B * jbr (latticePoint L k - (ζ : ℤ) • latticePoint L k') ^ (-A))
    (t : Icc (p : ℝ) (p + 1)) (k : Fin d → ℤ) :
    ‖SysAPI.kernelOp p K b t k‖ ≤
      jbr (latticePoint L k) ^ (-Λ) * (2 * (2 ^ (Λ / 2) * B * latSum d L * (ZNorm L Λ b).toReal)) := by
  set β := (ZNorm L Λ b).toReal
  have hβ : 0 ≤ β := ENNReal.toReal_nonneg
  have hjk := jbr_pos'' (latticePoint L k)
  -- one term
  have hterm : ∀ (ζ : ℤˣ) k', ‖∫ s in (p : ℝ)..t, K ζ t s k k' *
      zpowSign ζ (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k')‖ ≤
      jbr (latticePoint L k) ^ (-Λ) * (2 ^ (Λ / 2) * B * β *
        jbr (latticePoint L k - (ζ : ℤ) • latticePoint L k') ^ (-((d : ℝ) + 1))) := by
    intro ζ k'
    set m := latticePoint L k - (ζ : ℤ) • latticePoint L k'
    have hbk' : ∀ s, ‖zpowSign ζ (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k')‖ ≤
        jbr (latticePoint L k') ^ (-Λ) * β := fun s => by
      rw [SysAPI.norm_zpowSign]
      exact norm_le_of_mem_ZSpace hb _ k'
    have h1 : ‖∫ s in (p : ℝ)..t, K ζ t s k k' *
        zpowSign ζ (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k')‖ ≤
        ∫ s in (p : ℝ)..t, ‖K ζ t s k k'‖ * (jbr (latticePoint L k') ^ (-Λ) * β) :=
      intervalIntegral.norm_integral_le_of_norm_le t.2.1
        (ae_of_all _ fun s _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hbk' s) (norm_nonneg _))
        ((hKint ζ t k k').mul_const _)
    rw [intervalIntegral.integral_mul_const] at h1
    refine h1.trans ?_
    have hKb := hK ζ t k k'
    -- Peetre: `⟨k⟩^Λ ≤ 2^{Λ/2} ⟨m⟩^Λ ⟨k'⟩^Λ`
    have hpe : jbr (latticePoint L k) ^ Λ ≤ 2 ^ (Λ / 2) * jbr m ^ Λ * jbr (latticePoint L k') ^ Λ := by
      have := jbr_rpow_add_le hΛ m ((ζ : ℤ) • latticePoint L k')
      rwa [show m + (ζ : ℤ) • latticePoint L k' = latticePoint L k by simp [m], jbr_units_smul] at this
    have hjm := jbr_pos'' m
    have hjk' := jbr_pos'' (latticePoint L k')
    have hmA : jbr m ^ (-A) ≤ jbr m ^ (-Λ) * jbr m ^ (-((d : ℝ) + 1)) := by
      rw [← Real.rpow_add hjm]
      exact Real.rpow_le_rpow_of_exponent_le (by
        rw [jbr]; exact Real.one_le_sqrt.2 (by nlinarith [sq_nonneg ‖m‖])) (by linarith)
    calc (∫ s in (p : ℝ)..t, ‖K ζ t s k k'‖) * (jbr (latticePoint L k') ^ (-Λ) * β)
        ≤ (B * jbr m ^ (-A)) * (jbr (latticePoint L k') ^ (-Λ) * β) :=
          mul_le_mul_of_nonneg_right hKb (mul_nonneg (Real.rpow_nonneg hjk'.le _) hβ)
      _ ≤ (B * (jbr m ^ (-Λ) * jbr m ^ (-((d : ℝ) + 1)))) * (jbr (latticePoint L k') ^ (-Λ) * β) := by
          gcongr
      _ = (jbr m ^ Λ * jbr (latticePoint L k') ^ Λ)⁻¹ * (B * β * jbr m ^ (-((d : ℝ) + 1))) := by
          rw [Real.rpow_neg hjm.le, Real.rpow_neg hjk'.le, mul_inv]
          ring
      _ ≤ (jbr (latticePoint L k) ^ Λ / 2 ^ (Λ / 2))⁻¹ * (B * β * jbr m ^ (-((d : ℝ) + 1))) := by
          gcongr
          rw [div_le_iff₀ (by positivity)]
          linarith [hpe]
      _ = jbr (latticePoint L k) ^ (-Λ) * (2 ^ (Λ / 2) * B * β * jbr m ^ (-((d : ℝ) + 1))) := by
          rw [Real.rpow_neg hjk.le, inv_div]
          field_simp
  -- the sums
  have hsum : ∀ ζ : ℤˣ, ‖∑' k', ∫ s in (p : ℝ)..t, K ζ t s k k' *
      zpowSign ζ (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k')‖ ≤
      jbr (latticePoint L k) ^ (-Λ) * (2 ^ (Λ / 2) * B * β * latSum d L) := by
    intro ζ
    have hmaj : Summable fun k' => jbr (latticePoint L k) ^ (-Λ) * (2 ^ (Λ / 2) * B * β *
        jbr (latticePoint L k - (ζ : ℤ) • latticePoint L k') ^ (-((d : ℝ) + 1))) :=
      ((summable_shift hL k ζ).mul_left _).mul_left _
    refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm ζ) hmaj)).trans ?_
    refine (Summable.tsum_le_tsum (hterm ζ) (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm ζ) hmaj)
      hmaj).trans (le_of_eq ?_)
    rw [tsum_mul_left, tsum_mul_left, tsum_shift]
  unfold SysAPI.kernelOp
  refine (norm_sum_le _ _).trans ?_
  calc ∑ ζ : ℤˣ, ‖∑' k', ∫ s in (p : ℝ)..t, K ζ t s k k' *
        zpowSign ζ (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k')‖
      ≤ ∑ _ζ : ℤˣ, jbr (latticePoint L k) ^ (-Λ) * (2 ^ (Λ / 2) * B * β * latSum d L) :=
        Finset.sum_le_sum fun ζ _ => hsum ζ
    _ = jbr (latticePoint L k) ^ (-Λ) * (2 * (2 ^ (Λ / 2) * B * latSum d L * β)) := by
        rw [Finset.sum_const, Finset.card_univ, show Fintype.card ℤˣ = 2 from rfl, nsmul_eq_mul]
        push_cast
        ring

end WaveTurbulence.Fixedpt
