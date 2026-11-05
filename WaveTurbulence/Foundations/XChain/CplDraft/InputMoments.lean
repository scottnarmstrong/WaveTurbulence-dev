/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.AnsatzInputResidual
public import WaveTurbulence.Foundations.XChain.AnsatzInputKernelBound
public import WaveTurbulence.Foundations.XChain.CumulantEmbedding
public import WaveTurbulence.Foundations.XChain.WeightedMomentFromCumulants
public import WaveTurbulence.Foundations.XChain.RandomSeries
public import WaveTurbulence.Foundations.XChain.ForestBracketWeightSum

/-!
# CPL-1, step 1: finite-order `ℓ¹` moments of `a(p)` from `AnsatzAt`

**Statement** (`memLp_input_l1`). Assume `AnsatzAt P … p`, rapid data on `Fev p`, `|F_p| ≤ C⟨k⟩^{-Λ_p}`,
`δ^ν ≤ 1/2`, `1 ≤ L` and `d + 1 ≤ Λ_p/2`. Then `ω ↦ ∑_n |a_n(p)|` is in `L^r(F_p)` for every
`1 ≤ r ≤ 2R_p`.

**Proof.**
- Every input cumulant of size `≤ 2R_p` is bounded by `∏_i (C+1)⟨n_i⟩^{-Λ_p/2}`
  (`norm_cumulant_input_le`). This combines INDUCT's input kernel bound and its input residual bound.
- So `𝔼|a_n|^{2q} ≤ (4q)! ((C+1)⟨n⟩^{-Λ_p/2})^{2q}` for `q ≤ R_p` (INDUCT
  `norm_moment_le_of_weighted_cumulants`).
- The `L^{2q}` norms are summable in `n`, and INDUCT's `memLp_tsum_of_norm_sum` concludes.

`AnsatzAt` controls only cumulants of size `≤ 2R_p`. So unlike INDUCT's prefix invariant, the moments here
are only of finite order.
-/

@[expose] public section

namespace WaveTurbulence.Cpl

open Finset MeasureTheory Set Induct
open scoped ENNReal

/-- The signature `(+,…,+,−,…,−)` of width `q + q`. -/
def altSig (q : ℕ) : Fin (q + q) → ℤˣ := fun j => if (j : ℕ) < q then 1 else -1

theorem prod_altSig (q : ℕ) (z : ℂ) :
    ∏ j : Fin (q + q), zpowSign (altSig q j) z = ((‖z‖ ^ (2 * q) : ℝ) : ℂ) := by
  rw [Fin.prod_univ_add]
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have h1 (i : Fin q) : zpowSign (altSig q (Fin.castAdd q i)) z = z := by
    simp [altSig, zpowSign, i.2]
  have h2 (i : Fin q) : zpowSign (altSig q (Fin.natAdd q i)) z = (starRingEnd ℂ) z := by
    simp [altSig, zpowSign, hne]
  simp only [h1, h2, prod_const, card_univ, Fintype.card_fin]
  rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]
  push_cast
  rfl

section

variable (P : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ) (p : ℕ)

omit [IsProbabilityMeasure μ] in
theorem measurable_input (ha : AnsatzAt P μ g a Fev R E Et p) (n : Fin P.d → ℤ) :
    Measurable (fun ω => a ω p n) :=
  ha.1.2.2.2.2.2.1 p ⟨Nat.cast_nonneg p, le_rfl⟩ n

/-- Every input mode has moments of every order on `F_p` (`AnsatzAt` (1)). -/
theorem memLp_input_mode (ha : AnsatzAt P μ g a Fev R E Et p) (n : Fin P.d → ℤ) (q : ℕ)
    (hq : 1 ≤ q) : MemLp (fun ω => a ω p n) (q : ℝ≥0∞) (μ.restrict (Fev p)) := by
  have hm := measurable_input P μ g a Fev R E Et p ha n
  have hint := ha.1.2.2.2.2.2.2 (q + q) (fun _ => ⟨p, Nat.cast_nonneg p, le_rfl⟩) (fun _ => n) (altSig q)
  simp only [prod_altSig] at hint
  have hre : Integrable (fun ω => ‖a ω p n‖ ^ (2 * q)) (μ.restrict (Fev p)) := by
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using hint.re
  have h2q : MemLp (fun ω => a ω p n) (((2 * q : ℕ)) : ℝ≥0∞) (μ.restrict (Fev p)) := by
    rw [← integrable_norm_rpow_iff hm.aestronglyMeasurable (by exact_mod_cast (by omega : 2 * q ≠ 0))
      (ENNReal.natCast_ne_top _)]
    simpa only [ENNReal.toReal_natCast, Real.rpow_natCast] using hre
  exact h2q.mono_exponent (by exact_mod_cast (by omega : q ≤ 2 * q))

/-- **Input cumulant bound** for every block of size `≤ 2R_p`. -/
theorem norm_cumulant_input_le (hG : IsGaussianData μ g) (ha : AnsatzAt P μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff P.L P.φin g ω))
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hsmall : P.δ ^ P.ν ≤ 1 / 2) (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF P R p (latticePoint P.L n)| ≤
      C * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ)))
    {ι : Type*} [DecidableEq ι] (ζ : ι → ℤˣ) (m : ι → (Fin P.d → ℤ)) (A : Finset ι)
    (hA : A.Nonempty) (hAR : A.card ≤ 2 * P.R p) :
    ‖cumulant (μ.restrict (Fev p)) (fun i ω => zpowSign (ζ i) (a ω p (m i))) A‖ ≤
      ∏ i ∈ A, ((C + 1) * jbr (latticePoint P.L (m i)) ^ (-(P.Lambda p : ℝ) / 2)) := by
  classical
  let e : Fin A.card ↪ ι :=
    ⟨fun k => (A.equivFin.symm k).1, fun k k' h => A.equivFin.symm.injective (Subtype.ext h)⟩
  have hmap : (univ : Finset (Fin A.card)).map e = A := by
    ext i
    simp only [mem_map]
    constructor
    · rintro ⟨k, -, rfl⟩
      exact (A.equivFin.symm k).2
    · intro hi
      exact ⟨A.equivFin ⟨i, hi⟩, mem_univ _, congrArg Subtype.val (A.equivFin.symm_apply_apply ⟨i, hi⟩)⟩
  have hcum : cumulant (μ.restrict (Fev p)) (fun i ω => zpowSign (ζ i) (a ω p (m i))) A =
      cumulant (μ.restrict (Fev p)) (fun k ω => zpowSign (ζ (e k)) (a ω p (m (e k)))) univ := by
    rw [cumulant_map_embedding (μ.restrict (Fev p)) (fun i ω => zpowSign (ζ i) (a ω p (m i))) e univ,
      hmap]
  rw [hcum]
  have hw : 1 ≤ A.card := card_pos.mpr hA
  have hk := ansatz_input_kernel_bound P μ g a Fev R E Et p ha hL hδ hsmall C hC hF hw hAR
    (fun k => ζ (e k)) (fun k => m (e k))
  have hr := ansatz_input_residual_bound P μ g hG (zero_lt_one.trans_le hL) a Fev R E Et p ha hrapid
    hw hAR (fun k => ζ (e k)) (fun k => m (e k))
  have hW : (∏ k, jbr (latticePoint P.L (m (e k)))) ^ (-(P.Lambda p : ℝ) / 2) =
      ∏ i ∈ A, jbr (latticePoint P.L (m i)) ^ (-(P.Lambda p : ℝ) / 2) := by
    rw [← Real.finsetProd_rpow univ _ (fun k _ => (jbr_pos _).le)]
    conv_rhs => rw [← hmap, prod_map]
  rw [hW] at hk hr
  set W := ∏ i ∈ A, jbr (latticePoint P.L (m i)) ^ (-(P.Lambda p : ℝ) / 2) with hWdef
  have hW0 : 0 ≤ W := prod_nonneg fun i _ => Real.rpow_nonneg (jbr_pos _).le _
  have hexp : Real.exp (-(P.N p : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hC1 : (1 : ℝ) ≤ C + 1 := by linarith
  have hpow : C + 1 ≤ (C + 1) ^ A.card := le_self_pow₀ hC1 (by omega)
  calc _ ≤ ‖lowerKernelSum P.L P.γ P.δ (inputsF P R) (fun k => ζ (e k)) p (P.N p)
          (fun k => m (e k))‖ +
        ‖cumulant (μ.restrict (Fev p)) (fun k ω => zpowSign (ζ (e k)) (a ω p (m (e k)))) univ -
          lowerKernelSum P.L P.γ P.δ (inputsF P R) (fun k => ζ (e k)) p (P.N p) (fun k => m (e k))‖ :=
        norm_le_insert' _ _
    _ ≤ C * W + W * 1 := add_le_add hk (hr.trans (mul_le_mul_of_nonneg_left hexp hW0))
    _ = (C + 1) * W := by ring
    _ ≤ (C + 1) ^ A.card * W := mul_le_mul_of_nonneg_right hpow hW0
    _ = ∏ i ∈ A, ((C + 1) * jbr (latticePoint P.L (m i)) ^ (-(P.Lambda p : ℝ) / 2)) := by
        rw [prod_mul_distrib, prod_const]

/-- **Input moment bound:** `𝔼_p|a_n(p)|^{2q} ≤ (4q)! ((C+1)⟨n⟩^{-Λ_p/2})^{2q}` for `1 ≤ q ≤ R_p`. -/
theorem integral_norm_input_pow_le (hG : IsGaussianData μ g) (ha : AnsatzAt P μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff P.L P.φin g ω))
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hsmall : P.δ ^ P.ν ≤ 1 / 2) (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF P R p (latticePoint P.L n)| ≤
      C * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ)))
    (n : Fin P.d → ℤ) (q : ℕ) (hq : 1 ≤ q) (hqR : q ≤ P.R p) :
    ∫ ω in Fev p, ‖a ω p n‖ ^ (2 * q) ∂μ ≤
      ((4 * q).factorial : ℝ) * ((C + 1) * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ) / 2)) ^ (2 * q) := by
  classical
  let M : ℝ := (C + 1) * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ) / 2)
  have hM0 : 0 ≤ M := mul_nonneg (by linarith) (Real.rpow_nonneg (jbr_pos _).le _)
  have hs : (univ : Finset (Fin (q + q))).Nonempty := univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩
  have hb := norm_moment_le_of_weighted_cumulants (μ.restrict (Fev p))
    (fun j ω => zpowSign (altSig q j) (a ω p n)) univ hs 0 (fun _ => M) (fun _ => hM0)
    (fun A _ hA => by
      have h := norm_cumulant_input_le P μ g a Fev R E Et p hG ha hrapid hL hδ hsmall C hC hF
        (altSig q) (fun _ => n) A hA
        ((card_le_univ A).trans (by simp only [Fintype.card_fin]; omega))
      simpa only [zero_mul, Nat.factorial_zero, Nat.cast_one, one_mul] using h)
  simp only [prod_altSig, prod_const, card_univ, Fintype.card_fin, zero_add] at hb
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun ω => by positivity)] at hb
  have hqq : q + q = 2 * q := by ring
  have h4 : 2 * (q + q) = 4 * q := by ring
  rw [h4, hqq] at hb
  exact hb

/-- **Finite-order `ℓ¹` moments** of `a(p)` on `F_p`. -/
theorem memLp_input_l1 (hG : IsGaussianData μ g) (ha : AnsatzAt P μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff P.L P.φin g ω))
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hsmall : P.δ ^ P.ν ≤ 1 / 2) (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF P R p (latticePoint P.L n)| ≤
      C * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ)))
    (hΛ : (P.d : ℝ) + 1 ≤ (P.Lambda p : ℝ) / 2) (r : ℕ) (hr : 1 ≤ r) (hrR : r ≤ 2 * P.R p) :
    MemLp (fun ω => ∑' n, ‖a ω p n‖) (r : ℝ≥0∞) (μ.restrict (Fev p)) := by
  classical
  set q := P.R p with hqdef
  have hq : 1 ≤ q := by omega
  let K : ℝ := ((4 * q).factorial : ℝ) ^ ((2 * q : ℕ) : ℝ)⁻¹ * (C + 1)
  have hK0 : 0 ≤ K := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by linarith)
  let f : (Fin P.d → ℤ) → Ω → ℝ := fun n ω => ‖a ω p n‖
  have hf (n : Fin P.d → ℤ) : MemLp (f n) (((2 * q : ℕ)) : ℝ≥0∞) (μ.restrict (Fev p)) :=
    (memLp_input_mode P μ g a Fev R E Et p ha n (2 * q) (by omega)).norm
  have h2q0 : (((2 * q : ℕ)) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : 2 * q ≠ 0)
  have hnorm (n : Fin P.d → ℤ) : eLpNorm (f n) (((2 * q : ℕ)) : ℝ≥0∞) (μ.restrict (Fev p)) ≤
      ENNReal.ofReal (K * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ) / 2)) := by
    rw [(hf n).eLpNorm_eq_integral_rpow_norm h2q0 (ENNReal.natCast_ne_top _)]
    apply ENNReal.ofReal_le_ofReal
    simp only [ENNReal.toReal_natCast, f, norm_norm, Real.rpow_natCast]
    have hI := integral_norm_input_pow_le P μ g a Fev R E Et p hG ha hrapid hL hδ hsmall C hC hF n q hq
      le_rfl
    have hI0 : 0 ≤ ∫ ω in Fev p, ‖a ω p n‖ ^ (2 * q) ∂μ := integral_nonneg fun ω => by positivity
    have hpos : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * q)
    have hM0 : 0 ≤ (C + 1) * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ) / 2) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg (jbr_pos _).le _)
    calc (∫ ω in Fev p, ‖a ω p n‖ ^ (2 * q) ∂μ) ^ ((2 * q : ℕ) : ℝ)⁻¹
        ≤ (((4 * q).factorial : ℝ) * ((C + 1) * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ) / 2)) ^
            (2 * q)) ^ ((2 * q : ℕ) : ℝ)⁻¹ :=
          Real.rpow_le_rpow hI0 hI (inv_nonneg.mpr hpos.le)
      _ = K * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ) / 2) := by
          rw [Real.mul_rpow (Nat.cast_nonneg _) (pow_nonneg hM0 _), ← Real.rpow_natCast,
            ← Real.rpow_mul hM0, mul_inv_cancel₀ hpos.ne', Real.rpow_one]
          ring
  have hsum : Summable (fun n : Fin P.d → ℤ => K * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ) / 2)) := by
    have h := summable_lattice_bracket_weight P.L ((P.Lambda p : ℝ) / 2) hL hΛ
    simpa only [neg_div] using h.mul_left K
  have hs : ∑' n, eLpNorm (f n) (((2 * q : ℕ)) : ℝ≥0∞) (μ.restrict (Fev p)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hnorm)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hK0 (Real.rpow_nonneg (jbr_pos _).le _)) hsum]
    exact ENNReal.ofReal_ne_top
  have h1 : (1 : ℝ≥0∞) ≤ (((2 * q : ℕ)) : ℝ≥0∞) := by exact_mod_cast (by omega : 1 ≤ 2 * q)
  have hl := memLp_tsum_of_norm_sum h1 f hf hs
  exact hl.mono_exponent (by exact_mod_cast hrR)

end

end WaveTurbulence.Cpl
