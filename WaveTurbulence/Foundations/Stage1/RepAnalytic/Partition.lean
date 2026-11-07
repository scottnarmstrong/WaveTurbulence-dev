/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.PartitionOneD
public import WaveTurbulence.Foundations.Spine.WeightedSmoothMultiplier
public import WaveTurbulence.Foundations.VineEst.VineEstS3.PiProd

/-! # A translation-invariant smooth partition of unity on `ℝ^d` by unit balls

TARGET L1959 ("we may decompose (redvine) by restricting each `k_ℓ` to a unit ball `|k_ℓ - k_ℓ⁰| ≤ 1`"
and the same for nodes).  The partition is `χ_n(k) = χ₀(k - a n)`, `n ∈ ℤ^d`, `a = 1/(d+1)`,
`χ₀(k) = ∏_i θ(k_i / a + 1)`.  All the `χ_n` are translates of one compactly supported smooth function,
so every derivative bound is uniform in `n`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RepAnalytic
open WaveTurbulence Finset
open scoped ContDiff

/-- Lattice spacing `a = 1/(d+1)`. -/
noncomputable def lsp (d : ℕ) : ℝ := 1 / ((d : ℝ) + 1)

theorem lsp_pos (d : ℕ) : 0 < lsp d := by unfold lsp; positivity

/-- The lattice point `a n`. -/
noncomputable def latPt (d : ℕ) (n : Fin d → ℤ) : Mom d := WithLp.toLp 2 fun i => lsp d * (n i : ℝ)

/-- The model bump `χ₀(k) = ∏_i θ(k_i/a + 1)`, supported in `|k_i| ≤ a`. -/
noncomputable def chi0 (d : ℕ) (k : Mom d) : ℝ := ∏ i, theta1 (k i / lsp d + 1)

/-- The `n`-th partition function. -/
noncomputable def chi (d : ℕ) (n : Fin d → ℤ) (k : Mom d) : ℝ := chi0 d (k - latPt d n)

theorem chi0_nonneg (d : ℕ) (k : Mom d) : 0 ≤ chi0 d k :=
  Finset.prod_nonneg fun i _ => theta1_nonneg _

theorem chi_nonneg (d : ℕ) (n : Fin d → ℤ) (k : Mom d) : 0 ≤ chi d n k := chi0_nonneg d _

theorem chi0_contDiff (d : ℕ) : ContDiff ℝ ∞ (chi0 d) := by
  unfold chi0
  refine contDiff_prod fun i _ => theta1_contDiff.comp ?_
  have : ContDiff ℝ ∞ (fun k : Mom d => k i) := (EuclideanSpace.proj i : Mom d →L[ℝ] ℝ).contDiff
  exact (this.div_const _).add contDiff_const

theorem chi_contDiff (d : ℕ) (n : Fin d → ℤ) : ContDiff ℝ ∞ (chi d n) :=
  (chi0_contDiff d).comp (contDiff_id.sub contDiff_const)

/-- The support of `χ₀` lies in the unit ball. -/
theorem norm_le_one_of_chi0_ne_zero {d : ℕ} {k : Mom d} (h : chi0 d k ≠ 0) : ‖k‖ ≤ 1 := by
  have hi : ∀ i, |k i| < lsp d := by
    intro i
    have hne : theta1 (k i / lsp d + 1) ≠ 0 := fun h0 =>
      h (Finset.prod_eq_zero (Finset.mem_univ i) h0)
    obtain ⟨h1, h2⟩ := theta1_pos_lt hne
    have ha := lsp_pos d
    rw [abs_lt]
    constructor
    · have : -1 < k i / lsp d := by linarith
      rw [lt_div_iff₀ ha] at this; linarith
    · have : k i / lsp d < 1 := by linarith
      rw [div_lt_iff₀ ha] at this; linarith
  have hsq : ‖k‖ ^ 2 ≤ 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    calc ∑ i, k i ^ 2 ≤ ∑ _i : Fin d, lsp d ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            have := hi i
            nlinarith [abs_nonneg (k i), sq_abs (k i)]
      _ = (d : ℝ) * lsp d ^ 2 := by simp
      _ ≤ 1 := by
        unfold lsp
        rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
        nlinarith [sq_nonneg ((d : ℝ) - 1), (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  nlinarith [norm_nonneg k]

theorem norm_sub_le_one_of_chi_ne_zero {d : ℕ} {n : Fin d → ℤ} {k : Mom d} (h : chi d n k ≠ 0) :
    ‖k - latPt d n‖ ≤ 1 :=
  norm_le_one_of_chi0_ne_zero h

theorem chi0_hasCompactSupport (d : ℕ) : HasCompactSupport (chi0 d) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Mom d) 1) fun k hk => by
    simpa using norm_le_one_of_chi0_ne_zero hk

/-- **Partition of unity**: `∑_{n ∈ ℤ^d} χ_n = 1`. -/
theorem hasSum_chi (d : ℕ) (k : Mom d) : HasSum (fun n : Fin d → ℤ => chi d n k) 1 := by
  have key : ∀ n : Fin d → ℤ, chi d n k = ∏ i, theta1 (k i / lsp d - (n i : ℝ) + 1) := by
    intro n
    unfold chi chi0 latPt
    refine Finset.prod_congr rfl fun i _ => ?_
    have ha := (lsp_pos d).ne'
    congr 1
    simp only [WithLp.ofLp_sub, Pi.sub_apply]
    field_simp
  simp_rw [key]
  have hs : ∀ i : Fin d, Summable fun m : ℤ => ‖theta1 (k i / lsp d - (m : ℝ) + 1)‖ := fun i =>
    ((hasSum_theta1 (k i / lsp d)).summable.norm)
  have := (VineEstS3.Eng.hasSum_pi_prod_fin (M := ℤ) (𝕜 := ℝ) d
    (fun i (m : ℤ) => theta1 (k i / lsp d - (m : ℝ) + 1)) hs).2
  simpa [(hasSum_theta1 _).tsum_eq] using this

end WaveTurbulence.RepAnalytic
