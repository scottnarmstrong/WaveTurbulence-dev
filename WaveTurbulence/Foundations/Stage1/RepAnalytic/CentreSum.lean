/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.LatticeSum

/-! # The leaf-centre decomposition `H = ∑_c χ_c H` with an `𝔖(A,0)` Leibniz bound (W5, leaf centres)

TARGET L1959: restrict each `k_ℓ` to a unit ball `|k_ℓ - k_ℓ⁰| ≤ 1`; "summability is provided by the
decay properties" of `K*`.  Here: for a `C^A` function `H` on `ℝ^d` with finite `𝔖^{A,Λ}` norm,
`Λ > d`, one has `H = ∑_{n ∈ ℤ^d} χ_n H`, each `χ_n H` supported in `|k - a n| ≤ 1`, and
`∑_n ‖χ_n H‖_{𝔖^{A,0}} ≤ C(d, A, Λ) ‖H‖_{𝔖^{A,Λ}}`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RepAnalytic
open WaveTurbulence Finset
open scoped ContDiff ENNReal

theorem chi0_jet_bound (d A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ≤ A, ∀ x, ‖iteratedFDeriv ℝ r (chi0 d) x‖ ≤ C := by
  have h1 : ∀ r : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ r (chi0 d) x‖ ≤ C := fun r =>
    ((chi0_contDiff d).continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      ((chi0_hasCompactSupport d).iteratedFDeriv r)
  choose C hC using h1
  refine ⟨∑ r ∈ Finset.range (A + 1), |C r|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun r hr x => ?_⟩
  refine (hC r x).trans ?_
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun r => |C r|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hr)))

theorem iteratedFDeriv_chi (d : ℕ) (n : Fin d → ℤ) (r : ℕ) (x : Mom d) :
    iteratedFDeriv ℝ r (chi d n) x = iteratedFDeriv ℝ r (chi0 d) (x - latPt d n) :=
  iteratedFDeriv_comp_sub (f := chi0 d) r (latPt d n) x

/-- The complex-valued partition function. -/
noncomputable def chiC (d : ℕ) (n : Fin d → ℤ) (k : Mom d) : ℂ := ((chi d n k : ℝ) : ℂ)

theorem chiC_contDiff (d : ℕ) (n : Fin d → ℤ) (A : ℕ) : ContDiff ℝ A (chiC d n) :=
  (Complex.ofRealCLM.contDiff).comp ((chi_contDiff d n).of_le (by exact_mod_cast le_top))

theorem norm_iteratedFDeriv_chiC (d : ℕ) (n : Fin d → ℤ) (r : ℕ) (x : Mom d) :
    ‖iteratedFDeriv ℝ r (chiC d n) x‖ = ‖iteratedFDeriv ℝ r (chi d n) x‖ := by
  have hc : chiC d n = Complex.ofRealLI ∘ chi d n := rfl
  rw [hc]
  exact LinearIsometry.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (n := ∞) Complex.ofRealLI
    ((chi_contDiff d n).contDiffAt (x := x)) (i := r) (by exact_mod_cast le_top)

/-- Brackets at nearby points are comparable. -/
theorem jbr_le_two_mul {d : ℕ} {x c : Mom d} (h : ‖x - c‖ ≤ 1) : jbr c ≤ 2 * jbr x := by
  have hx := Induct.jbr_pos x
  have hxx : jbr x ^ 2 = 1 + ‖x‖ ^ 2 := by
    unfold jbr; rw [Real.sq_sqrt (by positivity)]
  unfold jbr at hx ⊢
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hc : ‖c‖ ≤ ‖x‖ + 1 := by
    calc ‖c‖ = ‖x - (x - c)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖ + ‖x - c‖ := norm_sub_le _ _
      _ ≤ ‖x‖ + 1 := by linarith
  have hsq : ‖c‖ ^ 2 ≤ (‖x‖ + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
  have : (2 * Real.sqrt (1 + ‖x‖ ^ 2)) ^ 2 = 4 * (1 + ‖x‖ ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  rw [this]
  nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]

theorem chi_jet_poly_bound (d A Λ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : Fin d → ℤ), ∀ r ≤ A, ∀ x : Mom d,
      ‖iteratedFDeriv ℝ r (chiC d n) x‖ ≤ (C * ((jbr (latPt d n)) ^ Λ)⁻¹) * jbr x ^ Λ := by
  obtain ⟨C0, hC0, hC⟩ := chi0_jet_bound d A
  refine ⟨C0 * 2 ^ Λ, by positivity, fun n r hr x => ?_⟩
  rw [norm_iteratedFDeriv_chiC, iteratedFDeriv_chi]
  have hJc := Induct.jbr_pos (latPt d n)
  have hJx := Induct.jbr_pos x
  by_cases hx : ‖x - latPt d n‖ ≤ 1
  · have h2 := jbr_le_two_mul hx
    have h3 : jbr (latPt d n) ^ Λ ≤ 2 ^ Λ * jbr x ^ Λ := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hJc.le h2 Λ
    have h4 : 1 ≤ (2 ^ Λ * jbr x ^ Λ) * ((jbr (latPt d n)) ^ Λ)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; simpa using h3
    calc ‖iteratedFDeriv ℝ r (chi0 d) (x - latPt d n)‖ ≤ C0 := hC r hr _
      _ = C0 * 1 := (mul_one _).symm
      _ ≤ C0 * ((2 ^ Λ * jbr x ^ Λ) * ((jbr (latPt d n)) ^ Λ)⁻¹) :=
          mul_le_mul_of_nonneg_left h4 hC0
      _ = _ := by ring
  · have hz : iteratedFDeriv ℝ r (chi0 d) (x - latPt d n) = 0 := by
      by_contra hne
      have hmem := support_iteratedFDeriv_subset (𝕜 := ℝ) r (Function.mem_support.2 hne)
      have hsub : tsupport (chi0 d) ⊆ Metric.closedBall 0 1 :=
        closure_minimal (fun k hk => by simpa using norm_le_one_of_chi0_ne_zero hk)
          Metric.isClosed_closedBall
      have := hsub hmem
      simp only [Metric.mem_closedBall, dist_zero_right] at this
      exact hx this
    rw [hz, norm_zero]
    positivity

end WaveTurbulence.RepAnalytic
