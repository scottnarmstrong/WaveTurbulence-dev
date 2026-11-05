/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RungFull
public import WaveTurbulence.Foundations.Spine.Poisson1D
public import WaveTurbulence.Foundations.Sumint.CutoffRescale
public import WaveTurbulence.Foundations.Sumint.InputCutoffLattice
public import WaveTurbulence.Foundations.LemLin.TensorFactorization
/-! # The rung with a sharp indicator in one variable (S3b LADDER-DECAY)

Weight `ι(x) χ_a(x) χ_b(y)` with `ι` bounded and supported in a short cube.  Absolute summation in
`x` of the `y`-sums, each factorised and estimated by the one-dimensional Poisson tail bound. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset MeasureTheory Set WaveTurbulence WaveTurbulence.WeylSums WaveTurbulence.Sumint

variable {d : ℕ}

/-- Rung weights with an arbitrary bounded factor in the first variable. -/
noncomputable def ballW (L : ℝ) (a b : Fin d → ℝ) (ι : (Fin d → ℤ) → ℂ) (p : Pt d) : ℂ :=
  ι p.1 * cutW L a b p

/-- The fixed finite box of `y`-values. -/
noncomputable def byBox (L : ℝ) (b : Fin d → ℝ) : Finset (Fin d → ℤ) :=
  Counting.latticeBox (fun j => L * b j) (4 * L)

/-- Factorisation of the `y`-sum of a rung with a first-variable weight. -/
theorem rungSum_ball_eq {L : ℝ} (hL : 0 < L) (a b : Fin d → ℝ) (ι : (Fin d → ℤ) → ℂ)
    (Qx : Finset (Fin d → ℤ)) (c : ℝ) (lam ν : Pt d →+ ℝ) (t : ℝ × ℝ) :
    rungSum L c (ballW L a b ι) (Qx ×ˢ byBox L b) lam ν t =
      ∑ x ∈ Qx, (ι x * (inputCutoff a (latticePoint L x) : ℂ) *
        e (inner ℝ (latticePoint L x) (repVec L (Pt.left (t.2 • lam + ν))))) *
      ∏ i, LemLin.scalarLatticeSum (4 * L) (b i / 4)
        (-(4 * (repVec L (Pt.right (t.2 • lam + ν)) i) +
          4 * (c * (t.2 - t.1)) * (x i : ℝ) / L)) := by
  unfold rungSum
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  set κ : ℝ := c * (t.2 - t.1) with hκ
  set ξ0 := repVec L (Pt.left (t.2 • lam + ν)) with hξ0
  set ζ0 := repVec L (Pt.right (t.2 • lam + ν)) with hζ0
  set w : Mom d := ζ0 + κ • latticePoint L x with hw
  -- termwise factorisation
  have hterm : ∀ y ∈ byBox L b, ballW L a b ι (x, y) * e (κ * bil L (x, y) + (t.2 * lam (x, y) + ν (x, y))) =
      (ι x * (inputCutoff a (latticePoint L x) : ℂ) * e (inner ℝ (latticePoint L x) ξ0)) *
        (((inputCutoff b (latticePoint L y) : ℝ) : ℂ) * (Real.fourierChar (inner ℝ w (latticePoint L y)) : ℂ)) := by
    intro y _
    have h := addHom_pt_eq hL.ne' (t.2 • lam + ν) (x, y)
    simp only [AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul] at h
    rw [fourierChar_eq_e]
    have hphase : κ * bil L (x, y) + (t.2 * lam (x, y) + ν (x, y)) =
        inner ℝ (latticePoint L x) ξ0 + inner ℝ w (latticePoint L y) := by
      rw [h, hw, inner_add_left, inner_smul_left, bil]
      simp only [conj_trivial]
      have hc : inner ℝ ζ0 (latticePoint L y) = inner ℝ (latticePoint L y) ζ0 := real_inner_comm _ _
      rw [hc]
      ring
    rw [hphase, e_add]
    simp only [ballW, cutW, Complex.ofReal_mul]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  have hsupp : ∀ y ∉ byBox L b, (((inputCutoff b (latticePoint L y) : ℝ) : ℂ) *
      (Real.fourierChar (inner ℝ w (latticePoint L y)) : ℂ)) = 0 := by
    intro y hy
    have : inputCutoff b (latticePoint L y) = 0 := by
      by_contra h
      exact hy (inputCutoff_mem_integerBox hL b y h)
    simp [this]
  rw [← tsum_eq_sum (L := SummationFilter.unconditional _) hsupp]
  have h1 := inputCutoff_linear_sum_eq L b w
  have h2 : ∀ y : Fin d → ℤ, (inputCutoff b (latticePoint L y) : ℂ) *
      (Real.fourierChar (inner ℝ w (latticePoint L y)) : ℂ) =
      (inputCutoff b (latticePoint L y) : ℂ) *
        (Real.fourierChar (inner ℝ w (latticePoint L y)) : ℂ) := fun _ => rfl
  rw [h1, LemLin.linearLatticeSum_eq_prod (by linarith)]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have e2 : -(((4 : ℝ) • w) i) = -(4 * (ζ0 i) + 4 * κ * (x i : ℝ) / L) := by
    simp only [hw, latticePoint, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
  have e1 : (((1 / 4 : ℝ) • WithLp.toLp 2 b) i) = b i / 4 := by simp [div_eq_inv_mul]
  rw [e1, e2]

/-- Absolute summation in the sharp variable. -/
theorem norm_rungSum_ball_le {L : ℝ} (hL : 0 < L) (a b : Fin d → ℝ) (ι : (Fin d → ℤ) → ℂ)
    (hι : ∀ x, ‖ι x‖ ≤ 1) (I : Fin d → Finset ℤ) (_hQ : ∀ x, ι x ≠ 0 → x ∈ Fintype.piFinset I)
    (c : ℝ) (lam ν : Pt d →+ ℝ) (t : ℝ × ℝ) :
    ‖rungSum L c (ballW L a b ι) (Fintype.piFinset I ×ˢ byBox L b) lam ν t‖ ≤
      ∏ i, ∑ n ∈ I i, ‖LemLin.scalarLatticeSum (4 * L) (b i / 4)
        (-(4 * (repVec L (Pt.right (t.2 • lam + ν)) i)) +
          (-(4 * (c * (t.2 - t.1)) / L)) * (n : ℝ))‖ := by
  classical
  rw [rungSum_ball_eq hL a b ι (Fintype.piFinset I) c lam ν t]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_le_sum (fun x hx => ?_)
  rw [norm_mul, norm_mul, norm_mul, norm_e, mul_one, Complex.norm_real]
  have hca : ‖inputCutoff a (latticePoint L x)‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (inputCutoff_nonneg _ _)]; exact inputCutoff_le_one _ _
  have h1 : ‖ι x‖ * ‖inputCutoff a (latticePoint L x)‖ ≤ 1 :=
    (mul_le_of_le_one_left (norm_nonneg _) (hι x)).trans hca
  rw [norm_prod]
  have hprod : ∏ i, ‖LemLin.scalarLatticeSum (4 * L) (b i / 4)
        (-(4 * (repVec L (Pt.right (t.2 • lam + ν)) i) + 4 * (c * (t.2 - t.1)) * (x i : ℝ) / L))‖ =
      ∏ i, ‖LemLin.scalarLatticeSum (4 * L) (b i / 4)
        (-(4 * (repVec L (Pt.right (t.2 • lam + ν)) i)) + (-(4 * (c * (t.2 - t.1)) / L)) * (x i : ℝ))‖ := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    congr 2
    ring
  rw [hprod]
  have h2 : 0 ≤ ∏ i, ‖LemLin.scalarLatticeSum (4 * L) (b i / 4)
        (-(4 * (repVec L (Pt.right (t.2 • lam + ν)) i)) + (-(4 * (c * (t.2 - t.1)) / L)) * (x i : ℝ))‖ :=
    Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  nlinarith [mul_nonneg (norm_nonneg (ι x)) (norm_nonneg (inputCutoff a (latticePoint L x)))]

/-- Rescaling the kernel time: the same rung sum at unit coefficient. -/
lemma rungSum_c_eq (L c : ℝ) (w : Pt d → ℂ) (S : Finset (Pt d)) (lam ν : Pt d →+ ℝ) (s τ : ℝ) :
    rungSum L c w S lam ν (s, τ) = rungSum L 1 w S lam ν (τ + c * (s - τ), τ) := by
  unfold rungSum
  refine Finset.sum_congr rfl (fun p _ => ?_)
  congr 2
  ring

/-- Trivial bound of the `y`-sums: each scalar factor is at most `3 L'`. -/
theorem norm_rungSum_ball_trivial {L : ℝ} (hL : 1 ≤ L) (a b : Fin d → ℝ) (ι : (Fin d → ℤ) → ℂ)
    (hι : ∀ x, ‖ι x‖ ≤ 1) (I : Fin d → Finset ℤ) (hQ : ∀ x, ι x ≠ 0 → x ∈ Fintype.piFinset I)
    (c : ℝ) (lam ν : Pt d →+ ℝ) (t : ℝ × ℝ) :
    ‖rungSum L c (ballW L a b ι) (Fintype.piFinset I ×ˢ byBox L b) lam ν t‖ ≤
      ∏ i, ((I i).card * (3 * (4 * L))) := by
  refine (norm_rungSum_ball_le (by linarith) a b ι hι I hQ c lam ν t).trans ?_
  refine Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (fun i _ => ?_)
  calc _ ≤ ∑ _n ∈ I i, (3 * (4 * L)) :=
        Finset.sum_le_sum (fun n _ => LemLin.norm_scalarLatticeSum_le (by linarith) _ _)
    _ = _ := by simp

lemma one_add_pow_le (y : ℝ) (hy : 0 ≤ y) (d : ℕ) : (1 + y) ^ d ≤ 2 ^ d * (1 + y ^ d) := by
  have h1 : 1 + y ≤ 2 * max 1 y := by
    rcases le_total 1 y with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  calc (1 + y) ^ d ≤ (2 * max 1 y) ^ d := pow_le_pow_left₀ (by linarith) h1 d
    _ = 2 ^ d * max 1 y ^ d := by rw [mul_pow]
    _ ≤ 2 ^ d * (1 + y ^ d) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases le_total 1 y with h | h
        · rw [max_eq_right h]; linarith [(one_pow d : (1 : ℝ) ^ d = 1), pow_nonneg hy d]
        · rw [max_eq_left h]; linarith [(one_pow d : (1 : ℝ) ^ d = 1), pow_nonneg hy d]

lemma three_pow_eq (X : ℝ) (d : ℕ) : (3 * X) ^ d = (6 * X) ^ d * ((2 : ℝ) ^ d)⁻¹ := by
  have : (6 * X) ^ d = 2 ^ d * (3 * X) ^ d := by rw [← mul_pow]; congr 1; ring
  rw [this, mul_comm ((2 : ℝ) ^ d), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), mul_one]

lemma ball_alg (C1 C0 L' s : ℝ) (d : ℕ) (hC1 : 0 ≤ C1) (h2 : 2 * C1 ≤ C0) (h4 : 4 * C1 ≤ C0)
    (hL' : 1 ≤ L') (hs : 1 ≤ s) :
    (C1 * L' * (1 + L' / s)) ^ d ≤ (C0 * L') ^ d * 1 + (C0 * L' ^ 2) ^ d * ((1 + s) ^ d)⁻¹ := by
  have hs0 : 0 < s := by linarith
  have hy : 0 ≤ L' / s := by positivity
  have h1 : (1 + L' / s) ^ d ≤ 2 ^ d * (1 + (L' / s) ^ d) := one_add_pow_le _ hy d
  have hinv : (s ^ d)⁻¹ ≤ 2 ^ d * ((1 + s) ^ d)⁻¹ := by
    have h : (1 + s) ^ d ≤ 2 ^ d * s ^ d := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) d
    calc (s ^ d)⁻¹ = 2 ^ d * ((2 ^ d * s ^ d)⁻¹) := by
          field_simp
      _ ≤ 2 ^ d * ((1 + s) ^ d)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h) (by positivity)
  have hA : (C1 * L') ^ d * (1 + L' / s) ^ d ≤ (C1 * L') ^ d * (2 ^ d * (1 + (L' / s) ^ d)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have hyd : (L' / s) ^ d ≤ L' ^ d * (2 ^ d * ((1 + s) ^ d)⁻¹) := by
    rw [div_pow, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have hB : (C1 * L') ^ d * (2 ^ d * (1 + (L' / s) ^ d)) ≤
      (2 * C1 * L') ^ d + (4 * C1 * L' ^ 2) ^ d * ((1 + s) ^ d)⁻¹ := by
    have e1 : (C1 * L') ^ d * (2 ^ d * (1 + (L' / s) ^ d)) =
        (2 * C1 * L') ^ d + (2 * C1 * L') ^ d * (L' / s) ^ d := by
      simp only [mul_pow]; ring
    have e2 : (4 * C1 * L' ^ 2) ^ d = (2 * C1 * L') ^ d * (L' ^ d * 2 ^ d) := by
      rw [show (4 : ℝ) * C1 * L' ^ 2 = 2 * 2 * C1 * L' * L' by ring]
      simp only [mul_pow]
      ring
    rw [e1]
    refine add_le_add le_rfl ?_
    calc (2 * C1 * L') ^ d * (L' / s) ^ d
        ≤ (2 * C1 * L') ^ d * (L' ^ d * (2 ^ d * ((1 + s) ^ d)⁻¹)) :=
          mul_le_mul_of_nonneg_left hyd (by positivity)
      _ = (4 * C1 * L' ^ 2) ^ d * ((1 + s) ^ d)⁻¹ := by rw [e2]; ring
  have hC : (2 * C1 * L') ^ d ≤ (C0 * L') ^ d * 1 := by
    rw [mul_one]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h2 (by linarith)) d
  have hD : (4 * C1 * L' ^ 2) ^ d * ((1 + s) ^ d)⁻¹ ≤ (C0 * L' ^ 2) ^ d * ((1 + s) ^ d)⁻¹ :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right h4 (by positivity)) d) (by positivity)
  calc (C1 * L' * (1 + L' / s)) ^ d = (C1 * L') ^ d * (1 + L' / s) ^ d := by rw [mul_pow]
    _ ≤ _ := hA.trans (hB.trans (add_le_add hC hD))

/-- **Pointwise majorant of the one-variable-sharp rung.** -/
theorem ball_majorant : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ {L : ℝ}, 1 ≤ L → ∀ (d : ℕ) (a b : Fin d → ℝ)
    (ι : (Fin d → ℤ) → ℂ), (∀ x, ‖ι x‖ ≤ 1) → ∀ (I : Fin d → Finset ℤ),
    (∀ x, ι x ≠ 0 → x ∈ Fintype.piFinset I) → ∀ (lam ν : Pt d →+ ℝ) (τ Ls Kc : ℝ), 0 ≤ Kc →
    (∀ i, ((I i).card : ℝ) ≤ Kc ∧ ∀ n ∈ I i, ∀ n' ∈ I i, |(n : ℝ) - n'| ≤ Kc) → Kc ≤ 4 * L →
    2 * Ls * Kc ≤ (4 * L) ^ 2 → ∀ σ : ℝ, |σ| ≤ Ls →
      ‖rungSum L 1 (ballW L a b ι) (Fintype.piFinset I ×ˢ byBox L b) lam ν (τ + σ / 16, τ)‖ ≤
        (C0 * (4 * L)) ^ d * 1 + (C0 * (4 * L) ^ 2) ^ d * ((1 + |σ|) ^ d)⁻¹ := by
  obtain ⟨C1, hC1, hP1⟩ := scalar_progression_bound
  refine ⟨max (2 * C1) (max (4 * C1) 6), by positivity, ?_⟩
  intro L hL d a b ι hι I hQ lam ν τ Ls Kc hKc0 hI hKc hLs σ hσ
  have hLp : 0 < L := by linarith
  set L' : ℝ := 4 * L with hL'
  have hL'1 : 1 ≤ L' := by rw [hL']; linarith
  set C0 := max (2 * C1) (max (4 * C1) 6) with hC0
  have h2C : 2 * C1 ≤ C0 := le_max_left _ _
  have h4C : 4 * C1 ≤ C0 := (le_max_left _ _).trans (le_max_right _ _)
  have h6C : 6 ≤ C0 := (le_max_right _ _).trans (le_max_right _ _)
  have hσ0 : 0 ≤ |σ| := abs_nonneg σ
  have hdpos : (0 : ℝ) ≤ ((1 + |σ|) ^ d)⁻¹ := by positivity
  by_cases hs1 : |σ| < 1
  · -- trivial regime
    have hT := norm_rungSum_ball_trivial hL a b ι hι I hQ 1 lam ν (τ + σ / 16, τ)
    have hT2 : ∏ i : Fin d, (((I i).card : ℝ) * (3 * (4 * L))) ≤ (3 * L' ^ 2) ^ d := by
      calc ∏ i : Fin d, (((I i).card : ℝ) * (3 * (4 * L))) ≤ ∏ _i : Fin d, (3 * L' ^ 2) := by
            refine Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => ?_)
            have h1 := (hI i).1
            nlinarith [hKc, h1, hL'1]
        _ = (3 * L' ^ 2) ^ d := by simp
    have hlow : ((2 : ℝ) ^ d)⁻¹ ≤ ((1 + |σ|) ^ d)⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ (by linarith) (by linarith) d
    have h3 : (3 * L' ^ 2) ^ d ≤ (C0 * L' ^ 2) ^ d * ((1 + |σ|) ^ d)⁻¹ := by
      calc (3 * L' ^ 2) ^ d = (6 * L' ^ 2) ^ d * ((2 : ℝ) ^ d)⁻¹ := by
            exact three_pow_eq _ d
        _ ≤ (C0 * L' ^ 2) ^ d * ((2 : ℝ) ^ d)⁻¹ := by
            refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ d) (by positivity)
            exact mul_le_mul_of_nonneg_right h6C (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
    have h4 : 0 ≤ (C0 * L') ^ d * 1 := by positivity
    linarith
  · push Not at hs1
    have hF := norm_rungSum_ball_le hLp a b ι hι I hQ 1 lam ν (τ + σ / 16, τ)
    have hσne : σ ≠ 0 := by intro h; rw [h] at hs1; simp at hs1; linarith
    have hα : (-(4 * (1 * (((τ + σ / 16, τ) : ℝ × ℝ).2 - ((τ + σ / 16, τ) : ℝ × ℝ).1)) / L)) = σ / L' := by
      simp only [hL']; field_simp; ring
    have hαne : σ / L' ≠ 0 := div_ne_zero hσne (by positivity)
    have hfac : ∀ i : Fin d, ∑ n ∈ I i, ‖LemLin.scalarLatticeSum (4 * L) (b i / 4)
        (-(4 * (repVec L (Pt.right (τ • lam + ν)) i)) +
          (-(4 * (1 * (((τ + σ / 16, τ) : ℝ × ℝ).2 - ((τ + σ / 16, τ) : ℝ × ℝ).1)) / L)) * (n : ℝ))‖ ≤
        C1 * L' * (1 + |σ / L'|⁻¹) := by
      intro i
      rw [hα]
      refine hP1 hL'1 (b i / 4) _ (σ / L') hαne (I i) ?_ ?_
      · intro n hn n' hn'
        have h1 := (hI i).2 n hn n' hn'
        have h2 : |σ / L'| ≤ Ls / L' := by
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < L')]
          exact div_le_div_of_nonneg_right hσ (by positivity)
        calc |σ / L'| * |(n : ℝ) - n'| ≤ (Ls / L') * Kc :=
              mul_le_mul h2 h1 (abs_nonneg _) (by
                have : 0 ≤ Ls := le_trans hσ0 hσ
                positivity)
          _ ≤ L' / 2 := by
              rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
              nlinarith [hLs]
      · have h1 := (hI i).1
        nlinarith [hKc, hL'1]
    have hprod : (∏ i : Fin d, ∑ n ∈ I i, ‖LemLin.scalarLatticeSum (4 * L) (b i / 4)
        (-(4 * (repVec L (Pt.right (τ • lam + ν)) i)) +
          (-(4 * (1 * (((τ + σ / 16, τ) : ℝ × ℝ).2 - ((τ + σ / 16, τ) : ℝ × ℝ).1)) / L)) * (n : ℝ))‖) ≤
        (C1 * L' * (1 + |σ / L'|⁻¹)) ^ d := by
      calc _ ≤ ∏ _i : Fin d, (C1 * L' * (1 + |σ / L'|⁻¹)) :=
            Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (fun i _ => hfac i)
        _ = _ := by simp
    have hinv : |σ / L'|⁻¹ = L' / |σ| := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < L'), inv_div]
    rw [hinv] at hprod
    have halg := ball_alg C1 C0 L' |σ| d hC1 h2C h4C hL'1 hs1
    linarith [hF, hprod, halg]

end WaveTurbulence.LadderDecay
