/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NTSP.TermBounds
public import WaveTurbulence.Foundations.NTSP.LatticeSums

/-!
# The full Poisson-dual sum, and TARGET Lemma 5.2

For `|s| ≤ κL`, `L ≥ 1`, `λ ≥ 1`, the per-term majorants of the integrals with frequencies
`(Lg + ξ, Lh + ζ)`, `(g, h) ∈ ℤ^{2d}`, sum to `≲ λ^{2d+2} ⟨s⟩^{-d}` (`tsum_termBound_le`): the
majorant factors as `⟨s⟩^{-d} B(g) B'(h)` with `B(g) = (1 + (|Lg + ξ + sb| - λ√d|s|)₊/⟨s⟩)^{-(d+1)}`
(`termBound_le_factor`), and each factor sums over a lattice of spacing `L/⟨s⟩ ≥ 1/(1+κ)`.

With `Φ ≡ 1`, `λ = 1`, `κ = 1` this is **TARGET Lemma 5.2** (`lemlayer1`, L958–L969).
-/

public section

noncomputable section

open MeasureTheory Metric

namespace WaveTurbulence.NTSP

variable {d : ℕ}

/-- The factorization of the per-term majorant. -/
theorem termBound_le_factor {N : ℕ} (hN : 2 * (d + 1) ≤ N) (lam s : ℝ) (P Q : Mom d) :
    termBound d N lam s P Q ≤ 4 ^ (d + 1) * ((1 + |s|) ^ d)⁻¹ *
      ((1 + max (‖P‖ - |s| * (lam * Real.sqrt d)) 0 / (1 + |s|)) ^ (d + 1))⁻¹ *
      ((1 + max (‖Q‖ - |s| * (lam * Real.sqrt d)) 0 / (1 + |s|)) ^ (d + 1))⁻¹ := by
  set S := 1 + |s|
  have hS : 1 ≤ S := le_add_of_nonneg_right (abs_nonneg s)
  have hS0 : 0 < S := by linarith
  set u := max (‖P‖ - |s| * (lam * Real.sqrt d)) 0
  set u' := max (‖Q‖ - |s| * (lam * Real.sqrt d)) 0
  have hu : 0 ≤ u := le_max_right _ _
  have hu' : 0 ≤ u' := le_max_right _ _
  set M := max u u'
  have hM : 0 ≤ M := le_max_of_le_left hu
  set X := (1 + u / S) ^ (d + 1)
  set X' := (1 + u' / S) ^ (d + 1)
  have hX : 0 < X := by positivity
  have hX' : 0 < X' := by positivity
  have hXX : X * X' ≤ (1 + M / S) ^ (2 * (d + 1)) := by
    rw [two_mul, pow_add]
    have h1 : 1 + u / S ≤ 1 + M / S := by gcongr; exact le_max_left u u'
    have h2 : 1 + u' / S ≤ 1 + M / S := by gcongr; exact le_max_right u u'
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) h1 _) (pow_le_pow_left₀ (by positivity) h2 _)
      (by positivity) (by positivity)
  -- the majorant is at most `min(S^{-d}, (1 + M)^{-N})`
  have hw : decayW N (‖P‖ - |s| * (lam * Real.sqrt d)) = ((1 + u) ^ N)⁻¹ := rfl
  have hw' : decayW N (‖Q‖ - |s| * (lam * Real.sqrt d)) = ((1 + u') ^ N)⁻¹ := rfl
  have hT : termBound d N lam s P Q ≤ min ((S ^ d)⁻¹) (((1 + M) ^ N)⁻¹) := by
    rw [termBound, hw, hw']
    refine min_le_min le_rfl ?_
    rcases le_total u u' with h | h
    · rw [show M = u' from max_eq_right h]; exact min_le_right _ _
    · rw [show M = u from max_eq_left h]; exact min_le_left _ _
  have hkey : min ((S ^ d)⁻¹) (((1 + M) ^ N)⁻¹) * (X * X') ≤ 4 ^ (d + 1) * (S ^ d)⁻¹ := by
    rcases le_total M S with h | h
    · have h1 : (1 + M / S) ^ (2 * (d + 1)) ≤ 4 ^ (d + 1) := by
        have : M / S ≤ 1 := (div_le_one hS0).2 h
        calc (1 + M / S) ^ (2 * (d + 1)) ≤ (2 : ℝ) ^ (2 * (d + 1)) :=
              pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + M / S)
                (by linarith : 1 + M / S ≤ 2) (2 * (d + 1))
          _ = 4 ^ (d + 1) := by rw [pow_mul]; norm_num
      calc min ((S ^ d)⁻¹) (((1 + M) ^ N)⁻¹) * (X * X') ≤ (S ^ d)⁻¹ * 4 ^ (d + 1) :=
            mul_le_mul (min_le_left _ _) (hXX.trans h1) (by positivity) (by positivity)
        _ = 4 ^ (d + 1) * (S ^ d)⁻¹ := mul_comm _ _
    · have hM1 : 1 ≤ M := hS.trans h
      have h1 : (1 + M / S) ^ (2 * (d + 1)) ≤ (2 * M / S) ^ (2 * (d + 1)) := by
        refine pow_le_pow_left₀ (by positivity) ?_ _
        rw [mul_div_assoc]
        have : 1 ≤ M / S := (one_le_div hS0).2 h
        linarith
      have h2 : ((1 + M) ^ N)⁻¹ * M ^ (2 * (d + 1)) ≤ 1 := by
        rw [inv_mul_le_one₀ (by positivity)]
        calc M ^ (2 * (d + 1)) ≤ M ^ N := pow_le_pow_right₀ hM1 hN
          _ ≤ (1 + M) ^ N := pow_le_pow_left₀ hM (by linarith) N
      have h3 : (S ^ (2 * (d + 1)))⁻¹ ≤ (S ^ d)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_right₀ hS (by omega))
      calc min ((S ^ d)⁻¹) (((1 + M) ^ N)⁻¹) * (X * X')
          ≤ ((1 + M) ^ N)⁻¹ * (2 * M / S) ^ (2 * (d + 1)) :=
            mul_le_mul (min_le_right _ _) (hXX.trans h1) (by positivity) (by positivity)
        _ = 4 ^ (d + 1) * (((1 + M) ^ N)⁻¹ * M ^ (2 * (d + 1))) * (S ^ (2 * (d + 1)))⁻¹ := by
            rw [div_pow, mul_pow, show (2 : ℝ) ^ (2 * (d + 1)) = 4 ^ (d + 1) by
              rw [pow_mul]; norm_num]
            ring
        _ ≤ 4 ^ (d + 1) * 1 * (S ^ d)⁻¹ := by gcongr
        _ = 4 ^ (d + 1) * (S ^ d)⁻¹ := by ring
  have hfin : termBound d N lam s P Q * (X * X') ≤ 4 ^ (d + 1) * (S ^ d)⁻¹ :=
    (mul_le_mul_of_nonneg_right hT (by positivity)).trans hkey
  calc termBound d N lam s P Q = termBound d N lam s P Q * (X * X') * (X⁻¹ * X'⁻¹) := by
        field_simp
    _ ≤ 4 ^ (d + 1) * (S ^ d)⁻¹ * (X⁻¹ * X'⁻¹) :=
        mul_le_mul_of_nonneg_right hfin (by positivity)
    _ = _ := by ring

/-- One factor of the majorant, summed over the lattice. -/
theorem lattice_factor_le {L κ lam s : ℝ} (hL : 1 ≤ L) (hκ : 0 ≤ κ) (hs : |s| ≤ κ * L)
    (hlam : 0 ≤ lam) (c : Mom d) :
    Summable (fun g : Fin d → ℤ =>
      ((1 + max (‖L • intVec g + c‖ - |s| * (lam * Real.sqrt d)) 0 / (1 + |s|)) ^
        (d + 1))⁻¹) ∧
    ∑' g : Fin d → ℤ,
      ((1 + max (‖L • intVec g + c‖ - |s| * (lam * Real.sqrt d)) 0 / (1 + |s|)) ^
        (d + 1))⁻¹ ≤ latConst d * ((1 + lam * Real.sqrt d) * (1 + κ)) ^ (d + 1) := by
  set S := 1 + |s|
  have hS0 : 0 < S := by positivity
  have hL0 : 0 < L := by linarith
  set ρ := |s| * (lam * Real.sqrt d)
  have hρ : 0 ≤ ρ := by positivity
  have heq : ∀ g : Fin d → ℤ,
      ((1 + max (‖L • intVec g + c‖ - ρ) 0 / S) ^ (d + 1))⁻¹ =
        ((1 + max (‖(L / S) • intVec g + S⁻¹ • c‖ - ρ / S) 0) ^ (d + 1))⁻¹ := fun g => by
    congr 3
    have hv : (L / S) • intVec g + S⁻¹ • c = S⁻¹ • (L • intVec g + c) := by
      rw [smul_add, smul_smul, div_eq_inv_mul]
    rw [hv, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hS0.le), ← div_eq_inv_mul,
      ← sub_div]
    rw [← max_div_div_right hS0.le, zero_div]
  simp_rw [heq]
  have hLS : 0 < L / S := div_pos hL0 hS0
  refine ⟨summable_latticeTail hLS (div_nonneg hρ hS0.le) _, ?_⟩
  refine (tsum_latticeTail_le hLS (div_nonneg hρ hS0.le) _).trans ?_
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) (latConst_nonneg d)
  have hmin : 1 / (1 + κ) ≤ min 1 (L / S) := by
    refine le_min ((div_le_one (by linarith)).2 (by linarith)) ?_
    rw [div_le_div_iff₀ (by linarith) hS0, one_mul]
    simp only [S]
    nlinarith
  have hρS : ρ / S ≤ lam * Real.sqrt d := by
    rw [div_le_iff₀ hS0]
    simp only [ρ, S]
    nlinarith [abs_nonneg s, mul_nonneg hlam (Real.sqrt_nonneg d)]
  calc (1 + ρ / S) / min 1 (L / S) ≤ (1 + lam * Real.sqrt d) / (1 / (1 + κ)) :=
        div_le_div₀ (by positivity) (by linarith) (by positivity) hmin
    _ = (1 + lam * Real.sqrt d) * (1 + κ) := by rw [div_div_eq_mul_div, div_one]

/-- The constant of the full sum. -/
@[expose] def fullConst (d : ℕ) (κ : ℝ) : ℝ :=
  4 ^ (d + 1) * latConst d ^ 2 * ((1 + Real.sqrt d) * (1 + κ)) ^ (2 * (d + 1))

theorem fullConst_nonneg (d : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ fullConst d κ := by
  unfold fullConst; have := latConst_nonneg d; positivity

/-- **The full sum of majorants**: for `|s| ≤ κL`, `L ≥ 1`, `λ ≥ 1`,
`∑_{(g,h) ∈ ℤ^{2d}} termBound ≤ C λ^{2d+2} ⟨s⟩^{-d}`. -/
theorem summable_tsum_termBound_le {N : ℕ} (hN : 2 * (d + 1) ≤ N) {L κ lam s : ℝ}
    (hL : 1 ≤ L) (hκ : 0 ≤ κ) (hs : |s| ≤ κ * L) (hlam : 1 ≤ lam) (a b ξ ζ : Mom d) :
    Summable (fun gh : (Fin d → ℤ) × (Fin d → ℤ) =>
      termBound d N lam s ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ζ) + s • a)) ∧
    ∑' gh : (Fin d → ℤ) × (Fin d → ℤ),
      termBound d N lam s ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ζ) + s • a) ≤
        fullConst d κ * lam ^ (2 * (d + 1)) * ((1 + |s|) ^ d)⁻¹ := by
  set B : (Fin d → ℤ) → ℝ := fun g =>
    ((1 + max (‖L • intVec g + (ξ + s • b)‖ - |s| * (lam * Real.sqrt d)) 0 /
      (1 + |s|)) ^ (d + 1))⁻¹
  set B' : (Fin d → ℤ) → ℝ := fun h =>
    ((1 + max (‖L • intVec h + (ζ + s • a)‖ - |s| * (lam * Real.sqrt d)) 0 /
      (1 + |s|)) ^ (d + 1))⁻¹
  obtain ⟨hB, hBle⟩ := lattice_factor_le (lam := lam) hL hκ hs (by linarith) (ξ + s • b)
  obtain ⟨hB', hB'le⟩ := lattice_factor_le (lam := lam) hL hκ hs (by linarith) (ζ + s • a)
  have hB0 : ∀ g, 0 ≤ B g := fun g => by positivity
  have hB'0 : ∀ g, 0 ≤ B' g := fun g => by positivity
  set A := 4 ^ (d + 1) * ((1 + |s|) ^ d)⁻¹
  have hA : 0 ≤ A := by positivity
  have hpt : ∀ gh : (Fin d → ℤ) × (Fin d → ℤ),
      termBound d N lam s ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ζ) + s • a) ≤
        A * (B gh.1 * B' gh.2) := fun gh => by
    refine (termBound_le_factor hN lam s _ _).trans (le_of_eq ?_)
    simp only [B, B', A, add_assoc]
    ring
  have hprod : Summable fun gh : (Fin d → ℤ) × (Fin d → ℤ) => B gh.1 * B' gh.2 :=
    summable_mul_of_summable_norm (f := B) (g := B')
      (hB.congr fun g => (Real.norm_of_nonneg (hB0 g)).symm)
      (hB'.congr fun g => (Real.norm_of_nonneg (hB'0 g)).symm)
  have hsum : Summable fun gh : (Fin d → ℤ) × (Fin d → ℤ) =>
      termBound d N lam s ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ζ) + s • a) :=
    Summable.of_nonneg_of_le (fun _ => termBound_nonneg _ _ _ _ _ _) hpt (hprod.mul_left A)
  refine ⟨hsum, ?_⟩
  have htsum : ∑' gh : (Fin d → ℤ) × (Fin d → ℤ), B gh.1 * B' gh.2 =
      (∑' g, B g) * ∑' h, B' h :=
    (tsum_mul_tsum_of_summable_norm (f := B) (g := B')
      (hB.congr fun g => (Real.norm_of_nonneg (hB0 g)).symm)
      (hB'.congr fun g => (Real.norm_of_nonneg (hB'0 g)).symm)).symm
  have hK := latConst_nonneg d
  calc ∑' gh : (Fin d → ℤ) × (Fin d → ℤ),
        termBound d N lam s ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ζ) + s • a)
      ≤ ∑' gh : (Fin d → ℤ) × (Fin d → ℤ), A * (B gh.1 * B' gh.2) :=
        Summable.tsum_le_tsum hpt hsum (hprod.mul_left A)
    _ = A * ((∑' g, B g) * ∑' h, B' h) := by rw [tsum_mul_left, htsum]
    _ ≤ A * ((latConst d * ((1 + lam * Real.sqrt d) * (1 + κ)) ^ (d + 1)) *
          (latConst d * ((1 + lam * Real.sqrt d) * (1 + κ)) ^ (d + 1))) := by
        gcongr
    _ ≤ A * ((latConst d * (lam * ((1 + Real.sqrt d) * (1 + κ))) ^ (d + 1)) *
          (latConst d * (lam * ((1 + Real.sqrt d) * (1 + κ))) ^ (d + 1))) := by
        have h1 : (1 + lam * Real.sqrt d) * (1 + κ) ≤ lam * ((1 + Real.sqrt d) * (1 + κ)) := by
          have := Real.sqrt_nonneg d
          nlinarith
        gcongr
    _ = fullConst d κ * lam ^ (2 * (d + 1)) * ((1 + |s|) ^ d)⁻¹ := by
        simp only [A, fullConst]
        generalize (1 + Real.sqrt d) * (1 + κ) = K
        rw [mul_pow lam K, two_mul, pow_add, pow_add]
        ring

/-! ### TARGET Lemma 5.2 -/

theorem ntBounds_one (N : ℕ) : NTBounds N 1 (fun _ _ : Mom d => (1 : ℂ)) where
  contDiff_left _ := contDiff_const
  contDiff_right _ := contDiff_const
  bound_left k _ x _ := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [iteratedFDeriv_const_of_ne hk.ne' (1 : ℂ)]; simp
  bound_right k _ _ y := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [iteratedFDeriv_const_of_ne hk.ne' (1 : ℂ)]; simp

theorem bilinearPhaseIntegral_chi0_eq (a b ξ ζ : Mom d) (s : ℝ) :
    Fourier.bilinearPhaseIntegral (Fourier.chi0MomSchwartz d) (Fourier.chi0MomSchwartz d)
      a b ξ ζ s = ntIntegral 1 (fun _ _ => 1) a b ξ ζ s := by
  simp [Fourier.bilinearPhaseIntegral, ntIntegral, chiScaled]

/-- **TARGET Lemma 5.2** (`lemlayer1`, L958–L969). For `|s| ≤ L` (`L ≥ 1`), uniformly in
`(a, b, ξ, ξ') ∈ (ℝ^d)^4`,
`∑_{(g,h) ∈ ℤ^{2d}} |∫∫ χ₀(x-a) χ₀(y-b) e[⟨Lg+ξ, x⟩ + ⟨Lh+ξ', y⟩ + s⟨x,y⟩] dx dy| ≤ C ⟨s⟩^{-d}`,
with `⟨s⟩ = (1 + s²)^{1/2}` and `C` depending only on `d`; the series converges absolutely. -/
theorem lemlayer1 (d : ℕ) : ∃ C : ℝ, ∀ L : ℝ, 1 ≤ L → ∀ s : ℝ, |s| ≤ L →
    ∀ a b ξ ξ' : Mom d,
      Summable (fun gh : (Fin d → ℤ) × (Fin d → ℤ) =>
        ‖Fourier.bilinearPhaseIntegral (Fourier.chi0MomSchwartz d) (Fourier.chi0MomSchwartz d)
          a b (L • intVec gh.1 + ξ) (L • intVec gh.2 + ξ') s‖) ∧
      ∑' gh : (Fin d → ℤ) × (Fin d → ℤ),
        ‖Fourier.bilinearPhaseIntegral (Fourier.chi0MomSchwartz d) (Fourier.chi0MomSchwartz d)
          a b (L • intVec gh.1 + ξ) (L • intVec gh.2 + ξ') s‖ ≤
        C / Real.sqrt (1 + s ^ 2) ^ d := by
  set N := 2 * (d + 1)
  refine ⟨termConst d N * fullConst d 1, fun L hL s hs a b ξ ξ' => ?_⟩
  obtain ⟨hsum, hle⟩ := summable_tsum_termBound_le (N := N) le_rfl hL zero_le_one
    (by rw [one_mul]; exact hs) le_rfl a b ξ ξ'
  have hpt : ∀ gh : (Fin d → ℤ) × (Fin d → ℤ),
      ‖Fourier.bilinearPhaseIntegral (Fourier.chi0MomSchwartz d) (Fourier.chi0MomSchwartz d)
          a b (L • intVec gh.1 + ξ) (L • intVec gh.2 + ξ') s‖ ≤
        termConst d N * termBound d N 1 s ((L • intVec gh.1 + ξ) + s • b)
          ((L • intVec gh.2 + ξ') + s • a) := fun gh => by
    rw [bilinearPhaseIntegral_chi0_eq]
    have h := norm_ntIntegral_le (by omega) (ntBounds_one N) le_rfl a b
      (L • intVec gh.1 + ξ) (L • intVec gh.2 + ξ') s
    simpa using h
  have hsum' := hsum.mul_left (termConst d N)
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsum', ?_⟩
  have hT := termConst_nonneg d N
  have hjap : ((1 + |s|) ^ d)⁻¹ ≤ (Real.sqrt (1 + s ^ 2) ^ d)⁻¹ := by
    refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ d)
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg s, sq_abs s]
  calc ∑' gh : (Fin d → ℤ) × (Fin d → ℤ),
        ‖Fourier.bilinearPhaseIntegral (Fourier.chi0MomSchwartz d) (Fourier.chi0MomSchwartz d)
          a b (L • intVec gh.1 + ξ) (L • intVec gh.2 + ξ') s‖
      ≤ ∑' gh : (Fin d → ℤ) × (Fin d → ℤ), termConst d N * termBound d N 1 s
          ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ξ') + s • a) :=
        Summable.tsum_le_tsum hpt (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsum')
          hsum'
    _ = termConst d N * ∑' gh : (Fin d → ℤ) × (Fin d → ℤ), termBound d N 1 s
          ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ξ') + s • a) := tsum_mul_left
    _ ≤ termConst d N * (fullConst d 1 * 1 ^ (2 * (d + 1)) * ((1 + |s|) ^ d)⁻¹) :=
        mul_le_mul_of_nonneg_left hle hT
    _ ≤ termConst d N * fullConst d 1 * (Real.sqrt (1 + s ^ 2) ^ d)⁻¹ := by
        rw [one_pow, mul_one, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left hjap (mul_nonneg hT (fullConst_nonneg d zero_le_one))
    _ = termConst d N * fullConst d 1 / Real.sqrt (1 + s ^ 2) ^ d := by rw [div_eq_mul_inv]

end WaveTurbulence.NTSP
