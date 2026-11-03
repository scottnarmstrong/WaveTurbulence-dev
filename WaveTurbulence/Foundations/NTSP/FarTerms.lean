/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NTSP.FullSum

/-!
# Far Poisson modes in DH23 Lemma 6.5 (2)

With the frequencies `P_g = Lg + ξ + s b`, `Q_h = Lh + ζ + s a` and `ρ = λ√d|s| ≤ L/8`, the modes
with `|P_g| ≥ L/4` contribute (`tsum_far_le`)

  `∑_{(g,h): |P_g| ≥ L/4} termBound ≤ C λ^{2d+2} ⟨s⟩ L^{-(d+1)}`,

by the factorization of the majorant with exponent `2(d+1)` (`termBound_le_factor_gen`): one factor
`(1 + (|P_g| - ρ)₊/⟨s⟩)^{-(d+1)}` is at most `(8⟨s⟩/L)^{d+1}`, the rest is summed over the lattice.
All sums here are in `ℝ≥0∞`.
-/

public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace WaveTurbulence.NTSP

variable {d : ℕ}

/-- The factorization of the per-term majorant with a general exponent `M`, `d ≤ 2M ≤ N`. -/
theorem termBound_le_factor_gen {N M : ℕ} (hM : d ≤ 2 * M) (hN : 2 * M ≤ N) (lam s : ℝ)
    (P Q : Mom d) :
    termBound d N lam s P Q ≤ 4 ^ M * ((1 + |s|) ^ d)⁻¹ *
      ((1 + max (‖P‖ - |s| * (lam * Real.sqrt d)) 0 / (1 + |s|)) ^ M)⁻¹ *
      ((1 + max (‖Q‖ - |s| * (lam * Real.sqrt d)) 0 / (1 + |s|)) ^ M)⁻¹ := by
  set S := 1 + |s|
  have hS : 1 ≤ S := le_add_of_nonneg_right (abs_nonneg s)
  have hS0 : 0 < S := by linarith
  set u := max (‖P‖ - |s| * (lam * Real.sqrt d)) 0
  set u' := max (‖Q‖ - |s| * (lam * Real.sqrt d)) 0
  have hu : 0 ≤ u := le_max_right _ _
  have hu' : 0 ≤ u' := le_max_right _ _
  set W := max u u'
  have hW : 0 ≤ W := le_max_of_le_left hu
  set X := (1 + u / S) ^ M
  set X' := (1 + u' / S) ^ M
  have hX : 0 < X := by positivity
  have hX' : 0 < X' := by positivity
  have hXX : X * X' ≤ (1 + W / S) ^ (2 * M) := by
    rw [two_mul, pow_add]
    have h1 : 1 + u / S ≤ 1 + W / S := by gcongr; exact le_max_left u u'
    have h2 : 1 + u' / S ≤ 1 + W / S := by gcongr; exact le_max_right u u'
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) h1 _) (pow_le_pow_left₀ (by positivity) h2 _)
      (by positivity) (by positivity)
  have hw : decayW N (‖P‖ - |s| * (lam * Real.sqrt d)) = ((1 + u) ^ N)⁻¹ := rfl
  have hw' : decayW N (‖Q‖ - |s| * (lam * Real.sqrt d)) = ((1 + u') ^ N)⁻¹ := rfl
  have hT : termBound d N lam s P Q ≤ min ((S ^ d)⁻¹) (((1 + W) ^ N)⁻¹) := by
    rw [termBound, hw, hw']
    refine min_le_min le_rfl ?_
    rcases le_total u u' with h | h
    · rw [show W = u' from max_eq_right h]; exact min_le_right _ _
    · rw [show W = u from max_eq_left h]; exact min_le_left _ _
  have hkey : min ((S ^ d)⁻¹) (((1 + W) ^ N)⁻¹) * (X * X') ≤ 4 ^ M * (S ^ d)⁻¹ := by
    rcases le_total W S with h | h
    · have h1 : (1 + W / S) ^ (2 * M) ≤ 4 ^ M := by
        have : W / S ≤ 1 := (div_le_one hS0).2 h
        calc (1 + W / S) ^ (2 * M) ≤ (2 : ℝ) ^ (2 * M) :=
              pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + W / S)
                (by linarith : 1 + W / S ≤ 2) (2 * M)
          _ = 4 ^ M := by rw [pow_mul]; norm_num
      calc min ((S ^ d)⁻¹) (((1 + W) ^ N)⁻¹) * (X * X') ≤ (S ^ d)⁻¹ * 4 ^ M :=
            mul_le_mul (min_le_left _ _) (hXX.trans h1) (by positivity) (by positivity)
        _ = 4 ^ M * (S ^ d)⁻¹ := mul_comm _ _
    · have hW1 : 1 ≤ W := hS.trans h
      have h1 : (1 + W / S) ^ (2 * M) ≤ (2 * W / S) ^ (2 * M) := by
        refine pow_le_pow_left₀ (by positivity) ?_ _
        rw [mul_div_assoc]
        have : 1 ≤ W / S := (one_le_div hS0).2 h
        linarith
      have h2 : ((1 + W) ^ N)⁻¹ * W ^ (2 * M) ≤ 1 := by
        rw [inv_mul_le_one₀ (by positivity)]
        calc W ^ (2 * M) ≤ W ^ N := pow_le_pow_right₀ hW1 hN
          _ ≤ (1 + W) ^ N := pow_le_pow_left₀ hW (by linarith) N
      have h3 : (S ^ (2 * M))⁻¹ ≤ (S ^ d)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_right₀ hS hM)
      calc min ((S ^ d)⁻¹) (((1 + W) ^ N)⁻¹) * (X * X')
          ≤ ((1 + W) ^ N)⁻¹ * (2 * W / S) ^ (2 * M) :=
            mul_le_mul (min_le_right _ _) (hXX.trans h1) (by positivity) (by positivity)
        _ = 4 ^ M * (((1 + W) ^ N)⁻¹ * W ^ (2 * M)) * (S ^ (2 * M))⁻¹ := by
            rw [div_pow, mul_pow, show (2 : ℝ) ^ (2 * M) = 4 ^ M by rw [pow_mul]; norm_num]
            ring
        _ ≤ 4 ^ M * 1 * (S ^ d)⁻¹ := by gcongr
        _ = 4 ^ M * (S ^ d)⁻¹ := by ring
  have hfin : termBound d N lam s P Q * (X * X') ≤ 4 ^ M * (S ^ d)⁻¹ :=
    (mul_le_mul_of_nonneg_right hT (by positivity)).trans hkey
  calc termBound d N lam s P Q = termBound d N lam s P Q * (X * X') * (X⁻¹ * X'⁻¹) := by
        field_simp
    _ ≤ 4 ^ M * (S ^ d)⁻¹ * (X⁻¹ * X'⁻¹) :=
        mul_le_mul_of_nonneg_right hfin (by positivity)
    _ = _ := by ring

/-- The constant of the far-mode bound. -/
@[expose] def farConst (d : ℕ) (κ : ℝ) : ℝ :=
  4 ^ (2 * (d + 1)) * 8 ^ (d + 1) * latConst d ^ 2 * ((1 + Real.sqrt d) * (1 + κ)) ^ (2 * (d + 1))

theorem farConst_nonneg (d : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ farConst d κ := by
  unfold farConst; have := latConst_nonneg d; positivity

/-- **Far modes**: for `ρ = λ√d|s| ≤ L/8`, the modes with `|Lg + ξ + s b| ≥ L/4` contribute at most
`C λ^{2d+2} ⟨s⟩ L^{-(d+1)}`. -/
theorem tsum_far_le {N : ℕ} (hN : 4 * (d + 1) ≤ N) {L κ lam s : ℝ} (hL : 1 ≤ L) (hκ : 0 ≤ κ)
    (hs : |s| ≤ κ * L) (hlam : 1 ≤ lam) (hρ : |s| * (lam * Real.sqrt d) ≤ L / 8)
    (a b ξ ζ : Mom d) :
    ∑' gh : (Fin d → ℤ) × (Fin d → ℤ),
      {gh : (Fin d → ℤ) × (Fin d → ℤ) | L / 4 ≤ ‖(L • intVec gh.1 + ξ) + s • b‖}.indicator
        (fun gh => ENNReal.ofReal
          (termBound d N lam s ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ζ) + s • a))) gh ≤
      ENNReal.ofReal (farConst d κ * lam ^ (2 * (d + 1)) * (1 + |s|) / L ^ (d + 1)) := by
  set S := 1 + |s|
  have hS0 : 0 < S := by positivity
  have hL0 : 0 < L := by linarith
  set ρ := |s| * (lam * Real.sqrt d)
  set B1 : (Fin d → ℤ) → ℝ := fun g =>
    ((1 + max (‖L • intVec g + (ξ + s • b)‖ - ρ) 0 / S) ^ (d + 1))⁻¹
  set B1' : (Fin d → ℤ) → ℝ := fun h =>
    ((1 + max (‖L • intVec h + (ζ + s • a)‖ - ρ) 0 / S) ^ (d + 1))⁻¹
  obtain ⟨hB, hBle⟩ := lattice_factor_le (lam := lam) hL hκ hs (by linarith) (ξ + s • b)
  obtain ⟨hB', hB'le⟩ := lattice_factor_le (lam := lam) hL hκ hs (by linarith) (ζ + s • a)
  set K := 4 ^ (2 * (d + 1)) * 8 ^ (d + 1) * S / L ^ (d + 1)
  have hK : 0 ≤ K := by positivity
  have hpt : ∀ gh : (Fin d → ℤ) × (Fin d → ℤ),
      {gh : (Fin d → ℤ) × (Fin d → ℤ) | L / 4 ≤ ‖(L • intVec gh.1 + ξ) + s • b‖}.indicator
        (fun gh => ENNReal.ofReal
          (termBound d N lam s ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ζ) + s • a)))
        gh ≤ ENNReal.ofReal K * (ENNReal.ofReal (B1 gh.1) * ENNReal.ofReal (B1' gh.2)) := by
    intro gh
    by_cases hfar : L / 4 ≤ ‖(L • intVec gh.1 + ξ) + s • b‖
    · rw [Set.indicator_of_mem (show gh ∈ {gh : (Fin d → ℤ) × (Fin d → ℤ) |
        L / 4 ≤ ‖(L • intVec gh.1 + ξ) + s • b‖} from hfar), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul hK]
      refine ENNReal.ofReal_le_ofReal ?_
      have hg := termBound_le_factor_gen (N := N) (M := 2 * (d + 1)) (by omega) (by omega) lam s
        ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ζ) + s • a)
      refine hg.trans ?_
      set u := max (‖(L • intVec gh.1 + ξ) + s • b‖ - ρ) 0
      set u' := max (‖(L • intVec gh.2 + ζ) + s • a‖ - ρ) 0
      have hu8 : L / 8 ≤ u := le_max_of_le_left (by linarith)
      have hB1 : B1 gh.1 = ((1 + u / S) ^ (d + 1))⁻¹ := by simp only [B1, u, add_assoc]
      have hB1' : B1' gh.2 = ((1 + u' / S) ^ (d + 1))⁻¹ := by simp only [B1', u', add_assoc]
      rw [hB1, hB1']
      have hu0 : 0 ≤ u := le_max_right _ _
      have hu0' : 0 ≤ u' := le_max_right _ _
      have e1 : ((1 + u / S) ^ (2 * (d + 1)))⁻¹ =
          ((1 + u / S) ^ (d + 1))⁻¹ * ((1 + u / S) ^ (d + 1))⁻¹ := by
        rw [two_mul, pow_add, mul_inv]
      have e2 : ((1 + u / S) ^ (d + 1))⁻¹ ≤ (8 * S / L) ^ (d + 1) := by
        have h1 : L / (8 * S) ≤ 1 + u / S :=
          calc L / (8 * S) = L / 8 / S := by rw [div_div]
            _ ≤ u / S := div_le_div_of_nonneg_right hu8 hS0.le
            _ ≤ 1 + u / S := by linarith
        calc ((1 + u / S) ^ (d + 1))⁻¹ ≤ ((L / (8 * S)) ^ (d + 1))⁻¹ :=
              inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 _)
          _ = (8 * S / L) ^ (d + 1) := by rw [← inv_pow, inv_div]
      have hu'S : 0 ≤ u' / S := by positivity
      have e3 : ((1 + u' / S) ^ (2 * (d + 1)))⁻¹ ≤ ((1 + u' / S) ^ (d + 1))⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by omega))
      calc 4 ^ (2 * (d + 1)) * ((1 + |s|) ^ d)⁻¹ * ((1 + u / S) ^ (2 * (d + 1)))⁻¹ *
            ((1 + u' / S) ^ (2 * (d + 1)))⁻¹
          ≤ 4 ^ (2 * (d + 1)) * (S ^ d)⁻¹ * ((8 * S / L) ^ (d + 1) * ((1 + u / S) ^ (d + 1))⁻¹) *
            ((1 + u' / S) ^ (d + 1))⁻¹ := by
            rw [e1]
            gcongr
        _ = K * (((1 + u / S) ^ (d + 1))⁻¹ * ((1 + u' / S) ^ (d + 1))⁻¹) := by
            simp only [K]
            rw [div_pow, mul_pow, pow_succ S d]
            field_simp
    · rw [Set.indicator_of_notMem (show gh ∉ {gh : (Fin d → ℤ) × (Fin d → ℤ) |
        L / 4 ≤ ‖(L • intVec gh.1 + ξ) + s • b‖} from hfar)]
      exact bot_le
  have hsumB : ∑' g, ENNReal.ofReal (B1 g) = ENNReal.ofReal (∑' g, B1 g) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun g => by positivity) hB).symm
  have hsumB' : ∑' h, ENNReal.ofReal (B1' h) = ENNReal.ofReal (∑' h, B1' h) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun h => by positivity) hB').symm
  set X := (1 + lam * Real.sqrt d) * (1 + κ)
  have hX : X ≤ lam * ((1 + Real.sqrt d) * (1 + κ)) := by
    have := Real.sqrt_nonneg d
    simp only [X]
    nlinarith
  calc ∑' gh : (Fin d → ℤ) × (Fin d → ℤ),
        {gh : (Fin d → ℤ) × (Fin d → ℤ) | L / 4 ≤ ‖(L • intVec gh.1 + ξ) + s • b‖}.indicator
          (fun gh => ENNReal.ofReal
            (termBound d N lam s ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ζ) + s • a))) gh
      ≤ ∑' gh : (Fin d → ℤ) × (Fin d → ℤ),
          ENNReal.ofReal K * (ENNReal.ofReal (B1 gh.1) * ENNReal.ofReal (B1' gh.2)) :=
        ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal K * ((∑' g, ENNReal.ofReal (B1 g)) * ∑' h, ENNReal.ofReal (B1' h)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_prod (f := fun g h =>
          ENNReal.ofReal (B1 g) * ENNReal.ofReal (B1' h)), ← ENNReal.tsum_mul_right]
        congr 1
        refine tsum_congr fun g => ?_
        rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (latConst d * X ^ (d + 1)) *
          ENNReal.ofReal (latConst d * X ^ (d + 1))) := by
        rw [hsumB, hsumB']
        gcongr
    _ ≤ ENNReal.ofReal (farConst d κ * lam ^ (2 * (d + 1)) * (1 + |s|) / L ^ (d + 1)) := by
        rw [← ENNReal.ofReal_mul (by have := latConst_nonneg d; positivity),
          ← ENNReal.ofReal_mul hK]
        refine ENNReal.ofReal_le_ofReal ?_
        have hc := latConst_nonneg d
        have hXp : X ^ (d + 1) ≤ (lam * ((1 + Real.sqrt d) * (1 + κ))) ^ (d + 1) :=
          pow_le_pow_left₀ (by positivity) hX _
        calc K * (latConst d * X ^ (d + 1) * (latConst d * X ^ (d + 1)))
            ≤ K * (latConst d * (lam * ((1 + Real.sqrt d) * (1 + κ))) ^ (d + 1) *
                (latConst d * (lam * ((1 + Real.sqrt d) * (1 + κ))) ^ (d + 1))) := by gcongr
          _ = farConst d κ * lam ^ (2 * (d + 1)) * (1 + |s|) / L ^ (d + 1) := by
              simp only [K, farConst, S]
              generalize (1 + Real.sqrt d) * (1 + κ) = Y
              rw [mul_pow lam Y, two_mul, pow_add, pow_add, pow_add]
              ring

end WaveTurbulence.NTSP
