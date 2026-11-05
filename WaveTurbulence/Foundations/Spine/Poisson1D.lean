/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
public import WaveTurbulence.Foundations.LemLin.ScalarFinite
public import WaveTurbulence.Foundations.LemLin.LatticeTail
/-! # One-dimensional Poisson tail sums (S3b LADDER-DECAY)

For the scalar cutoff lattice sum `τ(u) = scalarLatticeSum L b u`, the sum of `‖τ‖` along an
arithmetic progression of short extent is at most `C L (1 + 1/|α|)`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset MeasureTheory WaveTurbulence WaveTurbulence.LemLin
open scoped FourierTransform

/-- Polynomial decay of the Fourier transform of the fixed cutoff. -/
theorem chi0_fourier_poly : ∃ K : ℝ, 0 ≤ K ∧ ∀ v : ℝ,
    ‖𝓕 Fourier.chi0Complex v‖ ≤ K * ((1 + |v|) ^ 2)⁻¹ := by
  refine ⟨2 * (2 * Real.exp 4 * 1 * 1) + 2 * (2 * Real.exp 4 * (16 + 16 * Real.exp 2) ^ 2 * 24), by positivity, ?_⟩
  intro v
  have h0 := Fourier.chi0_fourier_moment_le 0 v
  have h2 := Fourier.chi0_fourier_moment_le 2 v
  simp only [pow_zero, one_mul, Nat.factorial,
    Nat.cast_one, mul_one] at h0
  have h2' : (2 * Real.pi * |v|) ^ 2 * ‖𝓕 Fourier.chi0Complex v‖ ≤
      2 * Real.exp 4 * (16 + 16 * Real.exp 2) ^ 2 * 24 := by
    refine h2.trans (le_of_eq ?_)
    norm_num [Nat.factorial]
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hn := norm_nonneg (𝓕 Fourier.chi0Complex v)
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hv2 : |v| ^ 2 * ‖𝓕 Fourier.chi0Complex v‖ ≤ (2 * Real.pi * |v|) ^ 2 * ‖𝓕 Fourier.chi0Complex v‖ := by
    have : |v| ^ 2 ≤ (2 * Real.pi * |v|) ^ 2 := by
      have h1 := abs_nonneg v
      have h3 : |v| ≤ 2 * Real.pi * |v| := by nlinarith
      exact pow_le_pow_left₀ h1 h3 2
    exact mul_le_mul_of_nonneg_right this hn
  nlinarith [sq_nonneg (1 - |v|), abs_nonneg v]

/-- Poisson majorant of the scalar cutoff sum by the tail series. -/
theorem norm_scalarLatticeSum_le_tail {L : ℝ} (hL : 1 ≤ L) (b u : ℝ) {K : ℝ}
    (hK : ∀ v : ℝ, ‖𝓕 Fourier.chi0Complex v‖ ≤ K * ((1 + |v|) ^ 2)⁻¹) :
    ‖scalarLatticeSum L b u‖ ≤ L * (K * ∑' m : ℤ, ((1 + |L * m + u|) ^ 2)⁻¹) ∧
      Summable (fun m : ℤ => ((1 + |L * m + u|) ^ 2)⁻¹) := by
  have hLp : 0 < L := by linarith
  have hsum : Summable (fun m : ℤ => scalarTailWeight (L * m + u)) :=
    (scalar_lattice_tail (by linarith : 1 / 3 ≤ L) u).1
  have hsum' : Summable (fun m : ℤ => ((1 + |L * m + u|) ^ 2)⁻¹) := by
    simpa [scalarTailWeight] using hsum
  refine ⟨?_, hsum'⟩
  have hK0 : 0 ≤ K := by
    have := hK 0
    have h2 := norm_nonneg (𝓕 Fourier.chi0Complex 0)
    simp at this
    linarith
  have hnorm : ∀ m : ℤ, ‖𝓕 (scalarAmplitudeSchwartz b u) (L * m)‖ ≤
      K * ((1 + |L * m + u|) ^ 2)⁻¹ := by
    intro m
    rw [scalarAmplitude_fourier_norm]
    have := hK (L * m + u)
    rw [add_comm (L * (m : ℝ)) u] at this ⊢
    exact this
  have hs1 : Summable (fun m : ℤ => ‖𝓕 (scalarAmplitudeSchwartz b u) (L * m)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm (hsum'.mul_left K)
  rw [scalarLatticeSum_poisson hLp, norm_mul, Complex.norm_real, Real.norm_of_nonneg hLp.le]
  refine mul_le_mul_of_nonneg_left ?_ hLp.le
  calc ‖∑' m : ℤ, 𝓕 (scalarAmplitudeSchwartz b u) (L * m)‖
      ≤ ∑' m : ℤ, ‖𝓕 (scalarAmplitudeSchwartz b u) (L * m)‖ := norm_tsum_le_tsum_norm hs1
    _ ≤ ∑' m : ℤ, K * ((1 + |L * m + u|) ^ 2)⁻¹ := hs1.tsum_le_tsum hnorm (hsum'.mul_left K)
    _ = K * ∑' m : ℤ, ((1 + |L * m + u|) ^ 2)⁻¹ := tsum_mul_left

/-- A progression of spacing at least `1/3` has uniformly bounded tail sum. -/
theorem tail_progression {β : ℝ} (hβ : 1 / 3 ≤ |β|) (c0 : ℝ) (K' : Finset ℤ) :
    ∑ k ∈ K', ((1 + |c0 + β * k|) ^ 2)⁻¹ ≤ scalarTailConstant := by
  rcases le_or_gt 0 β with hb | hb
  · have hb' : 1 / 3 ≤ β := by rwa [abs_of_nonneg hb] at hβ
    have h := scalar_lattice_tail hb' c0
    have hs : Summable (fun k : ℤ => ((1 + |c0 + β * k|) ^ 2)⁻¹) := by
      simpa [scalarTailWeight, add_comm] using h.1
    calc ∑ k ∈ K', ((1 + |c0 + β * k|) ^ 2)⁻¹ ≤ ∑' k : ℤ, ((1 + |c0 + β * k|) ^ 2)⁻¹ :=
          hs.sum_le_tsum _ (fun _ _ => by positivity)
      _ ≤ scalarTailConstant := by
          have := h.2
          simpa [scalarTailWeight, add_comm] using this
  · have hb' : 1 / 3 ≤ -β := by rwa [abs_of_neg hb] at hβ
    have h := scalar_lattice_tail hb' (-c0)
    have hs : Summable (fun k : ℤ => ((1 + |c0 + β * k|) ^ 2)⁻¹) := by
      have := h.1
      refine this.congr (fun k => ?_)
      simp only [scalarTailWeight]
      congr 2
      rw [← abs_neg]; congr 1; ring
    calc ∑ k ∈ K', ((1 + |c0 + β * k|) ^ 2)⁻¹ ≤ ∑' k : ℤ, ((1 + |c0 + β * k|) ^ 2)⁻¹ :=
          hs.sum_le_tsum _ (fun _ _ => by positivity)
      _ ≤ scalarTailConstant := by
          refine le_trans (le_of_eq (tsum_congr (fun k => ?_))) h.2
          simp only [scalarTailWeight]
          congr 2
          rw [← abs_neg]; congr 1; ring

lemma tail_shift_le {x y : ℝ} (h : |x - y| ≤ 4 / 3) :
    ((1 + |x|) ^ 2)⁻¹ ≤ (49 / 9) * ((1 + |y|) ^ 2)⁻¹ := by
  have h1 : 1 + |y| ≤ (7 / 3) * (1 + |x|) := by
    have := abs_sub_abs_le_abs_sub y x
    rw [abs_sub_comm] at this
    nlinarith [abs_nonneg x, abs_nonneg y]
  have hx : 0 < 1 + |x| := by positivity
  have hy : 0 < 1 + |y| := by positivity
  have h2 : (1 + |y|) ^ 2 ≤ (49 / 9) * (1 + |x|) ^ 2 := by nlinarith [mul_pos hx hy]
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  rw [show 49 / 9 * ((1 + |y|) ^ 2)⁻¹ * (1 + |x|) ^ 2 = (49 / 9 * (1 + |x|) ^ 2) * ((1 + |y|) ^ 2)⁻¹ by ring]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith

/-- **Tail sum along a progression.** -/
theorem tail_sum_le {α : ℝ} (hα : α ≠ 0) (c0 : ℝ) (I : Finset ℤ) :
    ∑ n ∈ I, ((1 + |c0 + α * n|) ^ 2)⁻¹ ≤ 6 * scalarTailConstant * (1 + |α|⁻¹) := by
  have hct := scalarTailConstant_nonneg
  have hapos : 0 < |α| := abs_pos.mpr hα
  rcases le_or_gt (1 / 3) |α| with h3 | h3
  · calc _ ≤ scalarTailConstant := tail_progression h3 c0 I
      _ ≤ _ := by
        have : 0 ≤ |α|⁻¹ := by positivity
        nlinarith
  · set N : ℕ := ⌈|α|⁻¹⌉₊ with hNdef
    have hNge : |α|⁻¹ ≤ N := Nat.le_ceil _
    have hNlt : (N : ℝ) < |α|⁻¹ + 1 := Nat.ceil_lt_add_one (by positivity)
    have hNpos : 0 < N := by
      have : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNge
      exact_mod_cast this
    have hNZ : (0 : ℤ) < N := by exact_mod_cast hNpos
    have hαN1 : 1 ≤ |α| * N := by
      calc (1 : ℝ) = |α| * |α|⁻¹ := (mul_inv_cancel₀ hapos.ne').symm
        _ ≤ |α| * N := mul_le_mul_of_nonneg_left hNge hapos.le
    have hαN2 : |α| * N ≤ 4 / 3 + 0 := by
      have : |α| * N < |α| * (|α|⁻¹ + 1) := mul_lt_mul_of_pos_left hNlt hapos
      rw [mul_add, mul_inv_cancel₀ hapos.ne'] at this
      linarith
    have hpt : ∀ n : ℤ, ((1 + |c0 + α * n|) ^ 2)⁻¹ ≤
        (49 / 9) * ((1 + |c0 + (α * N) * ((n / N : ℤ) : ℝ)|) ^ 2)⁻¹ := by
      intro n
      apply tail_shift_le
      have hr0 : 0 ≤ n % (N : ℤ) := Int.emod_nonneg _ hNZ.ne'
      have hr1 : n % (N : ℤ) < N := Int.emod_lt_of_pos _ hNZ
      have hn : (n : ℝ) = N * ((n / N : ℤ) : ℝ) + ((n % (N : ℤ) : ℤ) : ℝ) := by
        have := Int.mul_ediv_add_emod n N
        exact_mod_cast this.symm
      have hrR0 : (0 : ℝ) ≤ ((n % (N : ℤ) : ℤ) : ℝ) := by exact_mod_cast hr0
      have hrR1 : ((n % (N : ℤ) : ℤ) : ℝ) ≤ N := by exact_mod_cast hr1.le
      have : (c0 + α * n) - (c0 + (α * N) * ((n / N : ℤ) : ℝ)) = α * ((n % (N : ℤ) : ℤ) : ℝ) := by
        rw [hn]; ring
      rw [this, abs_mul, abs_of_nonneg hrR0]
      calc |α| * ((n % (N : ℤ) : ℤ) : ℝ) ≤ |α| * N := mul_le_mul_of_nonneg_left hrR1 hapos.le
        _ ≤ 4 / 3 := by linarith
    classical
    calc ∑ n ∈ I, ((1 + |c0 + α * n|) ^ 2)⁻¹
        ≤ ∑ n ∈ I, (49 / 9) * ((1 + |c0 + (α * N) * ((n / N : ℤ) : ℝ)|) ^ 2)⁻¹ :=
          Finset.sum_le_sum (fun n _ => hpt n)
      _ = (49 / 9) * ∑ n ∈ I, ((1 + |c0 + (α * N) * ((n / N : ℤ) : ℝ)|) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
      _ = (49 / 9) * ∑ k ∈ I.image (fun n : ℤ => n / (N : ℤ)),
            ((I.filter (fun n : ℤ => n / (N : ℤ) = k)).card : ℝ) * ((1 + |c0 + (α * N) * (k : ℝ)|) ^ 2)⁻¹ := by
          congr 1
          rw [Finset.sum_comp (fun k : ℤ => ((1 + |c0 + (α * N) * (k : ℝ)|) ^ 2)⁻¹) (fun n => n / (N : ℤ))]
          simp only [nsmul_eq_mul]
      _ ≤ (49 / 9) * ∑ k ∈ I.image (fun n : ℤ => n / (N : ℤ)), (N : ℝ) * ((1 + |c0 + (α * N) * (k : ℝ)|) ^ 2)⁻¹ := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => ?_)) (by norm_num)
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hsub : I.filter (fun n : ℤ => n / (N : ℤ) = k) ⊆ Finset.Ico ((N : ℤ) * k) ((N : ℤ) * k + N) := by
            intro n hn
            rw [Finset.mem_filter] at hn
            rw [Finset.mem_Ico]
            have h1 := Int.mul_ediv_add_emod n N
            have h2 := Int.emod_nonneg n hNZ.ne'
            have h3' := Int.emod_lt_of_pos n hNZ
            rw [hn.2] at h1
            constructor <;> nlinarith
          have := Finset.card_le_card hsub
          rw [Int.card_Ico] at this
          have h4 : ((N : ℤ) * k + N - N * k).toNat = N := by omega
          rw [h4] at this
          exact_mod_cast this
      _ = (49 / 9) * (N * ∑ k ∈ I.image (fun n : ℤ => n / (N : ℤ)), ((1 + |c0 + (α * N) * (k : ℝ)|) ^ 2)⁻¹) := by
          rw [← Finset.mul_sum]
      _ ≤ (49 / 9) * (N * scalarTailConstant) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by norm_num)
          refine tail_progression ?_ c0 _
          rw [abs_mul, abs_of_pos (by exact_mod_cast hNpos : (0 : ℝ) < N)]
          linarith
      _ ≤ _ := by
          have : (N : ℝ) ≤ |α|⁻¹ + 1 := hNlt.le
          have h5 : (N : ℝ) * scalarTailConstant ≤ (|α|⁻¹ + 1) * scalarTailConstant :=
            mul_le_mul_of_nonneg_right this hct
          nlinarith

/-- The scalar cutoff sum is `L`-periodic in its frequency. -/
theorem scalarLatticeSum_add_period {L : ℝ} (hL : 0 < L) (b u : ℝ) (k : ℤ) :
    scalarLatticeSum L b (u + L * k) = scalarLatticeSum L b u := by
  unfold scalarLatticeSum
  refine tsum_congr (fun n => ?_)
  unfold scalarAmplitude
  congr 1
  have h : (-(u + L * k) * ((n : ℝ) / L)) = (-u * ((n : ℝ) / L)) + ((-(k * n : ℤ) : ℤ) : ℝ) := by
    push_cast; field_simp; ring
  rw [h, AddChar.map_add_eq_mul, Circle.coe_mul]
  have : ((Real.fourierChar ((-(k * n : ℤ) : ℤ) : ℝ) : Circle) : ℂ) = 1 := by
    rw [Real.fourierChar_apply]
    rw [show ((2 * Real.pi * ((-(k * n : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I =
      ((-(k * n : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [this, mul_one]

/-- Far tail of the Poisson series. -/
theorem far_tail {L : ℝ} (hL : 1 ≤ L) {u : ℝ} (hu : |u| ≤ L) :
    ∑' m : ℤ, ((1 + |L * m + u|) ^ 2)⁻¹ ≤
      ∑ m ∈ ({-1, 0, 1} : Finset ℤ), ((1 + |L * m + u|) ^ 2)⁻¹ + 16 * scalarTailConstant / L ^ 2 := by
  have hLp : 0 < L := by linarith
  have hsum : Summable (fun m : ℤ => ((1 + |L * m + u|) ^ 2)⁻¹) := by
    have := (scalar_lattice_tail (by linarith : 1 / 3 ≤ L) u).1
    simpa [scalarTailWeight] using this
  have hsum1 : Summable (fun m : ℤ => ((1 + |(1 : ℝ) * m + 0|) ^ 2)⁻¹) := by
    have := (scalar_lattice_tail (by norm_num : (1 : ℝ) / 3 ≤ 1) 0).1
    simpa [scalarTailWeight] using this
  have hpt : ∀ m : ℤ, ((1 + |L * m + u|) ^ 2)⁻¹ ≤
      (if m ∈ ({-1, 0, 1} : Finset ℤ) then ((1 + |L * m + u|) ^ 2)⁻¹ else 0) +
        (16 / L ^ 2) * ((1 + |(1 : ℝ) * m + 0|) ^ 2)⁻¹ := by
    intro m
    by_cases hm : m ∈ ({-1, 0, 1} : Finset ℤ)
    · rw [ite_eq_left hm]
      have : 0 ≤ (16 / L ^ 2) * ((1 + |(1 : ℝ) * m + 0|) ^ 2)⁻¹ := by positivity
      linarith
    · rw [ite_eq_right hm, zero_add]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      have hm2 : (2 : ℝ) ≤ |(m : ℝ)| := by
        have : 2 ≤ |m| := by rcases abs_cases m with h | h <;> omega
        have h2 : ((2 : ℤ) : ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast this
        simpa using h2
      have h1 : (L / 4) * (1 + |(m : ℝ)|) ≤ 1 + |L * m + u| := by
        have h0 : |L * m| ≤ |L * m + u| + |u| := by
          have := abs_sub (L * m + u) u
          simpa using this
        rw [abs_mul, abs_of_pos hLp] at h0
        nlinarith [abs_nonneg u, abs_nonneg (L * m + u)]
      have h3 : 0 < (L / 4) * (1 + |(m : ℝ)|) := by positivity
      have h4 : ((1 + |L * m + u|) ^ 2)⁻¹ ≤ (((L / 4) * (1 + |(m : ℝ)|)) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ h3.le h1 2)
      refine h4.trans (le_of_eq ?_)
      simp only [one_mul, add_zero]
      field_simp
      ring
  have hfin : Summable (fun m : ℤ => (if m ∈ ({-1, 0, 1} : Finset ℤ) then ((1 + |L * m + u|) ^ 2)⁻¹ else 0)) :=
    summable_of_ne_finset_zero (s := ({-1, 0, 1} : Finset ℤ)) (fun m hm => by rw [ite_eq_right hm])
  calc ∑' m : ℤ, ((1 + |L * m + u|) ^ 2)⁻¹
      ≤ ∑' m : ℤ, ((if m ∈ ({-1, 0, 1} : Finset ℤ) then ((1 + |L * m + u|) ^ 2)⁻¹ else 0) +
        (16 / L ^ 2) * ((1 + |(1 : ℝ) * m + 0|) ^ 2)⁻¹) :=
        Summable.tsum_le_tsum hpt hsum (hfin.add (hsum1.mul_left _))
    _ = ∑' m : ℤ, (if m ∈ ({-1, 0, 1} : Finset ℤ) then ((1 + |L * m + u|) ^ 2)⁻¹ else 0) +
        (16 / L ^ 2) * ∑' m : ℤ, ((1 + |(1 : ℝ) * m + 0|) ^ 2)⁻¹ := by
        rw [hfin.tsum_add (hsum1.mul_left _), tsum_mul_left]
    _ ≤ ∑ m ∈ ({-1, 0, 1} : Finset ℤ), ((1 + |L * m + u|) ^ 2)⁻¹ +
        16 * scalarTailConstant / L ^ 2 := by
        refine add_le_add (le_of_eq ?_) ?_
        · rw [tsum_eq_sum (s := ({-1, 0, 1} : Finset ℤ)) (fun m hm => by rw [ite_eq_right hm])]
          exact Finset.sum_congr rfl (fun m hm => by rw [ite_eq_left hm])
        · have := (scalar_lattice_tail (by norm_num : (1 : ℝ) / 3 ≤ 1) 0).2
          have h5 : ∑' m : ℤ, ((1 + |(1 : ℝ) * m + 0|) ^ 2)⁻¹ ≤ scalarTailConstant := by
            simpa [scalarTailWeight] using this
          calc (16 / L ^ 2) * ∑' m : ℤ, ((1 + |(1 : ℝ) * m + 0|) ^ 2)⁻¹
              ≤ (16 / L ^ 2) * scalarTailConstant := mul_le_mul_of_nonneg_left h5 (by positivity)
            _ = _ := by ring

/-- **The one-dimensional progression bound.** -/
theorem scalar_progression_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 1 ≤ L → ∀ (b u0 α : ℝ), α ≠ 0 →
    ∀ I : Finset ℤ, (∀ n ∈ I, ∀ n' ∈ I, |α| * |(n : ℝ) - n'| ≤ L / 2) → (I.card : ℝ) ≤ L ^ 2 →
    ∑ n ∈ I, ‖scalarLatticeSum L b (u0 + α * n)‖ ≤ C * L * (1 + |α|⁻¹) := by
  obtain ⟨K, hK0, hK⟩ := chi0_fourier_poly
  have hct := scalarTailConstant_nonneg
  refine ⟨K * (34 * scalarTailConstant), by positivity, ?_⟩
  intro L hL b u0 α hα I hdiam hcard
  have hLp : 0 < L := by linarith
  have hapos : 0 < |α| := abs_pos.mpr hα
  rcases I.eq_empty_or_nonempty with rfl | ⟨n1, hn1⟩
  · simp; positivity
  set x1 := u0 + α * n1 with hx1
  set m1 : ℤ := ⌊-x1 / L + 1 / 2⌋ with hm1
  have hm1a : |x1 + L * m1| ≤ L / 2 := by
    have h1 := Int.floor_le (-x1 / L + 1 / 2)
    have h2 := Int.lt_floor_add_one (-x1 / L + 1 / 2)
    rw [← hm1] at h1 h2
    have h3 : x1 + L * m1 = L * (m1 + x1 / L) := by
      rw [mul_add, mul_div_cancel₀ _ hLp.ne']; ring
    rw [h3, abs_mul, abs_of_pos hLp]
    have e : -x1 / L = -(x1 / L) := neg_div _ _
    rw [e] at h1 h2
    have h4 : |(m1 : ℝ) + x1 / L| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith
    nlinarith
  -- shifted points
  have hshift : ∀ n ∈ I, ‖scalarLatticeSum L b (u0 + α * n)‖ =
      ‖scalarLatticeSum L b ((u0 + L * m1) + α * n)‖ := by
    intro n _
    rw [show (u0 + L * m1) + α * n = (u0 + α * n) + L * m1 by ring,
      scalarLatticeSum_add_period hLp]
  have hbd : ∀ n ∈ I, |(u0 + L * m1) + α * n| ≤ L := by
    intro n hn
    have h1 : (u0 + L * m1) + α * n = (x1 + L * m1) + α * ((n : ℝ) - n1) := by rw [hx1]; ring
    rw [h1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have := hdiam n hn n1 hn1
    linarith
  have hpt : ∀ n ∈ I, ‖scalarLatticeSum L b ((u0 + L * m1) + α * n)‖ ≤
      L * K * (∑ m ∈ ({-1, 0, 1} : Finset ℤ), ((1 + |L * m + ((u0 + L * m1) + α * n)|) ^ 2)⁻¹ +
        16 * scalarTailConstant / L ^ 2) := by
    intro n hn
    obtain ⟨h1, h2⟩ := norm_scalarLatticeSum_le_tail hL b ((u0 + L * m1) + α * n) hK
    have hft := far_tail hL (hbd n hn)
    calc _ ≤ L * (K * ∑' m : ℤ, ((1 + |L * m + ((u0 + L * m1) + α * n)|) ^ 2)⁻¹) := h1
      _ ≤ L * (K * (∑ m ∈ ({-1, 0, 1} : Finset ℤ), ((1 + |L * m + ((u0 + L * m1) + α * n)|) ^ 2)⁻¹ +
          16 * scalarTailConstant / L ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hft hK0) hLp.le
      _ = _ := by ring
  calc ∑ n ∈ I, ‖scalarLatticeSum L b (u0 + α * n)‖
      = ∑ n ∈ I, ‖scalarLatticeSum L b ((u0 + L * m1) + α * n)‖ :=
        Finset.sum_congr rfl hshift
    _ ≤ ∑ n ∈ I, L * K * (∑ m ∈ ({-1, 0, 1} : Finset ℤ),
          ((1 + |L * m + ((u0 + L * m1) + α * n)|) ^ 2)⁻¹ + 16 * scalarTailConstant / L ^ 2) :=
        Finset.sum_le_sum hpt
    _ = L * K * (∑ m ∈ ({-1, 0, 1} : Finset ℤ), ∑ n ∈ I,
          ((1 + |(L * m + (u0 + L * m1)) + α * n|) ^ 2)⁻¹ + I.card * (16 * scalarTailConstant / L ^ 2)) := by
        have e1 : ∀ n : ℤ, ∑ m ∈ ({-1, 0, 1} : Finset ℤ), ((1 + |L * m + ((u0 + L * m1) + α * n)|) ^ 2)⁻¹ =
            ∑ m ∈ ({-1, 0, 1} : Finset ℤ), ((1 + |(L * m + (u0 + L * m1)) + α * n|) ^ 2)⁻¹ := by
          intro n
          refine Finset.sum_congr rfl (fun m _ => ?_)
          congr 3; ring
        simp_rw [e1]
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm]
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ L * K * (3 * (6 * scalarTailConstant * (1 + |α|⁻¹)) + 16 * scalarTailConstant) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
        · calc ∑ m ∈ ({-1, 0, 1} : Finset ℤ), ∑ n ∈ I, ((1 + |(L * m + (u0 + L * m1)) + α * n|) ^ 2)⁻¹
              ≤ ∑ _m ∈ ({-1, 0, 1} : Finset ℤ), 6 * scalarTailConstant * (1 + |α|⁻¹) :=
                Finset.sum_le_sum (fun m _ => tail_sum_le hα _ I)
            _ = 3 * (6 * scalarTailConstant * (1 + |α|⁻¹)) := by simp
        · calc (I.card : ℝ) * (16 * scalarTailConstant / L ^ 2)
              ≤ L ^ 2 * (16 * scalarTailConstant / L ^ 2) :=
                mul_le_mul_of_nonneg_right hcard (by positivity)
            _ = 16 * scalarTailConstant := by field_simp
    _ ≤ K * (34 * scalarTailConstant) * L * (1 + |α|⁻¹) := by
        have h0 : 0 ≤ |α|⁻¹ := by positivity
        have h1 : (1 : ℝ) ≤ 1 + |α|⁻¹ := by linarith
        have h2 : 16 * scalarTailConstant ≤ 16 * scalarTailConstant * (1 + |α|⁻¹) := by
          nlinarith
        have h3 : 0 ≤ L * K := by positivity
        nlinarith [mul_nonneg h3 hct]

end WaveTurbulence.LadderDecay
