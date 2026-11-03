/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NTSP.Lemma65One

/-!
# The near terms of DH23 Lemma 6.5 (2): a one-dimensional measure estimate

The near Poisson modes of DH23 L1047–L1072 are controlled by the measure of the set of `s` for
which `L m + c + s β` is close to `0` for some `m ∈ ℤ` ("fractional part" argument). We prove the
weighted form (`lintegral_near_le`): for `d ≥ 3`, `N ≥ 4`, `L > 0`, `β ≠ 0`,

  `∫_{|s| > L/(4√d|β|)} ∑_{m ∈ ℤ} min(⟨s⟩^{-d}, (1 + (|Lm + c + sβ| - λ√d|s|)₊)^{-N}) ds
      ≤ C (λ + 1) / L`.

Proof: on the dyadic block `2^j ≤ ⟨s⟩ < 2^{j+1}` the integrand is at most
`∑_m f_j(Lm + c + sβ)` with `f_j(t) = min(2^{-jd}, ω(|t| - 2^{j+1}λ√d))`; after the change of
variables `t = Lm + c + sβ`, each point `t` is covered by at most `2^j|β|/L + 1` of the `m`
(`tsum_indicator_Icc_le`), and on a nonempty block `|β|^{-1} ≤ 8√d 2^j/L`; finally
`∫ f_j ≤ 2^{j+2}λ√d 2^{-jd} + 2 c₂ 2^{-jd/2}`, which sums over `j` for `d ≥ 3`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.NTSP

variable {d : ℕ}

/-! ### Counting lattice points in an interval -/

/-- At most `w/L + 1` multiples of `L` lie in an interval of length `w`. -/
theorem tsum_indicator_Icc_le {L : ℝ} (hL : 0 < L) (x w : ℝ) (hw : 0 ≤ w) :
    ∑' m : ℤ, (Icc x (x + w)).indicator (fun _ => (1 : ℝ≥0∞)) (L * m) ≤
      ENNReal.ofReal (w / L + 1) := by
  set F : Finset ℤ := Finset.Icc ⌈x / L⌉ ⌊(x + w) / L⌋
  have hsupp : ∀ m ∉ F, (Icc x (x + w)).indicator (fun _ => (1 : ℝ≥0∞)) (L * m) = 0 := by
    intro m hm
    rw [Set.indicator_of_notMem]
    intro hmem
    apply hm
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.ceil_le, div_le_iff₀ hL, mul_comm]; exact hmem.1
    · rw [Int.le_floor, le_div_iff₀ hL, mul_comm]
      exact hmem.2
  rw [tsum_eq_sum hsupp]
  calc ∑ m ∈ F, (Icc x (x + w)).indicator (fun _ => (1 : ℝ≥0∞)) (L * m)
      ≤ ∑ _m ∈ F, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun m _ => by unfold Set.indicator; split_ifs <;> simp
    _ = (F.card : ℝ≥0∞) := by simp
    _ ≤ ENNReal.ofReal (w / L + 1) := by
        rw [← ENNReal.ofReal_natCast]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Int.card_Icc]
        have h1 : ((⌊(x + w) / L⌋ + 1 - ⌈x / L⌉).toNat : ℝ) =
            max ((⌊(x + w) / L⌋ + 1 - ⌈x / L⌉ : ℤ) : ℝ) 0 := by
          rw [← Int.cast_natCast, Int.toNat_eq_max]; push_cast; rfl
        rw [h1]
        refine max_le ?_ (by positivity)
        push_cast
        have h2 := Int.floor_le ((x + w) / L)
        have h3 := Int.le_ceil (x / L)
        have h4 : (x + w) / L - x / L = w / L := by ring
        linarith

/-! ### Affine change of variables -/

theorem lintegral_comp_affine {β : ℝ} (hβ : β ≠ 0) (c : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ s, f (c + s * β) = ENNReal.ofReal |β|⁻¹ * ∫⁻ t, f t := by
  have hmap : Measure.map (fun s => c + s * β) volume = ENNReal.ofReal |β⁻¹| • volume := by
    have h1 : (fun s : ℝ => c + s * β) = (fun t => c + t) ∘ (fun s => s * β) := rfl
    rw [h1, ← Measure.map_map (measurable_const_add c) (measurable_mul_const β),
      Real.map_volume_mul_right hβ, Measure.map_smul, map_add_left_eq_self]
    exact (measurable_const_add c).aemeasurable
  rw [← lintegral_map hf (by fun_prop), hmap, lintegral_smul_measure, abs_inv, smul_eq_mul]

/-! ### The one-dimensional integral of the block majorant -/

/-- `min(A, ω(|t| - ρ)) ≤ A 1_{|t| ≤ ρ} + √A ((1+|t-ρ|)^{-2} + (1+|t+ρ|)^{-2})` for `N ≥ 4`. -/
theorem min_decayW_le {N : ℕ} (hN : 4 ≤ N) {A ρ : ℝ} (hA : 0 ≤ A) (t : ℝ) :
    min A (decayW N (|t| - ρ)) ≤ (Icc (-ρ) ρ).indicator (fun _ => A) t +
      Real.sqrt A * (((1 + |t - ρ|) ^ 2)⁻¹ + ((1 + |t + ρ|) ^ 2)⁻¹) := by
  have hB : 0 ≤ Real.sqrt A * (((1 + |t - ρ|) ^ 2)⁻¹ + ((1 + |t + ρ|) ^ 2)⁻¹) := by positivity
  by_cases ht : |t| ≤ ρ
  · rw [Set.indicator_of_mem (show t ∈ Icc (-ρ) ρ from abs_le.1 ht)]
    exact (min_le_left _ _).trans (le_add_of_nonneg_right hB)
  · have ht' : ρ < |t| := not_le.1 ht
    have hI : (Icc (-ρ) ρ).indicator (fun _ => A) t = 0 :=
      Set.indicator_of_notMem (show t ∉ Icc (-ρ) ρ from fun h => ht (abs_le.2 h)) _
    rw [hI, zero_add]
    set u := |t| - ρ
    have hu : 0 < u := by simp only [u]; linarith
    have hw : decayW N u = ((1 + u) ^ N)⁻¹ := by rw [decayW, max_eq_left hu.le]
    -- `min ≤ √A √ω` and `√ω ≤ (1+u)^{-2}`
    have hm : min A (decayW N u) ≤ Real.sqrt A * Real.sqrt (decayW N u) := by
      rw [← Real.sqrt_mul hA]
      refine Real.le_sqrt_of_sq_le ?_
      have h1 := min_le_left A (decayW N u)
      have h2 := min_le_right A (decayW N u)
      have h0 : 0 ≤ min A (decayW N u) := le_min hA (decayW_nonneg _ _)
      nlinarith
    have hs : Real.sqrt (decayW N u) ≤ ((1 + u) ^ 2)⁻¹ := by
      rw [hw, Real.sqrt_le_left (by positivity), inv_pow, ← pow_mul]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by omega))
    have hu2 : ((1 + u) ^ 2)⁻¹ ≤ ((1 + |t - ρ|) ^ 2)⁻¹ + ((1 + |t + ρ|) ^ 2)⁻¹ := by
      rcases le_or_gt 0 t with h | h
      · have : u = |t - ρ| := by
          simp only [u]; rw [abs_of_nonneg h, abs_of_nonneg (by rw [abs_of_nonneg h] at ht'; linarith)]
        rw [this]; exact le_add_of_nonneg_right (by positivity)
      · have : u = |t + ρ| := by
          simp only [u]; rw [abs_of_neg h, abs_of_nonpos (by rw [abs_of_neg h] at ht'; linarith)]
          ring
        rw [this]; exact le_add_of_nonneg_left (by positivity)
    exact hm.trans (mul_le_mul_of_nonneg_left (hs.trans hu2) (Real.sqrt_nonneg _))

theorem lintegral_min_decayW_le {N : ℕ} (hN : 4 ≤ N) {A ρ : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ) :
    ∫⁻ t, ENNReal.ofReal (min A (decayW N (|t| - ρ))) ≤
      ENNReal.ofReal (2 * ρ * A + 2 * sInt 2 * Real.sqrt A) := by
  have hint2 := integrable_inv_one_add_abs_pow (d := 2) le_rfl
  have hg : Integrable (fun t : ℝ => (Icc (-ρ) ρ).indicator (fun _ => A) t +
      Real.sqrt A * (((1 + |t - ρ|) ^ 2)⁻¹ + ((1 + |t + ρ|) ^ 2)⁻¹)) := by
    refine ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc).add ?_
    refine Integrable.const_mul ?_ _
    exact (hint2.comp_sub_right ρ).add (hint2.comp_add_right ρ)
  calc ∫⁻ t, ENNReal.ofReal (min A (decayW N (|t| - ρ)))
      ≤ ∫⁻ t, ENNReal.ofReal ((Icc (-ρ) ρ).indicator (fun _ => A) t +
          Real.sqrt A * (((1 + |t - ρ|) ^ 2)⁻¹ + ((1 + |t + ρ|) ^ 2)⁻¹)) :=
        lintegral_mono fun t => ENNReal.ofReal_le_ofReal (min_decayW_le hN hA t)
    _ = ENNReal.ofReal (∫ t, (Icc (-ρ) ρ).indicator (fun _ => A) t +
          Real.sqrt A * (((1 + |t - ρ|) ^ 2)⁻¹ + ((1 + |t + ρ|) ^ 2)⁻¹)) :=
        (ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall fun t => by
          have : 0 ≤ (Icc (-ρ) ρ).indicator (fun _ => A) t :=
            Set.indicator_nonneg (fun _ _ => hA) _
          positivity)).symm
    _ = ENNReal.ofReal (2 * ρ * A + 2 * sInt 2 * Real.sqrt A) := by
        congr 1
        have i1 : Integrable (fun t : ℝ => (Icc (-ρ) ρ).indicator (fun _ => A) t) :=
          (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
        have i2 : Integrable (fun t : ℝ => ((1 + |t - ρ|) ^ 2)⁻¹) := hint2.comp_sub_right ρ
        have i3 : Integrable (fun t : ℝ => ((1 + |t + ρ|) ^ 2)⁻¹) := hint2.comp_add_right ρ
        have e1 := integral_add (f := fun t : ℝ => (Icc (-ρ) ρ).indicator (fun _ => A) t)
          (g := fun t : ℝ => Real.sqrt A * (((1 + |t - ρ|) ^ 2)⁻¹ + ((1 + |t + ρ|) ^ 2)⁻¹))
          i1 ((i2.add i3).const_mul _)
        have e2 := integral_add i2 i3
        have e3 : ∫ t : ℝ, ((1 + |t - ρ|) ^ 2)⁻¹ = sInt 2 :=
          integral_sub_right_eq_self (fun t : ℝ => ((1 + |t|) ^ 2)⁻¹) ρ
        have e4 : ∫ t : ℝ, ((1 + |t + ρ|) ^ 2)⁻¹ = sInt 2 :=
          integral_add_right_eq_self (fun t : ℝ => ((1 + |t|) ^ 2)⁻¹) ρ
        have e5 : ∫ t : ℝ, (Icc (-ρ) ρ).indicator (fun _ => A) t = 2 * ρ * A := by
          rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
          ring
        rw [e1, integral_const_mul, e2, e3, e4, e5]
        ring

/-! ### One interval -/

/-- On an interval of length `ℓ`, `∫ ∑_m f(Lm + c + sβ) ds ≤ |β|^{-1} (ℓ|β|/L + 1) ∫ f`. -/
theorem lintegral_interval_tsum_le {L β : ℝ} (hL : 0 < L) (hβ : β ≠ 0) (c p ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ s, (Icc p (p + ℓ)).indicator (fun s => ∑' m : ℤ, f (L * m + c + s * β)) s ≤
      ENNReal.ofReal |β|⁻¹ * ENNReal.ofReal (ℓ * |β| / L + 1) * ∫⁻ t, f t := by
  set I := Icc p (p + ℓ)
  have hI : MeasurableSet I := measurableSet_Icc
  have h1 : ∀ s, I.indicator (fun s => ∑' m : ℤ, f (L * m + c + s * β)) s =
      ∑' m : ℤ, I.indicator (fun s => f (L * m + c + s * β)) s := fun s => by
    by_cases hs : s ∈ I
    · simp only [Set.indicator_of_mem hs]
    · simp only [Set.indicator_of_notMem hs, tsum_zero]
  have hmeas : ∀ m : ℤ, Measurable (fun s => I.indicator (fun s => f (L * m + c + s * β)) s) :=
    fun m => (hf.comp (by fun_prop)).indicator hI
  -- the integrand after the change of variables
  set G : ℤ → ℝ → ℝ≥0∞ := fun m t => I.indicator (fun _ => (1 : ℝ≥0∞)) ((t - (L * m + c)) / β) *
    f t
  have hGm : ∀ m, Measurable (G m) := fun m =>
    ((measurable_const.indicator hI).comp (by fun_prop)).mul hf
  have h2 : ∀ m : ℤ, ∫⁻ s, I.indicator (fun s => f (L * m + c + s * β)) s =
      ENNReal.ofReal |β|⁻¹ * ∫⁻ t, G m t := fun m => by
    rw [← lintegral_comp_affine hβ (L * m + c) (hGm m)]
    refine lintegral_congr fun s => ?_
    simp only [G]
    have : (L * m + c + s * β - (L * m + c)) / β = s := by field_simp; ring
    rw [this]
    by_cases hs : s ∈ I
    · simp only [Set.indicator_of_mem hs, one_mul]
    · simp only [Set.indicator_of_notMem hs, zero_mul]
  -- counting
  have hcount : ∀ t, ∑' m : ℤ, I.indicator (fun _ => (1 : ℝ≥0∞)) ((t - (L * m + c)) / β) ≤
      ENNReal.ofReal (ℓ * |β| / L + 1) := fun t => by
    set x := t - c - max (β * p) (β * (p + ℓ))
    refine le_trans (ENNReal.tsum_le_tsum fun m => ?_)
      (tsum_indicator_Icc_le hL x (ℓ * |β|) (by positivity))
    by_cases hm : (t - (L * m + c)) / β ∈ I
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem]
      set u := (t - (L * m + c)) / β
      have hu : L * m = t - c - β * u := by simp only [u]; field_simp; ring
      rcases lt_or_gt_of_ne hβ with hneg | hpos
      · have e1 : max (β * p) (β * (p + ℓ)) = β * p := max_eq_left (by nlinarith)
        simp only [x, e1, abs_of_neg hneg]
        constructor <;> nlinarith [hm.1, hm.2]
      · have e1 : max (β * p) (β * (p + ℓ)) = β * (p + ℓ) := max_eq_right (by nlinarith)
        simp only [x, e1, abs_of_pos hpos]
        constructor <;> nlinarith [hm.1, hm.2]
    · rw [Set.indicator_of_notMem hm]; exact bot_le
  calc ∫⁻ s, I.indicator (fun s => ∑' m : ℤ, f (L * m + c + s * β)) s
      = ∑' m : ℤ, ∫⁻ s, I.indicator (fun s => f (L * m + c + s * β)) s := by
        simp_rw [h1]; exact lintegral_tsum fun m => (hmeas m).aemeasurable
    _ = ∑' m : ℤ, ENNReal.ofReal |β|⁻¹ * ∫⁻ t, G m t := by simp_rw [h2]
    _ = ENNReal.ofReal |β|⁻¹ * ∫⁻ t, ∑' m : ℤ, G m t := by
        rw [ENNReal.tsum_mul_left, lintegral_tsum fun m => (hGm m).aemeasurable]
    _ = ENNReal.ofReal |β|⁻¹ * ∫⁻ t, (∑' m : ℤ,
          I.indicator (fun _ => (1 : ℝ≥0∞)) ((t - (L * m + c)) / β)) * f t := by
        simp only [G, ENNReal.tsum_mul_right]
    _ ≤ ENNReal.ofReal |β|⁻¹ * ∫⁻ t, ENNReal.ofReal (ℓ * |β| / L + 1) * f t := by
        gcongr with t
        exact hcount t
    _ = _ := by rw [lintegral_const_mul _ hf, mul_assoc]

/-! ### Dyadic assembly -/

/-- The dyadic blocks `2^j ≤ 1 + |s| < 2^{j+1}`. -/
@[expose] def dyBlock (j : ℕ) : Set ℝ := {s | (2 : ℝ) ^ j ≤ 1 + |s| ∧ 1 + |s| < 2 ^ (j + 1)}

theorem measurableSet_dyBlock (j : ℕ) : MeasurableSet (dyBlock j) := by
  have hm : Measurable fun s : ℝ => 1 + |s| := by fun_prop
  exact (measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)

theorem exists_mem_dyBlock (s : ℝ) : ∃ j, s ∈ dyBlock j := by
  set n := ⌊1 + |s|⌋₊
  have hn : 1 ≤ n := Nat.le_floor (by simp)
  refine ⟨Nat.log 2 n, ?_, ?_⟩
  · calc (2 : ℝ) ^ Nat.log 2 n = ((2 ^ Nat.log 2 n : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (n : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      _ ≤ 1 + |s| := Nat.floor_le (by positivity)
  · calc 1 + |s| < (n : ℝ) + 1 := Nat.lt_floor_add_one _
      _ ≤ ((2 ^ (Nat.log 2 n + 1) : ℕ) : ℝ) := by
          exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) n
      _ = 2 ^ (Nat.log 2 n + 1) := by push_cast; ring

theorem dyBlock_subset (j : ℕ) :
    dyBlock j ⊆ Icc (2 ^ j - 1) (2 ^ j - 1 + 2 ^ j) ∪
      Icc (-(2 ^ (j + 1) - 1)) (-(2 ^ (j + 1) - 1) + 2 ^ j) := by
  intro s hs
  obtain ⟨h1, h2⟩ := hs
  have hp : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
  rcases le_or_gt 0 s with h | h
  · left; rw [abs_of_nonneg h] at h1 h2; constructor <;> linarith
  · right; rw [abs_of_neg h] at h1 h2; constructor <;> linarith

/-- The constant of the near estimate. -/
@[expose] def nearConst (d : ℕ) : ℝ := 16 * (1 + 8 * Real.sqrt d) * (Real.sqrt d + sInt 2)

theorem nearConst_nonneg (d : ℕ) : 0 ≤ nearConst d := by
  unfold nearConst; have := sInt_nonneg 2; positivity

theorem continuous_decayW (N : ℕ) : Continuous (decayW N) := by
  unfold decayW
  exact Continuous.inv₀ (by fun_prop) (fun r => by positivity)

theorem two_pow_sq_mul_le (hd : 3 ≤ d) (j : ℕ) :
    (2 : ℝ) ^ (2 * j) * (((2 : ℝ) ^ j) ^ d)⁻¹ ≤ (1 / 2) ^ j := by
  have h1 : ((2 : ℝ) ^ j) ^ 3 ≤ ((2 : ℝ) ^ j) ^ d :=
    pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hd
  calc (2 : ℝ) ^ (2 * j) * (((2 : ℝ) ^ j) ^ d)⁻¹ ≤ (2 : ℝ) ^ (2 * j) * (((2 : ℝ) ^ j) ^ 3)⁻¹ := by
        gcongr
    _ = (1 / 2) ^ j := by
        rw [div_pow, one_pow, pow_mul]
        field_simp
        rw [← pow_mul, ← pow_mul, mul_comm]

theorem two_pow_mul_sqrt_le (hd : 3 ≤ d) (j : ℕ) :
    (2 : ℝ) ^ j * Real.sqrt ((((2 : ℝ) ^ j) ^ d)⁻¹) ≤ (3 / 4) ^ j := by
  have h0 : 0 ≤ (2 : ℝ) ^ j * Real.sqrt ((((2 : ℝ) ^ j) ^ d)⁻¹) := by positivity
  refine (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).1 ?_
  have h1 : ((2 : ℝ) ^ j) ^ 3 ≤ ((2 : ℝ) ^ j) ^ d :=
    pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hd
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  calc ((2 : ℝ) ^ j) ^ 2 * (((2 : ℝ) ^ j) ^ d)⁻¹ ≤ ((2 : ℝ) ^ j) ^ 2 * (((2 : ℝ) ^ j) ^ 3)⁻¹ := by
        gcongr
    _ = (1 / 2) ^ j := by
        rw [div_pow, one_pow]
        field_simp
    _ ≤ (9 / 16) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
    _ = ((3 / 4) ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- **The weighted near-term measure estimate.** -/
theorem lintegral_near_le (hd : 3 ≤ d) {N : ℕ} (hN : 4 ≤ N) {L lam β : ℝ} (hL : 0 < L)
    (hlam : 0 ≤ lam) (hβ : β ≠ 0) (c : ℝ) :
    ∫⁻ s, {s : ℝ | L / (4 * Real.sqrt d * |β|) < |s|}.indicator (fun s => ∑' m : ℤ,
      ENNReal.ofReal (min (((1 + |s|) ^ d)⁻¹)
        (decayW N (|L * m + c + s * β| - |s| * (lam * Real.sqrt d))))) s ≤
      ENNReal.ofReal (nearConst d * (lam + 1) / L) := by
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < d))
  have hβ0 : 0 < |β| := abs_pos.2 hβ
  set A := {s : ℝ | L / (4 * Real.sqrt d * |β|) < |s|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (by fun_prop)
  set F : ℝ → ℝ≥0∞ := fun s => ∑' m : ℤ, ENNReal.ofReal (min (((1 + |s|) ^ d)⁻¹)
    (decayW N (|L * m + c + s * β| - |s| * (lam * Real.sqrt d))))
  have hFm : Measurable F := by
    refine Measurable.tsum fun m => ENNReal.measurable_ofReal.comp ?_
    exact (Continuous.min (Continuous.inv₀ (by fun_prop) (fun s => by positivity))
      ((continuous_decayW N).comp (by fun_prop))).measurable
  -- the block majorants
  set Aj : ℕ → ℝ := fun j => (((2 : ℝ) ^ j) ^ d)⁻¹
  set ρj : ℕ → ℝ := fun j => 2 ^ (j + 1) * (lam * Real.sqrt d)
  set fj : ℕ → ℝ → ℝ := fun j t => min (Aj j) (decayW N (|t| - ρj j))
  set Bj : ℕ → ℝ := fun j => 2 * ((2 ^ j / L + 8 * Real.sqrt d * 2 ^ j / L) *
    (2 * ρj j * Aj j + 2 * sInt 2 * Real.sqrt (Aj j)))
  have hs2 := sInt_nonneg 2
  have hBj0 : ∀ j, 0 ≤ Bj j := fun j => by positivity
  have hblock : ∀ j, ∫⁻ s, (dyBlock j).indicator (A.indicator F) s ≤ ENNReal.ofReal (Bj j) := by
    intro j
    by_cases hj : L / (4 * Real.sqrt d * |β|) < 2 ^ (j + 1)
    · set G : ℝ → ℝ≥0∞ := fun s => ∑' m : ℤ, ENNReal.ofReal (fj j (L * m + c + s * β))
      have hfjm : Measurable (fun t => ENNReal.ofReal (fj j t)) :=
        ENNReal.measurable_ofReal.comp
          (Continuous.min continuous_const ((continuous_decayW N).comp (by fun_prop))).measurable
      set Ip := Icc ((2 : ℝ) ^ j - 1) (2 ^ j - 1 + 2 ^ j)
      set Im := Icc (-((2 : ℝ) ^ (j + 1) - 1)) (-(2 ^ (j + 1) - 1) + 2 ^ j)
      have hpt : ∀ s, (dyBlock j).indicator (A.indicator F) s ≤ Ip.indicator G s +
          Im.indicator G s := fun s => by
        by_cases hs : s ∈ dyBlock j
        · rw [Set.indicator_of_mem hs]
          have hFG : A.indicator F s ≤ G s := by
            refine (Set.indicator_le_self _ _ s).trans (ENNReal.tsum_le_tsum fun m => ?_)
            refine ENNReal.ofReal_le_ofReal (min_le_min ?_ (decayW_anti N ?_))
            · exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hs.1 d)
            · have : |s| * (lam * Real.sqrt d) ≤ ρj j :=
                mul_le_mul_of_nonneg_right (by linarith [hs.2]) (by positivity)
              linarith
          rcases dyBlock_subset j hs with h | h
          · rw [Set.indicator_of_mem h]; exact hFG.trans le_self_add
          · rw [Set.indicator_of_mem h]; exact hFG.trans le_add_self
        · rw [Set.indicator_of_notMem hs]; exact bot_le
      have hGm : Measurable G := Measurable.tsum fun m => hfjm.comp (by fun_prop)
      have hint := lintegral_min_decayW_le (A := Aj j) (ρ := ρj j) hN (by positivity)
        (by positivity)
      have hI : ∀ p : ℝ, ∫⁻ s, (Icc p (p + 2 ^ j)).indicator G s ≤
          ENNReal.ofReal (|β|⁻¹ * (2 ^ j * |β| / L + 1) *
            (2 * ρj j * Aj j + 2 * sInt 2 * Real.sqrt (Aj j))) := fun p => by
        refine (lintegral_interval_tsum_le hL hβ c p (2 ^ j) (by positivity) hfjm).trans ?_
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        gcongr
      have hbeta : |β|⁻¹ * (2 ^ j * |β| / L + 1) ≤ 2 ^ j / L + 8 * Real.sqrt d * 2 ^ j / L := by
        have h1 : |β|⁻¹ * (2 ^ j * |β| / L + 1) = 2 ^ j / L + |β|⁻¹ := by
          field_simp
        rw [h1]
        have h2 : |β|⁻¹ ≤ 8 * Real.sqrt d * 2 ^ j / L := by
          rw [div_lt_iff₀ (by positivity)] at hj
          rw [le_div_iff₀ hL, inv_mul_le_iff₀ hβ0]
          have : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
          calc L ≤ 2 ^ (j + 1) * (4 * Real.sqrt d * |β|) := hj.le
            _ = |β| * (8 * Real.sqrt d * 2 ^ j) := by rw [this]; ring
        linarith
      calc ∫⁻ s, (dyBlock j).indicator (A.indicator F) s
          ≤ ∫⁻ s, (Ip.indicator G s + Im.indicator G s) := lintegral_mono hpt
        _ = (∫⁻ s, Ip.indicator G s) + ∫⁻ s, Im.indicator G s :=
            lintegral_add_left (f := Ip.indicator G) (hGm.indicator measurableSet_Icc) _
        _ ≤ ENNReal.ofReal (|β|⁻¹ * (2 ^ j * |β| / L + 1) *
              (2 * ρj j * Aj j + 2 * sInt 2 * Real.sqrt (Aj j))) +
            ENNReal.ofReal (|β|⁻¹ * (2 ^ j * |β| / L + 1) *
              (2 * ρj j * Aj j + 2 * sInt 2 * Real.sqrt (Aj j))) := by
            exact add_le_add (hI ((2 : ℝ) ^ j - 1)) (hI (-((2 : ℝ) ^ (j + 1) - 1)))
        _ ≤ ENNReal.ofReal (Bj j) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            simp only [Bj]
            have hX : 0 ≤ 2 * ρj j * Aj j + 2 * sInt 2 * Real.sqrt (Aj j) := by positivity
            nlinarith [mul_le_mul_of_nonneg_right hbeta hX]
    · have hzero : ∀ s, (dyBlock j).indicator (A.indicator F) s = 0 := fun s => by
        by_cases hs : s ∈ dyBlock j
        · rw [Set.indicator_of_mem hs, Set.indicator_of_notMem]
          intro hsA
          apply hj
          have : (A : Set ℝ) s := hsA
          simp only [A, Set.mem_ofPred_eq] at hsA
          linarith [hs.2]
        · rw [Set.indicator_of_notMem hs]
      simp only [hzero, lintegral_zero]
      exact bot_le
  -- covering by the blocks
  have hcover : ∀ s, A.indicator F s ≤ ∑' j : ℕ, (dyBlock j).indicator (A.indicator F) s :=
    fun s => by
    obtain ⟨j, hj⟩ := exists_mem_dyBlock s
    calc A.indicator F s = (dyBlock j).indicator (A.indicator F) s := by
          rw [Set.indicator_of_mem hj]
      _ ≤ ∑' j : ℕ, (dyBlock j).indicator (A.indicator F) s :=
          ENNReal.le_tsum (f := fun j => (dyBlock j).indicator (A.indicator F) s) j
  -- summation
  set K₁ := 2 * (1 + 8 * Real.sqrt d) / L * (4 * lam * Real.sqrt d)
  set K₂ := 2 * (1 + 8 * Real.sqrt d) / L * (2 * sInt 2)
  have hK₁ : 0 ≤ K₁ := by positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  have hBy : ∀ j, Bj j ≤ K₁ * (1 / 2) ^ j + K₂ * (3 / 4) ^ j := fun j => by
    have h1 := two_pow_sq_mul_le hd j
    have h2 := two_pow_mul_sqrt_le hd j
    have hρ : ρj j = 2 * 2 ^ j * (lam * Real.sqrt d) := by simp only [ρj]; ring
    calc Bj j = 2 * (1 + 8 * Real.sqrt d) / L * (4 * lam * Real.sqrt d *
          (2 ^ (2 * j) * Aj j) + 2 * sInt 2 * (2 ^ j * Real.sqrt (Aj j))) := by
          simp only [Bj, hρ]
          rw [show (2 : ℝ) ^ (2 * j) = 2 ^ j * 2 ^ j by rw [two_mul, pow_add]]
          field_simp
          ring
      _ ≤ 2 * (1 + 8 * Real.sqrt d) / L * (4 * lam * Real.sqrt d * (1 / 2) ^ j +
          2 * sInt 2 * (3 / 4) ^ j) := by gcongr
      _ = K₁ * (1 / 2) ^ j + K₂ * (3 / 4) ^ j := by ring
  have hsum1 : Summable fun j : ℕ => ((1 : ℝ) / 2) ^ j :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum2 : Summable fun j : ℕ => ((3 : ℝ) / 4) ^ j :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hy : Summable fun j : ℕ => K₁ * (1 / 2) ^ j + K₂ * (3 / 4) ^ j :=
    (hsum1.mul_left K₁).add (hsum2.mul_left K₂)
  have hyv : ∑' j : ℕ, (K₁ * (1 / 2) ^ j + K₂ * (3 / 4) ^ j) = 2 * K₁ + 4 * K₂ := by
    rw [hsum1.mul_left K₁ |>.tsum_add (hsum2.mul_left K₂), tsum_mul_left, tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num) (by norm_num),
      tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
    ring
  calc ∫⁻ s, A.indicator F s ≤ ∫⁻ s, ∑' j : ℕ, (dyBlock j).indicator (A.indicator F) s :=
        lintegral_mono hcover
    _ = ∑' j : ℕ, ∫⁻ s, (dyBlock j).indicator (A.indicator F) s :=
        lintegral_tsum fun j => ((hFm.indicator hA).indicator (measurableSet_dyBlock j)).aemeasurable
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (K₁ * (1 / 2) ^ j + K₂ * (3 / 4) ^ j) :=
        ENNReal.tsum_le_tsum fun j => (hblock j).trans (ENNReal.ofReal_le_ofReal (hBy j))
    _ = ENNReal.ofReal (2 * K₁ + 4 * K₂) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hy, hyv]
    _ ≤ ENNReal.ofReal (nearConst d * (lam + 1) / L) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e : 2 * K₁ + 4 * K₂ =
            16 * (1 + 8 * Real.sqrt d) * (lam * Real.sqrt d + sInt 2) / L := by
          simp only [K₁, K₂]; ring
        rw [e, nearConst]
        refine div_le_div_of_nonneg_right ?_ hL.le
        rw [mul_assoc (16 * (1 + 8 * Real.sqrt d))]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [Real.sqrt_nonneg d]

end WaveTurbulence.NTSP
