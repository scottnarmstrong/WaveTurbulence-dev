/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3SupProb

/-!
# X3 TimeSup: the supremum in `t` with a scale (T (sobolev2), L2330)

Let `q > 1`, `0 < h`, `J ≥ 1` with `(J+1) h ≥ 1`, and grid times `g_j(s) = s + (j+1)(a+1−s)/(J+1)`,
`j < J`, all in `(s, a+1)`. Let `K, K' : ℝ → ℝ → ℂ` satisfy the FTC
`K(t,s) = K(t₀,s) + ∫_{t₀}^t K'(u,s) du` for `a < s < t₀, t ≤ a+1`, with `K'(·, s)` measurable.

**Statement 1** (`timeSup_le`, deterministic). For `t ∈ [a, a+1]`:

`∫⁻_{(a,t)} ‖K(t,s)‖ ds ≤ Φ_h := ∫⁻_{(a,a+1)} (∑_{j<J} ‖K(g_j(s), s)‖ + h^{1−1/q} (∫⁻_{(s,a+1)} ‖K'(u,s)‖^q du)^{1/q}) ds`.

**Statement 2** (`timeSup_moment`, moments). For random `K_ω`, `K'_ω`, jointly measurable, with
`𝔼_F ‖K_ω(t,s)‖^q ≤ C` and `𝔼_F ‖K'_ω(u,s)‖^q ≤ C'` on the open triangle:

`𝔼_F Φ_h^q ≤ 2^{q−1} (J^q C + h^{q−1} C')`.

(This replaces T's (sobolev2), Gagliardo–Nirenberg in `(t,s)`, by a grid in `t` and Hölder on windows of
length `h`. Only `∂_t` is used. With `h = M₂^{-1/50}`, the derivative term carries `M₂^{-(q−1)/50}`, which
makes up for the missing `M₂` gain of the `dRoot` moments.)
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open MeasureTheory Set
open scoped ENNReal Interval

/-! ## Hölder with the volume -/

/-- `∫⁻ g ≤ ν(univ)^{1−1/q} (∫⁻ g^q)^{1/q}` for `q > 1`. -/
theorem lintegral_le_measure_rpow_mul {α : Type*} [MeasurableSpace α] (ν : Measure α) {q : ℝ} (hq : 1 < q)
    {g : α → ℝ≥0∞} (hg : AEMeasurable g ν) :
    ∫⁻ x, g x ∂ν ≤ ν univ ^ (1 - 1 / q) * (∫⁻ x, g x ^ q ∂ν) ^ (1 / q) := by
  set p' : ℝ := q / (q - 1)
  have hpq : p'.HolderConjugate q := (Real.HolderConjugate.conjExponent hq).symm
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq aemeasurable_const hg (f := fun _ => (1 : ℝ≥0∞))
  have hp'0 : 0 < p' := hpq.pos
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have he : 1 / p' = 1 - 1 / q := by
    have := hpq.inv_add_inv_eq_one
    rw [one_div, one_div]
    linarith
  rwa [he] at h

/-- Jensen for `ν(univ) ≤ 1`: `(∫⁻ g)^q ≤ ∫⁻ g^q`. -/
theorem lintegral_rpow_le {α : Type*} [MeasurableSpace α] (ν : Measure α) (hν : ν univ ≤ 1) {q : ℝ} (hq : 1 < q)
    {g : α → ℝ≥0∞} (hg : AEMeasurable g ν) : (∫⁻ x, g x ∂ν) ^ q ≤ ∫⁻ x, g x ^ q ∂ν := by
  have hq0 : 0 < q := by linarith
  have h := lintegral_le_measure_rpow_mul ν hq hg
  have h1 : ν univ ^ (1 - 1 / q) ≤ 1 := ENNReal.rpow_le_one hν (by
    rw [sub_nonneg, div_le_one hq0]; exact hq.le)
  have h2 : ∫⁻ x, g x ∂ν ≤ (∫⁻ x, g x ^ q ∂ν) ^ (1 / q) :=
    h.trans (by calc ν univ ^ (1 - 1 / q) * (∫⁻ x, g x ^ q ∂ν) ^ (1 / q)
        ≤ 1 * (∫⁻ x, g x ^ q ∂ν) ^ (1 / q) := by gcongr
      _ = _ := one_mul _)
  calc (∫⁻ x, g x ∂ν) ^ q ≤ ((∫⁻ x, g x ^ q ∂ν) ^ (1 / q)) ^ q := ENNReal.rpow_le_rpow h2 hq0.le
    _ = ∫⁻ x, g x ^ q ∂ν := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]

/-! ## The grid -/

/-- The grid times `g_j(s) = s + (j+1)(a+1−s)/(J+1)`. -/
noncomputable def gridT (a : ℝ) (J : ℕ) (j : Fin J) (s : ℝ) : ℝ := s + (j + 1 : ℝ) * ((a + 1 - s) / (J + 1))

theorem gridT_mem {a : ℝ} {J : ℕ} (j : Fin J) {s : ℝ} (hs : s < a + 1) : gridT a J j s ∈ Ioo s (a + 1) := by
  unfold gridT
  have hΔ : 0 < (a + 1 - s) / (J + 1) := div_pos (by linarith) (by positivity)
  have hj : (j : ℝ) + 1 ≤ J := by exact_mod_cast j.2
  constructor
  · nlinarith [hΔ]
  · have : ((j : ℝ) + 1) * ((a + 1 - s) / (J + 1)) < a + 1 - s := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith

/-- **A grid time within `Δ = (a+1−s)/(J+1)` of `t`.** -/
theorem exists_gridT_near {a : ℝ} {J : ℕ} (hJ : 1 ≤ J) {s t : ℝ} (hst : s < t) (hta : t ≤ a + 1) :
    ∃ j : Fin J, |t - gridT a J j s| ≤ (a + 1 - s) / (J + 1) := by
  set Δ := (a + 1 - s) / (J + 1) with hΔdef
  have hΔ : 0 < Δ := div_pos (by linarith) (by positivity)
  set m := ⌈(t - s) / Δ⌉₊ with hm
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (by
    rw [hm, Ne, Nat.ceil_eq_zero, not_le]; exact div_pos (by linarith) hΔ)
  have hmJ : m ≤ J + 1 := by
    rw [hm, Nat.ceil_le]
    rw [div_le_iff₀ hΔ, hΔdef, mul_div_assoc', le_div_iff₀ (by positivity)]
    push_cast
    nlinarith
  have hceil1 : (t - s) / Δ ≤ m := Nat.le_ceil _
  have hceil2 : (m : ℝ) - 1 < (t - s) / Δ := by
    have := Nat.ceil_lt_add_one (div_pos (by linarith : (0 : ℝ) < t - s) hΔ).le
    rw [← hm] at this
    linarith
  rw [div_le_iff₀ hΔ] at hceil1
  rw [lt_div_iff₀ hΔ] at hceil2
  by_cases hmJ' : m ≤ J
  · refine ⟨⟨m - 1, by omega⟩, ?_⟩
    unfold gridT
    have : ((m - 1 : ℕ) : ℝ) + 1 = m := by push_cast [Nat.cast_sub hm1]; ring
    simp only [this]
    rw [← hΔdef, abs_le]
    constructor <;> nlinarith
  · have hmeq : m = J + 1 := by omega
    refine ⟨⟨J - 1, by omega⟩, ?_⟩
    unfold gridT
    have : ((J - 1 : ℕ) : ℝ) + 1 = J := by push_cast [Nat.cast_sub hJ]; ring
    simp only [this]
    rw [← hΔdef, abs_le]
    rw [hmeq] at hceil2
    push_cast at hceil2
    have hΔJ : ((J : ℝ) + 1) * Δ = a + 1 - s := by
      rw [hΔdef]; field_simp
    constructor <;> nlinarith

/-! ## The deterministic bound -/

theorem enorm_intervalIntegral_le (f : ℝ → ℂ) (x y : ℝ) : ‖∫ u in x..y, f u‖ₑ ≤ ∫⁻ u in Ι x y, ‖f u‖ₑ := by
  rcases le_total x y with h | h
  · rw [intervalIntegral.integral_of_le h, uIoc_of_le h]
    exact enorm_integral_le_lintegral_enorm _
  · rw [intervalIntegral.integral_of_ge h, uIoc_of_ge h, enorm_neg]
    exact enorm_integral_le_lintegral_enorm _

section Det

variable {a h q : ℝ} {J : ℕ} (hJ : 1 ≤ J) (hh : 0 < h) (hJh : 1 ≤ ((J : ℝ) + 1) * h) (hq : 1 < q)
  {K K' : ℝ → ℝ → ℂ}
  (hFTC : ∀ s ∈ Ioo a (a + 1), ∀ t₀ ∈ Ioc s (a + 1), ∀ t ∈ Ioc s (a + 1),
    K t s = K t₀ s + ∫ u in t₀..t, K' u s)
  (hK'm : ∀ s, Measurable fun u => K' u s)

/-- The integrand of `Φ_h`. -/
noncomputable def timeSupIntegrand (a h q : ℝ) (J : ℕ) (K K' : ℝ → ℝ → ℂ) (s : ℝ) : ℝ≥0∞ :=
  (∑ j : Fin J, ‖K (gridT a J j s) s‖ₑ) +
    ENNReal.ofReal h ^ (1 - 1 / q) * (∫⁻ u in Ioo s (a + 1), ‖K' u s‖ₑ ^ q) ^ (1 / q)

include hJ hJh hq hFTC hK'm in
theorem enorm_le_timeSupIntegrand {s t : ℝ} (hs : s ∈ Ioo a (a + 1)) (hst : s < t) (hta : t ≤ a + 1) :
    ‖K t s‖ₑ ≤ timeSupIntegrand a h q J K K' s := by
  have hq0 : 0 < q := by linarith
  obtain ⟨j, hj⟩ := exists_gridT_near hJ hst hta
  set g := gridT a J j s
  have hg := gridT_mem j hs.2
  rw [hFTC s hs g ⟨hg.1, hg.2.le⟩ t ⟨hst, hta⟩]
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact Finset.single_le_sum (f := fun j => ‖K (gridT a J j s) s‖ₑ) (fun _ _ => zero_le) (Finset.mem_univ j)
  refine (enorm_intervalIntegral_le _ g t).trans ?_
  have hW : Ι g t ⊆ Ioc s (a + 1) := by
    intro u hu
    rw [mem_uIoc] at hu
    rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hg.1.trans h1, h2.trans hta⟩
    · exact ⟨hst.trans h1, h2.trans hg.2.le⟩
  have hΔ : (a + 1 - s) / (J + 1) ≤ h := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hs.1]
  have hvol : volume (Ι g t) ≤ ENNReal.ofReal h := by
    rw [uIoc, Real.volume_Ioc]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [max_sub_min_eq_abs]
    exact hj.trans hΔ
  have hmeas : AEMeasurable (fun u => ‖K' u s‖ₑ) (volume.restrict (Ι g t)) :=
    (hK'm s).enorm.aemeasurable
  calc ∫⁻ u in Ι g t, ‖K' u s‖ₑ
      ≤ (volume.restrict (Ι g t)) univ ^ (1 - 1 / q) * (∫⁻ u in Ι g t, ‖K' u s‖ₑ ^ q) ^ (1 / q) :=
        lintegral_le_measure_rpow_mul _ hq hmeas
    _ ≤ ENNReal.ofReal h ^ (1 - 1 / q) * (∫⁻ u in Ioo s (a + 1), ‖K' u s‖ₑ ^ q) ^ (1 / q) := by
        rw [Measure.restrict_apply_univ]
        have he : 0 ≤ 1 - 1 / q := by rw [sub_nonneg, div_le_one hq0]; exact hq.le
        have hle : (∫⁻ u in Ι g t, ‖K' u s‖ₑ ^ q) ≤ ∫⁻ u in Ioo s (a + 1), ‖K' u s‖ₑ ^ q := by
          rw [setLIntegral_congr Ioo_ae_eq_Ioc]
          exact lintegral_mono_set hW
        exact mul_le_mul' (ENNReal.rpow_le_rpow hvol he) (ENNReal.rpow_le_rpow hle (by positivity))

include hJ hJh hq hFTC hK'm in
/-- **Statement 1: the deterministic bound.** -/
theorem timeSup_le {t : ℝ} (ht : t ∈ Icc a (a + 1)) :
    ∫⁻ s in Ioo a t, ‖K t s‖ₑ ≤ ∫⁻ s in Ioo a (a + 1), timeSupIntegrand a h q J K K' s :=
  calc ∫⁻ s in Ioo a t, ‖K t s‖ₑ ≤ ∫⁻ s in Ioo a t, timeSupIntegrand a h q J K K' s :=
        setLIntegral_mono' measurableSet_Ioo fun _s hs =>
          enorm_le_timeSupIntegrand hJ hJh hq hFTC hK'm ⟨hs.1, hs.2.trans_le ht.2⟩ hs.2 ht.2
    _ ≤ _ := lintegral_mono_set (Ioo_subset_Ioo_right ht.2)

end Det

/-! ## The moments -/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] {F : Set Ω}
  {a h q : ℝ} {J : ℕ} (hq : 1 < q) {K K' : Ω → ℝ → ℝ → ℂ}
  (hKm : Measurable fun z : Ω × ℝ × ℝ => K z.1 z.2.1 z.2.2)
  (hK'm : Measurable fun z : Ω × ℝ × ℝ => K' z.1 z.2.1 z.2.2)

include hK'm in
theorem measurable_timeSupB :
    Measurable fun z : Ω × ℝ => ∫⁻ u in Ioo z.2 (a + 1), ‖K' z.1 u z.2‖ₑ ^ q := by
  have hset : MeasurableSet {w : (Ω × ℝ) × ℝ | w.2 ∈ Ioo w.1.2 (a + 1)} :=
    (measurableSet_lt (measurable_snd.comp measurable_fst) measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const)
  have hf : Measurable fun w : (Ω × ℝ) × ℝ => ‖K' w.1.1 w.2 w.1.2‖ₑ ^ q :=
    (hK'm.comp (measurable_fst.comp measurable_fst |>.prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))).enorm.pow_const q
  have h := (hf.indicator hset).lintegral_prod_right' (ν := (volume : Measure ℝ))
  convert h using 1
  funext z
  rw [← lintegral_indicator measurableSet_Ioo]
  rfl

include hKm in
theorem measurable_timeSupK (j : Fin J) :
    Measurable fun z : Ω × ℝ => ‖K z.1 (gridT a J j z.2) z.2‖ₑ := by
  have hg : Measurable fun s : ℝ => gridT a J j s := by
    unfold gridT; fun_prop
  exact (hKm.comp (measurable_fst.prodMk ((hg.comp measurable_snd).prodMk measurable_snd))).enorm

include hq in
/-- The pointwise power bound `T^q ≤ 2^{q−1}(J^{q−1} ∑_j ‖K(g_j)‖^q + h^{q−1} B)`. -/
theorem timeSupIntegrand_rpow_le (h : ℝ) (Kω K'ω : ℝ → ℝ → ℂ) (s : ℝ) :
    timeSupIntegrand a h q J Kω K'ω s ^ q ≤ 2 ^ (q - 1) * ((J : ℝ≥0∞) ^ (q - 1) *
      (∑ j : Fin J, ‖Kω (gridT a J j s) s‖ₑ ^ q) +
        ENNReal.ofReal h ^ (q - 1) * ∫⁻ u in Ioo s (a + 1), ‖K'ω u s‖ₑ ^ q) := by
  have hq0 : 0 < q := by linarith
  unfold timeSupIntegrand
  refine (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq.le).trans ?_
  gcongr
  · have := ENNReal.rpow_sum_le_const_mul_sum_rpow (s := (Finset.univ : Finset (Fin J)))
      (f := fun j => ‖Kω (gridT a J j s) s‖ₑ) hq.le
    simpa using this
  · rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
    have : (1 - 1 / q) * q = q - 1 := by field_simp
    rw [this]

include hq hKm hK'm in
/-- **Statement 2: the moments of `Φ_h`.** -/
theorem timeSup_moment {C C' : ℝ≥0∞}
    (hC : ∀ s ∈ Ioo a (a + 1), ∀ t ∈ Ioo s (a + 1), ∫⁻ ω in F, ‖K ω t s‖ₑ ^ q ∂μ ≤ C)
    (hC' : ∀ s ∈ Ioo a (a + 1), ∀ u ∈ Ioo s (a + 1), ∫⁻ ω in F, ‖K' ω u s‖ₑ ^ q ∂μ ≤ C') :
    ∫⁻ ω in F, (∫⁻ s in Ioo a (a + 1), timeSupIntegrand a h q J (K ω) (K' ω) s) ^ q ∂μ ≤
      2 ^ (q - 1) * ((J : ℝ≥0∞) ^ q * C + ENNReal.ofReal h ^ (q - 1) * C') := by
  have hq0 : 0 < q := by linarith
  have hB := measurable_timeSupB (a := a) (q := q) hK'm
  have hKj := fun j : Fin J => measurable_timeSupK (a := a) hKm j
  set G : Ω × ℝ → ℝ≥0∞ := fun z => 2 ^ (q - 1) * ((J : ℝ≥0∞) ^ (q - 1) *
      (∑ j : Fin J, ‖K z.1 (gridT a J j z.2) z.2‖ₑ ^ q) +
        ENNReal.ofReal h ^ (q - 1) * ∫⁻ u in Ioo z.2 (a + 1), ‖K' z.1 u z.2‖ₑ ^ q) with hGdef
  have hGm : Measurable G :=
    measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun j _ => (hKj j).pow_const q)).add
      (measurable_const.mul hB))
  have hTm : ∀ ω, Measurable fun s => timeSupIntegrand a h q J (K ω) (K' ω) s := fun ω => by
    unfold timeSupIntegrand
    refine (Finset.measurable_sum _ fun j _ => (hKj j).comp (measurable_const.prodMk measurable_id)).add
      (measurable_const.mul ((hB.comp (measurable_const.prodMk measurable_id)).pow_const _))
  have hvol : (volume.restrict (Ioo a (a + 1))) univ ≤ 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]; simp
  -- the bound of `∫⁻_F G(·, s)` for each `s`
  have hinner : ∀ s ∈ Ioo a (a + 1), ∫⁻ ω in F, G (ω, s) ∂μ ≤
      2 ^ (q - 1) * ((J : ℝ≥0∞) ^ q * C + ENNReal.ofReal h ^ (q - 1) * C') := by
    intro s hs
    have hK1 : ∀ j : Fin J, ∫⁻ ω in F, ‖K ω (gridT a J j s) s‖ₑ ^ q ∂μ ≤ C := fun j =>
      hC s hs _ (gridT_mem j hs.2)
    have hB1 : ∫⁻ ω in F, (∫⁻ u in Ioo s (a + 1), ‖K' ω u s‖ₑ ^ q) ∂μ ≤ C' := by
      have hm2 : Measurable (Function.uncurry fun ω u => ‖K' ω u s‖ₑ ^ q) :=
        (hK'm.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))).enorm.pow_const q
      rw [lintegral_lintegral_swap hm2.aemeasurable]
      calc ∫⁻ u in Ioo s (a + 1), ∫⁻ ω in F, ‖K' ω u s‖ₑ ^ q ∂μ ≤ ∫⁻ _u in Ioo s (a + 1), C' :=
            setLIntegral_mono' measurableSet_Ioo fun u hu => hC' s hs u hu
        _ = C' * volume (Ioo s (a + 1)) := setLIntegral_const _ _
        _ ≤ C' * 1 := by
            gcongr
            rw [Real.volume_Ioo]
            exact ENNReal.ofReal_le_one.2 (by linarith [hs.1])
        _ = C' := mul_one _
    have hmeasω : ∀ j : Fin J, Measurable fun ω => ‖K ω (gridT a J j s) s‖ₑ ^ q := fun j =>
      ((hKj j).comp (measurable_id.prodMk measurable_const)).pow_const q
    have hmeasB : Measurable fun ω => ∫⁻ u in Ioo s (a + 1), ‖K' ω u s‖ₑ ^ q :=
      hB.comp (measurable_id.prodMk measurable_const)
    have hX : Measurable fun ω => ∑ j : Fin J, ‖K ω (gridT a J j s) s‖ₑ ^ q :=
      Finset.measurable_sum _ fun j _ => hmeasω j
    have hY1 : Measurable fun ω => (J : ℝ≥0∞) ^ (q - 1) * ∑ j : Fin J, ‖K ω (gridT a J j s) s‖ₑ ^ q :=
      hX.const_mul _
    have hY2 : Measurable fun ω => ENNReal.ofReal h ^ (q - 1) * ∫⁻ u in Ioo s (a + 1), ‖K' ω u s‖ₑ ^ q :=
      hmeasB.const_mul _
    have hY : Measurable fun ω => (J : ℝ≥0∞) ^ (q - 1) * (∑ j : Fin J, ‖K ω (gridT a J j s) s‖ₑ ^ q) +
        ENNReal.ofReal h ^ (q - 1) * ∫⁻ u in Ioo s (a + 1), ‖K' ω u s‖ₑ ^ q := hY1.add hY2
    show ∫⁻ ω in F, 2 ^ (q - 1) * ((J : ℝ≥0∞) ^ (q - 1) * (∑ j : Fin J, ‖K ω (gridT a J j s) s‖ₑ ^ q) +
        ENNReal.ofReal h ^ (q - 1) * ∫⁻ u in Ioo s (a + 1), ‖K' ω u s‖ₑ ^ q) ∂μ ≤ _
    rw [lintegral_const_mul _ hY, lintegral_add_left hY1, lintegral_const_mul _ hX,
      lintegral_finsetSum _ fun j _ => hmeasω j, lintegral_const_mul _ hmeasB]
    gcongr 2 ^ (q - 1) * (?_ + ENNReal.ofReal h ^ (q - 1) * ?_)
    · calc (J : ℝ≥0∞) ^ (q - 1) * ∑ j : Fin J, ∫⁻ ω in F, ‖K ω (gridT a J j s) s‖ₑ ^ q ∂μ
          ≤ (J : ℝ≥0∞) ^ (q - 1) * ∑ _j : Fin J, C := by gcongr with j; exact hK1 j
        _ = (J : ℝ≥0∞) ^ q * C := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
            congr 1
            by_cases hJ0 : J = 0
            · subst hJ0
              simp [ENNReal.zero_rpow_of_pos hq0]
            · conv_rhs => rw [show q = (q - 1) + 1 by ring]
              rw [ENNReal.rpow_add _ _ (by exact_mod_cast hJ0) (ENNReal.natCast_ne_top J), ENNReal.rpow_one]
  calc ∫⁻ ω in F, (∫⁻ s in Ioo a (a + 1), timeSupIntegrand a h q J (K ω) (K' ω) s) ^ q ∂μ
      ≤ ∫⁻ ω in F, (∫⁻ s in Ioo a (a + 1), G (ω, s)) ∂μ := by
        refine lintegral_mono fun ω => ?_
        refine (lintegral_rpow_le _ hvol hq (hTm ω).aemeasurable).trans ?_
        exact lintegral_mono fun s => timeSupIntegrand_rpow_le hq h (K ω) (K' ω) s
    _ = ∫⁻ s in Ioo a (a + 1), ∫⁻ ω in F, G (ω, s) ∂μ :=
        lintegral_lintegral_swap (f := fun ω s => G (ω, s)) hGm.aemeasurable
    _ ≤ ∫⁻ _s in Ioo a (a + 1), 2 ^ (q - 1) * ((J : ℝ≥0∞) ^ q * C + ENNReal.ofReal h ^ (q - 1) * C') :=
        setLIntegral_mono' measurableSet_Ioo hinner
    _ ≤ 2 ^ (q - 1) * ((J : ℝ≥0∞) ^ q * C + ENNReal.ofReal h ^ (q - 1) * C') := by
        rw [setLIntegral_const, Real.volume_Ioo]
        simp

end Moments

end WaveTurbulence.Fixedpt
