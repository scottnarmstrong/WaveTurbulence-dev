/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.KinkIBP

/-! # PROT-PIN (D3-KINK): the kinked atom `Ψ₀ k_z` is uniformly bounded in `A^θ(ℝ)`, `θ ≤ 1/2`

`kink z v = h_z(v₊) = 1_{v>0} h_z(v)` (continuous, kinked at `0`), `katom z = Ψ₀ · kink z`.
Its transform is `Fk z λ = ∫_0^3 Ψ₀(v) h_z(v) e^{-2πiλv} dv` (`fourier_katom`), and with `a = -2πiλ`:
* `‖Fk‖ ≤ 9`;
* two integrations by parts (`φ = Ψ₀ h_z`, then `Ψ₀' h_z`; both vanish at `0` and `3`):
  `(2π|λ|)² ‖Fk z λ‖ ≤ C1 + 2π|λ| ‖J(λ - z)‖` (`Fk_ibp_bound`), the `J` term from `Ψ₀ e(zv) e^{-2πiλv}`;
* `‖J(μ)‖ ≤ 3`, `2π|μ| ‖J(μ)‖ ≤ C2`.
Hence `⟨λ⟩^θ |Fk| ≤ ⟨λ⟩^{1/2} |Fk| ≤ Kc (⟨λ⟩^{-3/2} + ⟨λ - z⟩^{-3/2})` (with `p q² ≤ p³ + q³`), and
`‖katom z‖_{A^θ} ≤ 2 Kc ∫⟨x⟩^{-3/2} dx` for every `z` (`katom_norm_le`). No splitting in `|z|` is needed. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal ContDiff FourierTransform

namespace WaveTurbulence.Flower.ProtPin

/-- The kinked one-link profile `k_z(v) = 1_{v>0} h_z(v) = h_z(v₊)`. -/
def kink (z v : ℝ) : ℂ := ProtTa.hz z (max v 0)

/-- The kinked atom `Ψ₀ k_z`. -/
def katom (z v : ℝ) : ℂ := Psi0 v * kink z v

theorem kink_continuous : Continuous (fun p : ℝ × ℝ => kink p.1 p.2) :=
  ProtTa.hz_continuous.comp (continuous_fst.prodMk (continuous_snd.max continuous_const))

theorem norm_kink_le (z v : ℝ) : ‖kink z v‖ ≤ |v| := by
  refine (ProtTa.norm_hz_le z _).trans ?_
  rcases le_total v 0 with h | h
  · rw [max_eq_right h, abs_zero]
    exact abs_nonneg v
  · rw [max_eq_left h]

theorem kink_of_nonpos (z : ℝ) {v : ℝ} (hv : v ≤ 0) : kink z v = 0 := by
  rw [kink, max_eq_right hv, hz_at_zero]

theorem katom_continuous (z : ℝ) : Continuous (katom z) :=
  Psi0_continuous.mul (kink_continuous.comp (continuous_const.prodMk continuous_id))

theorem katom_compact (z : ℝ) : HasCompactSupport (katom z) := Psi0_compact.mul_right

theorem katom_integrable (z : ℝ) : Integrable (katom z) :=
  (katom_continuous z).integrable_of_hasCompactSupport (katom_compact z)

theorem norm_katom_le (z v : ℝ) : ‖katom z v‖ ≤ ‖Psi0 v‖ * |v| := by
  rw [katom, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_kink_le z v) (norm_nonneg _)

/-- The transform of the kinked atom, as an integral over `[0,3]`. -/
def Fk (z l : ℝ) : ℂ := ∫ v in (0:ℝ)..3, Psi0 v * ProtTa.hz z v * Complex.exp (ea l * v)

theorem fourier_katom (z l : ℝ) : 𝓕 (katom z) l = Fk z l := by
  rw [Real.fourier_real_eq]
  have hsupp : ∀ v, v ∉ Set.Ioc (0:ℝ) 3 → Real.fourierChar (-(v * l)) • katom z v = 0 := by
    intro v hv
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hv
    rcases hv with hv | hv
    · rw [katom, kink_of_nonpos z hv, mul_zero, smul_zero]
    · rw [katom, Psi0_zero (by rw [abs_of_pos (by linarith)]; linarith), zero_mul, smul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 3)]
  unfold Fk
  refine intervalIntegral.integral_congr fun v hv => ?_
  have hv0 : 0 ≤ v := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3)] at hv
    exact hv.1
  simp only [katom, kink, max_eq_left hv0, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  rw [cexp_ea]
  have : ((2 * Real.pi * -(v * l) : ℝ) : ℂ) = ((-2 * Real.pi * l * v : ℝ) : ℂ) := by
    congr 1
    ring
  rw [this]
  ring

theorem norm_Fk_le (z l : ℝ) : ‖Fk z l‖ ≤ 9 := by
  unfold Fk
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 3) (C := 3)
    (f := fun v => Psi0 v * ProtTa.hz z v * Complex.exp (ea l * v)) (fun v hv => by
      rw [norm_mul, norm_mul, norm_cexp_ea, mul_one]
      have h1 := norm_Psi0_le v
      have h2 := ProtTa.norm_hz_le z v
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 3)] at hv
      have hv' : |v| ≤ 3 := by rw [abs_of_pos hv.1]; exact hv.2
      nlinarith [norm_nonneg (Psi0 v), norm_nonneg (ProtTa.hz z v)])
  norm_num at h
  linarith

/-- `C1 = ∫_0^3 (3|Ψ₀''| + |Ψ₀'|)`. -/
def C1 : ℝ := ∫ v in (0:ℝ)..3, (3 * ‖Psi2 v‖ + ‖Psi1 v‖)

theorem C1_nonneg : 0 ≤ C1 :=
  intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => by positivity)

/-- Two integrations by parts: `(2π|λ|)² |Fk z λ| ≤ C1 + 2π|λ| |J(λ - z)|`. -/
theorem Fk_ibp_bound (z l : ℝ) :
    (2 * Real.pi * |l|) ^ 2 * ‖Fk z l‖ ≤ C1 + 2 * Real.pi * |l| * ‖Jf (l - z)‖ := by
  by_cases hl : l = 0
  · subst hl
    simp only [abs_zero, mul_zero, zero_mul, add_zero]
    norm_num
    exact C1_nonneg
  have ha := ea_ne_zero hl
  have hPc := Psi0_continuous
  have hP1c := Psi1_contDiff.continuous
  have hP2c := Psi2_contDiff.continuous
  have hzc : Continuous (ProtTa.hz z) :=
    ProtTa.hz_continuous.comp (continuous_const.prodMk continuous_id)
  have hezc := ez_continuous z
  have hd1 : ∀ x, HasDerivAt (fun v => Psi0 v * ProtTa.hz z v)
      (Psi1 x * ProtTa.hz z x + Psi0 x * ez z x) x :=
    fun x => (hasDerivAt_Psi0 x).mul (hasDerivAt_hz z x)
  have hc1 : Continuous (fun x => Psi1 x * ProtTa.hz z x + Psi0 x * ez z x) :=
    (hP1c.mul hzc).add (hPc.mul hezc)
  have h1 := norm_ibp_le (R := 3) ha hd1 hc1 (by simp only [Psi0_at_three, zero_mul])
  have hd2 : ∀ x, HasDerivAt (fun v => Psi1 v * ProtTa.hz z v)
      (Psi2 x * ProtTa.hz z x + Psi1 x * ez z x) x :=
    fun x => (hasDerivAt_Psi1 x).mul (hasDerivAt_hz z x)
  have hc2 : Continuous (fun x => Psi2 x * ProtTa.hz z x + Psi1 x * ez z x) :=
    (hP2c.mul hzc).add (hP1c.mul hezc)
  have h2 := norm_ibp_le (R := 3) ha hd2 hc2 (by simp only [Psi1_at_three, zero_mul])
  have hcexp : Continuous (fun x : ℝ => Complex.exp (ea l * x)) := by fun_prop
  have hsplit : ∫ x in (0:ℝ)..3, (Psi1 x * ProtTa.hz z x + Psi0 x * ez z x) * Complex.exp (ea l * x) =
      (∫ x in (0:ℝ)..3, Psi1 x * ProtTa.hz z x * Complex.exp (ea l * x)) + Jf (l - z) := by
    unfold Jf
    have hI1 : IntervalIntegrable (fun x : ℝ => Psi1 x * ProtTa.hz z x * Complex.exp (ea l * x)) volume 0 3 :=
      ((hP1c.mul hzc).mul hcexp).intervalIntegrable _ _
    have hI2 : IntervalIntegrable (fun x : ℝ => Psi0 x * Complex.exp (ea (l - z) * x)) volume 0 3 :=
      (hPc.mul (by fun_prop : Continuous fun x : ℝ => Complex.exp (ea (l - z) * x))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add hI1 hI2]
    congr 1
    funext x
    rw [← ez_mul_cexp_ea]
    ring
  have h3 : ‖∫ x in (0:ℝ)..3, (Psi2 x * ProtTa.hz z x + Psi1 x * ez z x) * Complex.exp (ea l * x)‖ ≤ C1 := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans ?_
    unfold C1
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact ((hc2.mul hcexp).norm).intervalIntegrable _ _
    · exact (((hP2c.norm).const_smul (3:ℝ)).add hP1c.norm).intervalIntegrable _ _
    intro x hx
    rw [norm_mul, norm_cexp_ea, mul_one]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_ez, mul_one]
    have hh := ProtTa.norm_hz_le z x
    have hx3 : |x| ≤ 3 := by rw [abs_of_nonneg hx.1]; exact hx.2
    nlinarith [norm_nonneg (Psi2 x), norm_nonneg (ProtTa.hz z x)]
  rw [norm_ea] at h1 h2
  simp only [hz_at_zero, mul_zero, norm_zero, zero_add] at h1 h2
  rw [hsplit] at h1
  have h4 := norm_add_le (∫ x in (0:ℝ)..3, Psi1 x * ProtTa.hz z x * Complex.exp (ea l * x)) (Jf (l - z))
  set X := ‖∫ x in (0:ℝ)..3, Psi1 x * ProtTa.hz z x * Complex.exp (ea l * x)‖
  set A := 2 * Real.pi * |l|
  have hA : 0 ≤ A := by positivity
  have h2' : A * X ≤ C1 := h2.trans h3
  calc A ^ 2 * ‖Fk z l‖ = A * (A * ‖Fk z l‖) := by ring
    _ ≤ A * (X + ‖Jf (l - z)‖) := by
        apply mul_le_mul_of_nonneg_left _ hA
        unfold Fk
        exact h1.trans h4
    _ ≤ C1 + A * ‖Jf (l - z)‖ := by nlinarith

/-! ### The weighted bound -/

/-- `√⟨x⟩`. -/
def sq4 (x : ℝ) : ℝ := Real.sqrt (Sumint.scalarBracket x)

theorem sq4_pos (x : ℝ) : 0 < sq4 x :=
  Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (Sumint.one_le_scalarBracket x))

theorem sq4_sq (x : ℝ) : sq4 x ^ 2 = Sumint.scalarBracket x :=
  Real.sq_sqrt (zero_le_one.trans (Sumint.one_le_scalarBracket x))

theorem rpow_le_sq4 {θ : ℝ} (hθ : θ ≤ 1 / 2) (x : ℝ) : Sumint.scalarBracket x ^ θ ≤ sq4 x := by
  rw [sq4, Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le (Sumint.one_le_scalarBracket x) hθ

/-- The integrable envelope `⟨x⟩^{-3/2}`. -/
def env (x : ℝ) : ℝ := 1 / sq4 x ^ 3

theorem env_nonneg (x : ℝ) : 0 ≤ env x := by
  unfold env
  have := sq4_pos x
  positivity

theorem env_integrable : Integrable env := by
  have hi := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := (3 / 2 : ℝ))
    (by norm_num)
  apply hi.congr
  filter_upwards [] with x
  rw [Real.norm_eq_abs, sq_abs]
  have hy : (0 : ℝ) ≤ 1 + x ^ 2 := by positivity
  unfold env sq4 Sumint.scalarBracket
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hy,
    ← Real.rpow_natCast ((1 + x ^ 2) ^ (1 / 2 * (1 / 2) : ℝ)) 3, ← Real.rpow_mul hy, one_div,
    ← Real.rpow_neg hy]
  norm_num

/-- `p q² ≤ p³ + q³` in reciprocal form. -/
theorem inv_mul_sq_le {p r : ℝ} (hp : 0 < p) (hr : 0 < r) :
    1 / (p * r ^ 2) ≤ 1 / p ^ 3 + 1 / r ^ 3 := by
  have h3 : p ^ 2 * r ≤ r ^ 3 + p ^ 3 := by
    nlinarith [mul_nonneg (add_pos hp hr).le (sq_nonneg (p - r)), mul_pos hp (pow_pos hr 2)]
  calc 1 / (p * r ^ 2) = p ^ 2 * r / (p ^ 3 * r ^ 3) := by field_simp
    _ ≤ (r ^ 3 + p ^ 3) / (p ^ 3 * r ^ 3) := by gcongr
    _ = 1 / p ^ 3 + 1 / r ^ 3 := by field_simp

/-- The algebra of the weighted bound. -/
theorem alg_bound {p r f j K0 D e : ℝ} (hp : 0 < p) (hr : 0 < r) (he : 0 < e) (hK0 : 0 ≤ K0)
    (hD : 0 ≤ D) (h1 : (p ^ 2) ^ 2 * f ≤ K0 + p ^ 2 * j / e) (h2 : r ^ 2 * j ≤ D) :
    p * f ≤ (K0 + D / e) * (1 / p ^ 3 + 1 / r ^ 3) := by
  have hDe : 0 ≤ D / e := div_nonneg hD he.le
  have key : p ^ 4 * r ^ 2 * f ≤ K0 * r ^ 2 + D / e * p ^ 2 := by
    have h1' := mul_le_mul_of_nonneg_left h1 (sq_nonneg r)
    have h2' : p ^ 2 * (r ^ 2 * j) / e ≤ p ^ 2 * D / e :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (sq_nonneg p)) he.le
    have e1 : r ^ 2 * ((p ^ 2) ^ 2 * f) = p ^ 4 * r ^ 2 * f := by ring
    have e2 : r ^ 2 * (K0 + p ^ 2 * j / e) = K0 * r ^ 2 + p ^ 2 * (r ^ 2 * j) / e := by ring
    have e3 : p ^ 2 * D / e = D / e * p ^ 2 := by ring
    linarith
  have step : p * f ≤ K0 / p ^ 3 + D / e / (p * r ^ 2) := by
    rw [div_add_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left key hp.le]
  have hinv := inv_mul_sq_le hp hr
  have hq3 : 0 ≤ 1 / r ^ 3 := by positivity
  calc p * f ≤ K0 / p ^ 3 + D / e / (p * r ^ 2) := step
    _ = K0 * (1 / p ^ 3) + D / e * (1 / (p * r ^ 2)) := by ring
    _ ≤ K0 * (1 / p ^ 3 + 1 / r ^ 3) + D / e * (1 / p ^ 3 + 1 / r ^ 3) := by
        gcongr
        linarith
    _ = (K0 + D / e) * (1 / p ^ 3 + 1 / r ^ 3) := by ring

/-- `D = 3 + C2/(2π)`, the bound on `⟨μ⟩ |J(μ)|`. -/
def Dk : ℝ := 3 + C2 / (2 * Real.pi)

/-- The atom constant. -/
def Kc : ℝ := 9 + C1 / (2 * Real.pi) ^ 2 + Dk / (2 * Real.pi)

theorem Dk_nonneg : 0 ≤ Dk := by
  unfold Dk
  have := C2_pos
  positivity

theorem Kc_nonneg : 0 ≤ Kc := by
  unfold Kc
  have := C1_nonneg
  have := Dk_nonneg
  positivity

theorem bracket_mul_Jf_le (μ : ℝ) : Sumint.scalarBracket μ * ‖Jf μ‖ ≤ Dk := by
  have hb : Sumint.scalarBracket μ ≤ 1 + |μ| := by
    unfold Sumint.scalarBracket
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_abs μ, abs_nonneg μ]
  have hJ := norm_Jf_le μ
  have hJ2 := mul_norm_Jf_le μ
  have hpi : 0 < 2 * Real.pi := by positivity
  have hm : |μ| * ‖Jf μ‖ ≤ C2 / (2 * Real.pi) := by
    rw [le_div_iff₀ hpi]
    nlinarith
  unfold Dk
  nlinarith [norm_nonneg (Jf μ), abs_nonneg μ]

/-- The pointwise weighted bound on the transform of the kinked atom, uniform in `z`. -/
theorem weighted_Fk_le {θ : ℝ} (hθ : θ ≤ 1 / 2) (z l : ℝ) :
    Sumint.scalarBracket l ^ θ * ‖Fk z l‖ ≤ Kc * (env l + env (l - z)) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  set b := Sumint.scalarBracket l with hbdef
  set p := sq4 l with hpdef
  set r := sq4 (l - z) with hrdef
  have hp := sq4_pos l
  have hr := sq4_pos (l - z)
  have hpb : p ^ 2 = b := sq4_sq l
  have hrc : r ^ 2 = Sumint.scalarBracket (l - z) := sq4_sq (l - z)
  have hf0 : 0 ≤ ‖Fk z l‖ := norm_nonneg _
  have hj0 : 0 ≤ ‖Jf (l - z)‖ := norm_nonneg _
  have hb2 : b ^ 2 = 1 + l ^ 2 := by
    rw [hbdef]
    unfold Sumint.scalarBracket
    exact Real.sq_sqrt (by positivity)
  have hLb : |l| ≤ b := Sumint.abs_le_scalarBracket l
  have hF1 := norm_Fk_le z l
  have hF2 := Fk_ibp_bound z l
  have h1 : (p ^ 2) ^ 2 * ‖Fk z l‖ ≤ (9 + C1 / (2 * Real.pi) ^ 2) + p ^ 2 * ‖Jf (l - z)‖ / (2 * Real.pi) := by
    rw [hpb, hb2]
    have hl2 : l ^ 2 * ‖Fk z l‖ ≤ C1 / (2 * Real.pi) ^ 2 + |l| * ‖Jf (l - z)‖ / (2 * Real.pi) := by
      have e : (2 * Real.pi * |l|) ^ 2 * ‖Fk z l‖ = (2 * Real.pi) ^ 2 * (l ^ 2 * ‖Fk z l‖) := by
        rw [mul_pow, sq_abs]; ring
      rw [e] at hF2
      have e2 : C1 / (2 * Real.pi) ^ 2 + |l| * ‖Jf (l - z)‖ / (2 * Real.pi) =
          (C1 + 2 * Real.pi * |l| * ‖Jf (l - z)‖) / (2 * Real.pi) ^ 2 := by
        field_simp
      rw [e2, le_div_iff₀ (by positivity)]
      linarith
    have hLj : |l| * ‖Jf (l - z)‖ / (2 * Real.pi) ≤ b * ‖Jf (l - z)‖ / (2 * Real.pi) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hLb hj0) hpi.le
    nlinarith
  have h2 : r ^ 2 * ‖Jf (l - z)‖ ≤ Dk := by rw [hrc]; exact bracket_mul_Jf_le (l - z)
  have hK0 : 0 ≤ 9 + C1 / (2 * Real.pi) ^ 2 := by have := C1_nonneg; positivity
  have halg := alg_bound hp hr hpi hK0 Dk_nonneg h1 h2
  have hw : b ^ θ ≤ p := rpow_le_sq4 hθ l
  calc b ^ θ * ‖Fk z l‖ ≤ p * ‖Fk z l‖ := mul_le_mul_of_nonneg_right hw hf0
    _ ≤ (9 + C1 / (2 * Real.pi) ^ 2 + Dk / (2 * Real.pi)) * (1 / p ^ 3 + 1 / r ^ 3) := halg
    _ = Kc * (env l + env (l - z)) := by rw [Kc, env, env]

/-- The uniform atom constant `B = 2 Kc ∫ ⟨x⟩^{-3/2} dx`. -/
def Bk : ℝ := Kc * (2 * ∫ x, env x)

theorem Bk_nonneg : 0 ≤ Bk := by
  unfold Bk
  have := Kc_nonneg
  have : 0 ≤ ∫ x, env x := integral_nonneg env_nonneg
  positivity

/-- **The kinked atom** `T ↦ Ψ₀(T) k_z(T)` (one time) has `A^θ` norm at most `Bk` for every `z`, `θ ≤ 1/2`. -/
theorem katom_norm_le {θ : ℝ} (hθ : θ ≤ 1 / 2) (z : ℝ) :
    timeFourierNorm θ (fun T : Fin 1 → ℝ => katom z (T 0)) ≤ ENNReal.ofReal Bk := by
  have hiT : Integrable (fun T : Fin 1 → ℝ => katom z (T 0)) :=
    (volume_preserving_funUnique (Fin 1) ℝ).integrable_comp_of_integrable (katom_integrable z)
  rw [timeFourierNorm_eq_lintegral hiT, lintegral_lift_one θ (katom z)]
  simp_rw [fourier_katom]
  have hint : Integrable (fun x : ℝ => Kc * (env x + env (x - z))) :=
    (env_integrable.add (env_integrable.comp_sub_right z)).const_mul Kc
  have hnn : 0 ≤ᵐ[volume] fun x : ℝ => Kc * (env x + env (x - z)) :=
    ae_of_all _ fun x => mul_nonneg Kc_nonneg (add_nonneg (env_nonneg x) (env_nonneg _))
  calc ∫⁻ x, ENNReal.ofReal (Sumint.scalarBracket x ^ θ) * ‖Fk z x‖ₑ
      ≤ ∫⁻ x, ENNReal.ofReal (Kc * (env x + env (x - z))) := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_mul
          (Real.rpow_nonneg (zero_le_one.trans (Sumint.one_le_scalarBracket x)) _)]
        exact ENNReal.ofReal_le_ofReal (weighted_Fk_le hθ z x)
    _ = ENNReal.ofReal (∫ x, Kc * (env x + env (x - z))) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = ENNReal.ofReal Bk := by
        rw [integral_const_mul, integral_add env_integrable (env_integrable.comp_sub_right z),
          integral_sub_right_eq_self, Bk]
        ring_nf

end WaveTurbulence.Flower.ProtPin
