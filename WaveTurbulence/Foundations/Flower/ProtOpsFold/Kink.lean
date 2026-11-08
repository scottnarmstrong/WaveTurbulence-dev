/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib

/-! # D1b-F FOLD 1: the one-dimensional kink atom (o82 Lemma 17.1, the atom estimate behind (17.2))

`kinkAtom c α β x = e^{-|x-c|} e(α x + β |x - c|)` has the exact transform
`oneFT (kinkAtom c α β) z = e((α - z) c) · kinkHat β (z - α)` with
`kinkHat β ζ = 1/(1 + 2πi(ζ-β)) + 1/(1 - 2πi(ζ+β))`. Hence `|kinkHat β ζ| ≤ 16π(1+|β|)/((1+|ζ-β|)(1+|ζ+β|))` and
`∫ (1+|ξ|)^s |kinkHat β (ξ-α)| dξ ≤ C_{s,ε} max(1+|α|, 1+|β|)^{s+ε}` for `0 ≤ s`, `0 < ε`, `s + ε ≤ 1`: the
leading reciprocals cancel in the tail (o82 §17), and no logarithm appears (the near region costs `(1+|β|)^ε`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Real

namespace WaveTurbulence.Flower.ProtOpsFold

/-- One-dimensional Fourier transform with the time pairing `e(-x z)`. -/
def oneFT (g : ℝ → ℂ) (z : ℝ) : ℂ := ∫ x, (Real.fourierChar (-(x * z)) : ℂ) * g x

/-- The kink atom `e^{-|x-c|} e(α x + β |x-c|)`. -/
def kinkAtom (c α β x : ℝ) : ℂ :=
  Complex.exp (-((|x - c| : ℝ) : ℂ) + 2 * π * Complex.I * (α * x + β * ((|x - c| : ℝ) : ℂ)))

/-- The transform of `e^{-(1 - 2πiβ)|u|}` at `ζ`. -/
def kinkHat (β ζ : ℝ) : ℂ :=
  1 / (1 + 2 * π * Complex.I * (ζ - β)) + 1 / (1 - 2 * π * Complex.I * (ζ + β))

theorem kinkAtom_continuous (c α β : ℝ) : Continuous (kinkAtom c α β) := by
  unfold kinkAtom; fun_prop

theorem norm_kinkAtom (c α β x : ℝ) : ‖kinkAtom c α β x‖ = Real.exp (-|x - c|) := by
  unfold kinkAtom
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im]

/-- The two-sided exponential transform. -/
theorem integral_exp_abs {w : ℂ} (hw : 0 < w.re) (ζ : ℝ) :
    ∫ u : ℝ, Complex.exp (-w * ((|u| : ℝ) : ℂ) - 2 * π * Complex.I * ζ * u) =
      1 / (w + 2 * π * Complex.I * ζ) + 1 / (w - 2 * π * Complex.I * ζ) := by
  set f : ℝ → ℂ := fun u => Complex.exp (-w * ((|u| : ℝ) : ℂ) - 2 * π * Complex.I * ζ * u) with hf
  have hR : EqOn f (fun u : ℝ => Complex.exp (-(w + 2 * π * Complex.I * ζ) * u)) (Ioi 0) := by
    intro u hu
    simp only [hf, abs_of_pos (mem_Ioi.mp hu)]
    ring_nf
  have hL : EqOn f (fun u : ℝ => Complex.exp ((w - 2 * π * Complex.I * ζ) * u)) (Iic 0) := by
    intro u hu
    simp only [hf, abs_of_nonpos (mem_Iic.mp hu), Complex.ofReal_neg]
    ring_nf
  have reR : (-(w + 2 * π * Complex.I * ζ)).re < 0 := by
    simp [Complex.add_re, Complex.mul_re]; linarith
  have reL : 0 < (w - 2 * π * Complex.I * ζ).re := by
    simp [Complex.sub_re, Complex.mul_re]; linarith
  have iR : IntegrableOn f (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi reR 0).congr_fun (fun u hu => (hR hu).symm) measurableSet_Ioi
  have iL : IntegrableOn f (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic reL 0).congr_fun (fun u hu => (hL hu).symm) measurableSet_Iic
  have h1 : w + 2 * π * Complex.I * ζ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [Complex.add_re, Complex.mul_re] at this; linarith
  have h2 : w - 2 * π * Complex.I * ζ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [Complex.sub_re, Complex.mul_re] at this; linarith
  rw [← intervalIntegral.integral_Iic_add_Ioi iL iR, setIntegral_congr_fun measurableSet_Iic hL,
    setIntegral_congr_fun measurableSet_Ioi hR, integral_exp_mul_complex_Ioi reR,
    integral_exp_mul_complex_Iic reL]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring

/-- **The exact transform of the kink atom.** -/
theorem oneFT_kinkAtom (c α β z : ℝ) :
    oneFT (kinkAtom c α β) z =
      Complex.exp (2 * π * Complex.I * ((α - z) * c)) * kinkHat β (z - α) := by
  unfold oneFT
  rw [← integral_add_right_eq_self (μ := (volume : Measure ℝ)) _ c]
  have hpt : ∀ u : ℝ, (Real.fourierChar (-((u + c) * z)) : ℂ) * kinkAtom c α β (u + c) =
      Complex.exp (2 * π * Complex.I * ((α - z) * c)) *
        Complex.exp (-(1 - 2 * π * Complex.I * β) * ((|u| : ℝ) : ℂ) - 2 * π * Complex.I * (z - α) * u) := by
    intro u
    rw [Real.fourierChar_apply, kinkAtom, add_sub_cancel_right, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  have hre : 0 < (1 - 2 * π * Complex.I * (β : ℂ)).re := by
    simp [Complex.sub_re, Complex.mul_re]
  have hint := integral_exp_abs hre (z - α)
  push_cast at hint ⊢
  rw [hint]
  unfold kinkHat
  push_cast
  congr 1
  congr 1
  · congr 1; ring
  · congr 1; ring

theorem norm_one_add_two_pi_I_ge (y : ℝ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    (1 + |y|) / 2 ≤ ‖(1 : ℂ) + σ * (2 * π * Complex.I * y)‖ := by
  have hre := Complex.abs_re_le_norm ((1 : ℂ) + σ * (2 * π * Complex.I * y))
  have him := Complex.abs_im_le_norm ((1 : ℂ) + σ * (2 * π * Complex.I * y))
  have hpi : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hs : |σ| = 1 := by rcases hσ with h | h <;> simp [h]
  simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im] at hre him
  rw [hs, one_mul] at him
  have : |y| ≤ 2 * π * |y| := by nlinarith [abs_nonneg y]
  linarith

/-- **Pointwise bound** with the cancelled leading reciprocals. -/
theorem norm_kinkHat_le (β ζ : ℝ) :
    ‖kinkHat β ζ‖ ≤ 16 * π * (1 + |β|) / ((1 + |ζ - β|) * (1 + |ζ + β|)) := by
  set d1 : ℂ := 1 + 2 * π * Complex.I * (ζ - β) with hd1def
  set d2 : ℂ := 1 - 2 * π * Complex.I * (ζ + β) with hd2def
  have hd1 : (1 + |ζ - β|) / 2 ≤ ‖d1‖ := by
    have := norm_one_add_two_pi_I_ge (ζ - β) 1 (Or.inl rfl)
    simpa [hd1def] using this
  have hd2 : (1 + |ζ + β|) / 2 ≤ ‖d2‖ := by
    have := norm_one_add_two_pi_I_ge (ζ + β) (-1) (Or.inr rfl)
    have he : (1 : ℂ) + ((-1 : ℝ) : ℂ) * (2 * π * Complex.I * ((ζ + β : ℝ) : ℂ)) = d2 := by
      rw [hd2def]; push_cast; ring
    rw [he] at this; exact this
  have hp1 : 0 < (1 + |ζ - β|) / 2 := by positivity
  have hp2 : 0 < (1 + |ζ + β|) / 2 := by positivity
  have hn1 : d1 ≠ 0 := fun h => by rw [h, norm_zero] at hd1; linarith
  have hn2 : d2 ≠ 0 := fun h => by rw [h, norm_zero] at hd2; linarith
  have hk : kinkHat β ζ = 2 * (1 - 2 * π * Complex.I * β) / (d1 * d2) := by
    unfold kinkHat
    rw [← hd1def, ← hd2def]
    field_simp
    rw [hd1def, hd2def]
    ring
  have hpi : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hn : ‖(2 : ℂ) * (1 - 2 * π * Complex.I * β)‖ ≤ 4 * π * (1 + |β|) := by
    rw [norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have h3 : ‖(1 : ℂ) - 2 * π * Complex.I * β‖ ≤ 1 + 2 * π * |β| := by
      refine (norm_sub_le _ _).trans ?_
      simp [abs_of_pos Real.pi_pos]
    rw [h2]
    nlinarith [abs_nonneg β]
  rw [hk, norm_div, norm_mul d1 d2]
  calc ‖(2 : ℂ) * (1 - 2 * π * Complex.I * β)‖ / (‖d1‖ * ‖d2‖)
      ≤ 4 * π * (1 + |β|) / ((1 + |ζ - β|) / 2 * ((1 + |ζ + β|) / 2)) :=
        div_le_div₀ (by positivity) hn (by positivity) (mul_le_mul hd1 hd2 hp2.le (norm_nonneg _))
    _ = 16 * π * (1 + |β|) / ((1 + |ζ - β|) * (1 + |ζ + β|)) := by
        field_simp
        ring

/-- The real inequality behind the weighted bound (cases `L ≥ K` and `L < K`). -/
theorem kink_real_le {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε) (hse : s + ε ≤ 1) {x K N m L : ℝ}
    (hK : 1 ≤ K) (hN : 1 ≤ N) (hm : 1 ≤ m) (hmL : m ≤ L) (hNL : N ≤ L) (hx0 : 0 ≤ x)
    (hx : x ≤ L + K) :
    x ^ s * N / (m * L) ≤ 2 ^ s * max K N ^ (s + ε) * m ^ (-(1 + ε)) := by
  have hm0 : 0 < m := by linarith
  have hL0 : 0 < L := by linarith
  have hN0 : 0 < N := by linarith
  have hK0 : 0 < K := by linarith
  set M := max K N with hM
  have hM0 : 0 < M := lt_of_lt_of_le hK0 (le_max_left _ _)
  set A := max L K with hA
  have hA0 : 0 < A := lt_of_lt_of_le hL0 (le_max_left _ _)
  have hxA : x ^ s ≤ 2 ^ s * A ^ s := by
    rw [← Real.mul_rpow (by norm_num) hA0.le]
    exact Real.rpow_le_rpow hx0 (by linarith [le_max_left L K, le_max_right L K]) hs
  have hclaim : A ^ s * N / L ≤ M ^ (s + ε) * m ^ (-ε) := by
    rcases le_or_gt K L with hKL | hKL
    · have hAL : A = L := max_eq_left hKL
      rw [hAL]
      have e1 : L ^ s * N / L = N * (L ^ (s + ε - 1) * L ^ (-ε)) := by
        rw [← Real.rpow_add hL0]
        have : s + ε - 1 + -ε = s - 1 := by ring
        rw [this, Real.rpow_sub_one hL0.ne']
        ring
      rw [e1]
      have hb1 : L ^ (s + ε - 1) ≤ N ^ (s + ε - 1) := Real.rpow_le_rpow_of_nonpos hN0 hNL (by linarith)
      have hb2 : L ^ (-ε) ≤ m ^ (-ε) := Real.rpow_le_rpow_of_nonpos hm0 hmL (by linarith)
      have hb3 : N ^ (s + ε) ≤ M ^ (s + ε) :=
        Real.rpow_le_rpow hN0.le (le_max_right _ _) (by linarith)
      calc N * (L ^ (s + ε - 1) * L ^ (-ε)) ≤ N * (N ^ (s + ε - 1) * m ^ (-ε)) := by
            gcongr
        _ = N ^ (s + ε) * m ^ (-ε) := by
            rw [← mul_assoc]
            congr 1
            rw [show s + ε = (s + ε - 1) + 1 by ring, Real.rpow_add_one hN0.ne']
            ring
        _ ≤ M ^ (s + ε) * m ^ (-ε) := by
            gcongr
    · have hAK : A = K := max_eq_right hKL.le
      rw [hAK]
      have hNL1 : N / L ≤ 1 := (div_le_one hL0).mpr hNL
      have e1 : K ^ s = K ^ (s + ε) * K ^ (-ε) := by
        rw [← Real.rpow_add hK0]; congr 1; ring
      have hb1 : K ^ (-ε) ≤ m ^ (-ε) := Real.rpow_le_rpow_of_nonpos hm0 (by linarith) (by linarith)
      have hb2 : K ^ (s + ε) ≤ M ^ (s + ε) := Real.rpow_le_rpow hK0.le (le_max_left _ _) (by linarith)
      calc K ^ s * N / L = K ^ s * (N / L) := by ring
        _ ≤ K ^ s * 1 := by gcongr
        _ = K ^ (s + ε) * K ^ (-ε) := by rw [mul_one, e1]
        _ ≤ M ^ (s + ε) * m ^ (-ε) := by
            gcongr
  have hmexp : m ^ (-ε) / m = m ^ (-(1 + ε)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hm0]
    congr 1; ring
  calc x ^ s * N / (m * L) = x ^ s * N / L / m := by rw [mul_comm m L, div_div]
    _ ≤ 2 ^ s * A ^ s * N / L / m := by gcongr
    _ = 2 ^ s * (A ^ s * N / L) / m := by ring
    _ ≤ 2 ^ s * (M ^ (s + ε) * m ^ (-ε)) / m := by gcongr
    _ = 2 ^ s * M ^ (s + ε) * (m ^ (-ε) / m) := by ring
    _ = 2 ^ s * M ^ (s + ε) * m ^ (-(1 + ε)) := by rw [hmexp]

/-- `∫ (1+|ζ|)^{-(1+ε)} dζ`. -/
def kinkI (ε : ℝ) : ℝ := ∫ ζ : ℝ, (1 + |ζ|) ^ (-(1 + ε))

theorem integrable_kinkTail {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    Integrable (fun ζ : ℝ => (1 + |ζ - a|) ^ (-(1 + ε))) := by
  have h : Integrable (fun ζ : ℝ => (1 + ‖ζ‖) ^ (-(1 + ε))) :=
    integrable_one_add_norm (by simp; linarith)
  simpa [Real.norm_eq_abs] using h.comp_sub_right a

theorem integral_kinkTail (ε a : ℝ) :
    ∫ ζ : ℝ, (1 + |ζ - a|) ^ (-(1 + ε)) = kinkI ε :=
  integral_sub_right_eq_self (fun ζ : ℝ => (1 + |ζ|) ^ (-(1 + ε))) a

theorem kinkI_nonneg (ε : ℝ) : 0 ≤ kinkI ε :=
  integral_nonneg fun ζ => (Real.rpow_pos_of_pos (by positivity) _).le

/-- The constant of the weighted kink bound. -/
def kinkC (s ε : ℝ) : ℝ := 16 * π * 2 ^ s * (2 * kinkI ε)

theorem kinkC_nonneg (s ε : ℝ) : 0 ≤ kinkC s ε := by
  unfold kinkC
  have := kinkI_nonneg ε
  positivity

/-- **The weighted kink integral** `∫ (1+|ξ|)^s |kinkHat β (ξ-α)| ≤ C max(1+|α|, 1+|β|)^{s+ε}`. -/
theorem kink_weighted_le {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε) (hse : s + ε ≤ 1) (α β : ℝ) :
    ∫⁻ ξ : ℝ, ENNReal.ofReal ((1 + |ξ|) ^ s) * ‖kinkHat β (ξ - α)‖ₑ ≤
      ENNReal.ofReal (kinkC s ε * max (1 + |α|) (1 + |β|) ^ (s + ε)) := by
  set M := max (1 + |α|) (1 + |β|)
  set g : ℝ → ℝ := fun ξ => 16 * π * (2 ^ s * M ^ (s + ε)) *
    ((1 + |ξ - (α + β)|) ^ (-(1 + ε)) + (1 + |ξ - (α - β)|) ^ (-(1 + ε))) with hg
  have hgi : Integrable g :=
    ((integrable_kinkTail hε (α + β)).add (integrable_kinkTail hε (α - β))).const_mul _
  have hg0 : ∀ ξ, 0 ≤ g ξ := fun ξ => by
    have := Real.rpow_pos_of_pos (show (0 : ℝ) < 1 + |ξ - (α + β)| by positivity) (-(1 + ε))
    have := Real.rpow_pos_of_pos (show (0 : ℝ) < 1 + |ξ - (α - β)| by positivity) (-(1 + ε))
    have := Real.rpow_pos_of_pos (show (0 : ℝ) < M by positivity) (s + ε)
    positivity
  have hpt : ∀ ξ : ℝ, ENNReal.ofReal ((1 + |ξ|) ^ s) * ‖kinkHat β (ξ - α)‖ₑ ≤ ENNReal.ofReal (g ξ) := by
    intro ξ
    set ζ := ξ - α
    set P := 1 + |ζ - β|
    set Q := 1 + |ζ + β|
    have hP : 1 ≤ P := by simp [P]
    have hQ : 1 ≤ Q := by simp [Q]
    have hsum : 2 * (1 + |β|) ≤ P + Q := by
      have := abs_sub_abs_le_abs_sub (ζ + β) (ζ - β)
      have h2 : |(ζ + β) - (ζ - β)| = 2 * |β| := by
        rw [show (ζ + β) - (ζ - β) = 2 * β by ring, abs_mul]; norm_num
      have := abs_sub_le_iff.mp (abs_abs_sub_abs_le_abs_sub (ζ + β) (ζ - β))
      have h3 : |(ζ + β) - (ζ - β)| ≤ |ζ + β| + |ζ - β| := by
        have := abs_sub (ζ + β) (ζ - β); linarith
      simp only [P, Q]; linarith
    have hsumz : 2 * (1 + |ζ|) ≤ P + Q := by
      have h3 : |(ζ + β) + (ζ - β)| ≤ |ζ + β| + |ζ - β| := abs_add_le _ _
      have h2 : |(ζ + β) + (ζ - β)| = 2 * |ζ| := by
        rw [show (ζ + β) + (ζ - β) = 2 * ζ by ring, abs_mul]; norm_num
      simp only [P, Q]; linarith
    have hNL : 1 + |β| ≤ max P Q := by
      linarith [le_max_left P Q, le_max_right P Q]
    have hxL : 1 + |ξ| ≤ max P Q + (1 + |α|) := by
      have : |ξ| ≤ |ζ| + |α| := by
        have := abs_add_le ζ α; simpa [ζ] using this
      linarith [le_max_left P Q, le_max_right P Q]
    have hmin : 1 ≤ min P Q := le_min hP hQ
    have hreal := kink_real_le hs hε hse (x := 1 + |ξ|) (K := 1 + |α|) (N := 1 + |β|)
      (m := min P Q) (L := max P Q) (by simp) (by simp) hmin (min_le_max) hNL (by positivity) hxL
    have hPQ : min P Q * max P Q = P * Q := min_mul_max P Q
    have hminpow : min P Q ^ (-(1 + ε)) ≤ P ^ (-(1 + ε)) + Q ^ (-(1 + ε)) := by
      have hP' := Real.rpow_pos_of_pos (show (0:ℝ) < P by linarith) (-(1 + ε))
      have hQ' := Real.rpow_pos_of_pos (show (0:ℝ) < Q by linarith) (-(1 + ε))
      rcases min_choice P Q with h | h <;> rw [h] <;> linarith
    have hnorm := norm_kinkHat_le β ζ
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos (by positivity) _).le]
    apply ENNReal.ofReal_le_ofReal
    have hx0 : 0 ≤ (1 + |ξ|) ^ s := (Real.rpow_pos_of_pos (by positivity) _).le
    have hPQ0 : 0 < P * Q := by positivity
    calc (1 + |ξ|) ^ s * ‖kinkHat β ζ‖
        ≤ (1 + |ξ|) ^ s * (16 * π * (1 + |β|) / (P * Q)) := by gcongr
      _ = 16 * π * ((1 + |ξ|) ^ s * (1 + |β|) / (min P Q * max P Q)) := by rw [hPQ]; ring
      _ ≤ 16 * π * (2 ^ s * M ^ (s + ε) * min P Q ^ (-(1 + ε))) := by gcongr
      _ ≤ 16 * π * (2 ^ s * M ^ (s + ε) * (P ^ (-(1 + ε)) + Q ^ (-(1 + ε)))) := by
          have := Real.rpow_pos_of_pos (show (0 : ℝ) < M by positivity) (s + ε)
          gcongr
      _ = g ξ := by
          simp only [g, P, Q, ζ]
          have e1 : ξ - α - β = ξ - (α + β) := by ring
          have e2 : ξ - α + β = ξ - (α - β) := by ring
          rw [e1, e2]; ring
  calc ∫⁻ ξ : ℝ, ENNReal.ofReal ((1 + |ξ|) ^ s) * ‖kinkHat β (ξ - α)‖ₑ
      ≤ ∫⁻ ξ, ENNReal.ofReal (g ξ) := lintegral_mono hpt
    _ = ENNReal.ofReal (∫ ξ, g ξ) := (ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0)).symm
    _ = ENNReal.ofReal (kinkC s ε * M ^ (s + ε)) := by
        congr 1
        rw [hg, integral_const_mul, integral_add (integrable_kinkTail hε _) (integrable_kinkTail hε _),
          integral_kinkTail, integral_kinkTail]
        unfold kinkC
        ring

end WaveTurbulence.Flower.ProtOpsFold
