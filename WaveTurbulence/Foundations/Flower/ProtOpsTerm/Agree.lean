/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsTerm.Slice

/-! # PROT-OPS-TERM: `T_A h` with `r` spectators as a Fourier synthesis, almost everywhere -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier WaveTurbulence.Flower.ProtTa
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtOpsTerm

theorem pairing_append {n m : ℕ} (a c : Fin n → ℝ) (b d : Fin m → ℝ) :
    timePairing (n + m) (Fin.append a b) (Fin.append c d) = timePairing n a c + timePairing m b d := by
  simp only [pairing_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem pairing_split {n m : ℕ} (l : Fin (n + m) → ℝ) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    timePairing (n + m) l (Fin.append x w) = timePairing n (hd l) x + timePairing m (tl l) w := by
  conv_lhs => rw [← append_hd_tl l]
  exact pairing_append _ _ _ _

theorem char_add (a b : ℝ) :
    ((Real.fourierChar (a + b) : Circle) : ℂ) = (Real.fourierChar a : ℂ) * (Real.fourierChar b : ℂ) := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- Inversion formula on `ℝ^n` (positive character). -/
def reconN {n : ℕ} (h : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  ∫ l, Real.fourierChar (timePairing n l x) • timeFourier h l

theorem reconN_ae {n : ℕ} {h : (Fin n → ℝ) → ℂ} (hint : Integrable h) (hhat : Integrable (timeFourier h)) :
    reconN h =ᵐ[volume] h := by
  have := Regref.timeFourier_inversion_ae hint hhat
  refine Filter.EventuallyEq.trans (ae_of_all _ fun x => ?_) this
  simp only [reconN, timeFourier, VectorFourier.fourierIntegral, map_neg, LinearMap.neg_apply, neg_neg]

theorem ae_slice_r {r : ℕ} {P : (Fin (r + 3) → ℝ) → Prop} (h : ∀ᵐ x : Fin (r + 3) → ℝ, P x) :
    ∀ᵐ ts : Fin (r + 2) → ℝ, ∀ᵐ u : ℝ,
      P (Fin.append (hd ts) ![tl ts 0, u, tl ts 1]) := by
  have h2 := (lamMP r).quasiMeasurePreserving.ae h
  have h3 := (Measure.measurePreserving_swap (μ := (volume : Measure (Fin (r + 2) → ℝ)))
    (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae h2
  exact Measure.ae_ae_of_ae_prod h3

theorem swap_int {n : ℕ} (a b : ℝ) (f : ℝ → (Fin n → ℝ) → ℂ)
    (hf : Integrable (Function.uncurry f) ((volume.restrict (Set.uIoc a b)).prod volume)) :
    ∫ u in a..b, ∫ l, f u l = ∫ l, ∫ u in a..b, f u l := by
  rcases le_total a b with hab | hab
  · rw [Set.uIoc_of_le hab] at hf
    simp only [intervalIntegral.integral_of_le hab]
    exact integral_integral_swap hf
  · rw [Set.uIoc_of_ge hab] at hf
    simp only [intervalIntegral.integral_of_ge hab, integral_neg]
    rw [integral_integral_swap hf]

theorem op_agree_r {r : ℕ} {h : (Fin (r + 3) → ℝ) → ℂ} (hint : Integrable h)
    (hhat : Integrable (timeFourier h)) (A : ℝ) :
    ∀ᵐ ts : Fin (r + 2) → ℝ,
      (∫ u in tl ts 1..tl ts 0, Complex.exp (((Real.pi * A * (u - tl ts 1) : ℝ) : ℂ) * Complex.I) *
          h (Fin.append (hd ts) ![tl ts 0, u, tl ts 1])) =
        ∫ l, timeFourier h l * ((Real.fourierChar (timePairing r (hd l) (hd ts)) : ℂ) *
          ((Real.fourierChar (timePairing 2 (tl ts) (nu (tl l))) : ℂ) *
            hz (A / 2 + tl l 1) (tl ts 0 - tl ts 1))) := by
  have hae := ae_slice_r (P := fun x => reconN h x = h x) (reconN_ae hint hhat)
  filter_upwards [hae] with ts hy
  set y : Fin 2 → ℝ := tl ts with hydef
  set x : Fin r → ℝ := hd ts with hxdef
  have hcongr : (∫ u in y 1..y 0, Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
          h (Fin.append x ![y 0, u, y 1])) = ∫ u in y 1..y 0,
          Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
            reconN h (Fin.append x ![y 0, u, y 1]) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hy] with u hu _
    rw [hu]
  rw [hcongr]
  have hc : Continuous (timeFourier h) := timeFourier_continuous hint
  have hexpand : ∀ u, reconN h (Fin.append x ![y 0, u, y 1]) =
      ∫ l, (Real.fourierChar (timePairing r (hd l) x) : ℂ) *
        ((Real.fourierChar (timePairing 3 (tl l) ![y 0, u, y 1]) : ℂ) * timeFourier h l) := by
    intro u
    simp only [reconN, Circle.smul_def, smul_eq_mul, pairing_split, char_add]
    refine integral_congr_ae (ae_of_all _ fun l => ?_)
    ring
  simp_rw [hexpand, ← integral_const_mul]
  have hcont : Continuous (Function.uncurry fun (u : ℝ) (l : Fin (r + 3) → ℝ) =>
      Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
        ((Real.fourierChar (timePairing r (hd l) x) : ℂ) *
        ((Real.fourierChar (timePairing 3 (tl l) ![y 0, u, y 1]) : ℂ) * timeFourier h l))) := by
    simp only [Real.fourierChar_apply, pairing_apply, Fin.sum_univ_three]
    have := hc
    have hhd : ∀ i : Fin r, Continuous (fun p : ℝ × (Fin (r + 3) → ℝ) => p.2 (Fin.castAdd 3 i)) :=
      fun i => (continuous_apply _).comp continuous_snd
    have htl : ∀ j : Fin 3, Continuous (fun p : ℝ × (Fin (r + 3) → ℝ) => p.2 (Fin.natAdd r j)) :=
      fun j => (continuous_apply _).comp continuous_snd
    simp only [hd, tl, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e1 : Continuous (fun p : ℝ × (Fin (r + 3) → ℝ) =>
        ∑ i : Fin r, x i * p.2 (Fin.castAdd 3 i)) :=
      continuous_finsetSum _ fun i _ => continuous_const.mul (hhd i)
    fun_prop
  have hint2 : Integrable (Function.uncurry fun (u : ℝ) (l : Fin (r + 3) → ℝ) =>
      Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
        ((Real.fourierChar (timePairing r (hd l) x) : ℂ) *
        ((Real.fourierChar (timePairing 3 (tl l) ![y 0, u, y 1]) : ℂ) * timeFourier h l)))
      ((volume.restrict (Set.uIoc (y 1) (y 0))).prod volume) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (y 1) (y 0))) :=
      ⟨by rw [Measure.restrict_apply_univ, Set.uIoc]; exact measure_Ioc_lt_top⟩
    have h1 : Integrable (fun p : ℝ × (Fin (r + 3) → ℝ) => (1 : ℝ) * ‖timeFourier h p.2‖)
        ((volume.restrict (Set.uIoc (y 1) (y 0))).prod volume) :=
      Integrable.mul_prod (f := fun _ : ℝ => (1 : ℝ)) (g := fun l => ‖timeFourier h l‖)
        (integrable_const _) hhat.norm
    refine h1.mono' hcont.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, Circle.norm_coe, one_mul]
    exact le_rfl
  rw [swap_int _ _ _ hint2]
  refine integral_congr_ae (ae_of_all _ fun l => ?_)
  dsimp only
  have := inner_eq A (tl l) y
  calc (∫ u in y 1..y 0, Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
        ((Real.fourierChar (timePairing r (hd l) x) : ℂ) *
        ((Real.fourierChar (timePairing 3 (tl l) ![y 0, u, y 1]) : ℂ) * timeFourier h l)))
      = (Real.fourierChar (timePairing r (hd l) x) : ℂ) * timeFourier h l *
        (∫ u in y 1..y 0, Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
        (Real.fourierChar (timePairing 3 (tl l) ![y 0, u, y 1]) : ℂ)) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr (fun u _ => ?_)
        ring
    _ = _ := by rw [this]; ring

end WaveTurbulence.Flower.ProtOpsTerm
