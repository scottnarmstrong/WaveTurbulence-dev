/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsTerm.FourierSide

/-! # PROT-OPS-TERM: `reconN (uHat) = ∫ ĥ(l) e(μ·x) atom_{λ}(y) dl`

`uHat A h ζ = ∫ ĥ(ζ_spec, λ) â_λ(ζ_tail) dλ`; its inverse transform is the Fourier synthesis with atoms
`e(μ·x) atom_λ(y)` (not in `L¹` in the spectators, hence the inverse-transform route). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier WaveTurbulence.Flower.ProtTa
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtOpsTerm

variable {r : ℕ}

def uHat (A : ℝ) (h : (Fin (r + 3) → ℝ) → ℂ) (ζ : Fin (r + 2) → ℝ) : ℂ :=
  ∫ l, fh h (hd ζ, l) * timeFourier (atom A l) (tl ζ)

/-- The inverse transform of a frequency-side function (positive character). -/
def invN {n : ℕ} (u : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  ∫ l, Real.fourierChar (timePairing n l x) • u l

theorem reconN_eq_invN {n : ℕ} (h : (Fin n → ℝ) → ℂ) : reconN h = invN (timeFourier h) := rfl

theorem pairing_split' {n m : ℕ} (l ts : Fin (n + m) → ℝ) :
    timePairing (n + m) l ts = timePairing n (hd l) (hd ts) + timePairing m (tl l) (tl ts) := by
  conv_lhs => rw [← append_hd_tl ts]
  exact pairing_split _ _ _

theorem uHat_integrable (A : ℝ) {h : (Fin (r + 3) → ℝ) → ℂ} (hint : Integrable h)
    (hhat : Integrable (timeFourier h)) : Integrable (uHat A h) := by
  have hW := (W_integrable A hint hhat).integral_prod_left
  have e : uHat A h = fun z => (fun p : (Fin r → ℝ) × (Fin 2 → ℝ) => ∫ l, W A h (p, l)) (hd z, tl z) := by
    funext z
    simp [uHat, W]
  rw [e]
  exact (integrable_split _).2 hW

/-- Inversion for an output atom, at every point. -/
theorem atom_recon (A : ℝ) (l : Fin 3 → ℝ) (y : Fin 2 → ℝ) :
    reconN (atom A l) y = atom A l y := by
  obtain ⟨B, hBt, hB⟩ := atom_l1 A
  have hhat : Integrable (timeFourier (atom A l)) := by
    have hm : Measurable (timeFourier (atom A l)) := (timeFourier_continuous (atom_integrable A l)).measurable
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (hB l) hBt
  have := Regref.timeFourier_inversion_at (atom_integrable A l) hhat y
    ((atom_continuous A).comp (by fun_prop : Continuous fun y : Fin 2 → ℝ => (l, y))).continuousAt
  rw [← this]
  simp only [reconN, timeFourier, VectorFourier.fourierIntegral, map_neg, LinearMap.neg_apply, neg_neg]

theorem continuous_char_pair {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) :
    Continuous (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
      ((Real.fourierChar (timePairing n p.1 x + timePairing m p.2 y) : Circle) : ℂ)) := by
  simp only [Real.fourierChar_apply, pairing_apply]
  have e1 : Continuous (fun p : (Fin n → ℝ) × (Fin m → ℝ) => ∑ i, p.1 i * x i) :=
    continuous_finsetSum _ fun i _ => ((continuous_apply i).comp continuous_fst).mul continuous_const
  have e2 : Continuous (fun p : (Fin n → ℝ) × (Fin m → ℝ) => ∑ i, p.2 i * y i) :=
    continuous_finsetSum _ fun i _ => ((continuous_apply i).comp continuous_snd).mul continuous_const
  fun_prop

theorem recon_uHat (A : ℝ) {h : (Fin (r + 3) → ℝ) → ℂ} (hint : Integrable h)
    (hhat : Integrable (timeFourier h)) (ts : Fin (r + 2) → ℝ) :
    invN (uHat A h) ts = ∫ l, timeFourier h l *
      ((Real.fourierChar (timePairing r (hd l) (hd ts)) : ℂ) * atom A (tl l) (tl ts)) := by
  set x : Fin r → ℝ := hd ts with hx
  set y : Fin 2 → ℝ := tl ts with hy
  have hW := W_integrable A hint hhat
  let Fk : ((Fin r → ℝ) × (Fin 2 → ℝ)) × (Fin 3 → ℝ) → ℂ := fun q =>
    ((Real.fourierChar (timePairing r q.1.1 x + timePairing 2 q.1.2 y) : Circle) : ℂ) * W A h q
  have hFk : Integrable Fk (((volume : Measure (Fin r → ℝ)).prod (volume : Measure (Fin 2 → ℝ))).prod
      (volume : Measure (Fin 3 → ℝ))) := by
    refine hW.norm.mono' ?_ (ae_of_all _ fun q => ?_)
    · exact ((continuous_char_pair x y).comp (continuous_fst.comp continuous_fst |>.prodMk
        (continuous_snd.comp continuous_fst))).aestronglyMeasurable.mul
        (measurable_W A hint).aestronglyMeasurable
    · simp [Fk, norm_mul]
  have step1 : invN (uHat A h) ts =
      ∫ p : (Fin r → ℝ) × (Fin 2 → ℝ), ∫ l, Fk (p, l) := by
    refine Eq.trans ?_ (integral_split (fun p : (Fin r → ℝ) × (Fin 2 → ℝ) => ∫ l, Fk (p, l)))
    simp only [invN, Circle.smul_def, smul_eq_mul, uHat]
    refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
    dsimp only
    rw [← integral_const_mul, pairing_split' ζ ts]
    refine integral_congr_ae (ae_of_all _ fun l => ?_)
    simp only [Fk, W]
    ring
  have step2 : (∫ p : (Fin r → ℝ) × (Fin 2 → ℝ), ∫ l, Fk (p, l)) =
      ∫ l, ∫ p : (Fin r → ℝ) × (Fin 2 → ℝ), Fk (p, l) := by
    exact (integral_prod Fk hFk).symm.trans (integral_prod_symm Fk hFk)
  have step3 : ∀ l : Fin 3 → ℝ, ∫ p : (Fin r → ℝ) × (Fin 2 → ℝ), Fk (p, l) =
      (∫ μ : Fin r → ℝ, (Real.fourierChar (timePairing r μ x) : ℂ) * fh h (μ, l)) * atom A l y := by
    intro l
    have e : ∀ p : (Fin r → ℝ) × (Fin 2 → ℝ), Fk (p, l) =
        ((Real.fourierChar (timePairing r p.1 x) : ℂ) * fh h (p.1, l)) *
          ((Real.fourierChar (timePairing 2 p.2 y) : ℂ) * timeFourier (atom A l) p.2) := by
      intro p
      simp only [Fk, W, char_add]
      ring
    simp_rw [e]
    refine Eq.trans (integral_prod_mul (μ := (volume : Measure (Fin r → ℝ)))
      (ν := (volume : Measure (Fin 2 → ℝ)))
      (fun μ => (Real.fourierChar (timePairing r μ x) : ℂ) * fh h (μ, l))
      (fun m => (Real.fourierChar (timePairing 2 m y) : ℂ) * timeFourier (atom A l) m)) ?_
    congr 1
    have := atom_recon A l y
    simp only [reconN, Circle.smul_def, smul_eq_mul] at this
    exact this
  simp_rw [step1, step2, step3]
  set G : (Fin r → ℝ) × (Fin 3 → ℝ) → ℂ := fun z =>
    ((Real.fourierChar (timePairing r z.1 x) : ℂ) * fh h z) * atom A z.2 y with hG
  have hGi : Integrable G (volume.prod volume) := by
    refine (fh_integrable hhat).norm.mul_const ‖chi y‖ |>.mono' ?_ (ae_of_all _ fun z => ?_)
    · have hc : Continuous (fun z : (Fin r → ℝ) × (Fin 3 → ℝ) =>
          ((Real.fourierChar (timePairing r z.1 x) : Circle) : ℂ)) := by
        simp only [Real.fourierChar_apply, pairing_apply]
        have e1 : Continuous (fun z : (Fin r → ℝ) × (Fin 3 → ℝ) => ∑ i, z.1 i * x i) :=
          continuous_finsetSum _ fun i _ => ((continuous_apply i).comp continuous_fst).mul continuous_const
        fun_prop
      exact (hc.aestronglyMeasurable.mul (measurable_fh hint).aestronglyMeasurable).mul
        ((atom_continuous A).comp (continuous_snd.prodMk continuous_const)).aestronglyMeasurable
    · simp only [G, norm_mul, Circle.norm_coe, one_mul]
      exact mul_le_mul_of_nonneg_left (norm_atom_le A _ _) (norm_nonneg _)
  have step4 : (∫ l, (∫ μ : Fin r → ℝ, (Real.fourierChar (timePairing r μ x) : ℂ) * fh h (μ, l)) *
      atom A l y) = ∫ z, G z ∂(volume.prod volume) := by
    rw [integral_prod_symm G hGi]
    refine integral_congr_ae (ae_of_all _ fun l => ?_)
    dsimp only
    simp only [G]
    exact (integral_mul_const _ _).symm
  rw [step4, ← integral_split G]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [G, fh, append_hd_tl]
  ring

end WaveTurbulence.Flower.ProtOpsTerm
