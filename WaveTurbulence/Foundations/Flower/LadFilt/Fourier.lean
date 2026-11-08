/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.LadFilt.Defs
public import WaveTurbulence.Foundations.Flower.LadFilt.CoreT

/-! # C3 LAD-FILT: filters are time translations (o83 Lemma T, o75 Lemma F step 1)

For a Schwartz profile `ψ`, Fourier inversion gives `ψ(Ω/R) = ∫ 𝓕ψ(ξ) e^{2πiξΩ/R} dξ`. Since the time phase of an
atom is `e^{πi(ζ δ L^{2γ} Ω + f) t}`, the factor `e^{2πiξΩ/R}` is a translation of the atom's time by
`τ = 2ζξ/(δ L^{2γ} R)` times the unimodular constant `e^{-πifτ}` (`phase_identity`). Hence the filtered lattice sum at
`t` is the `𝓕ψ`-average of unfiltered sums at `t + τ(ξ)` (`filtered_sum_eq`), and the time-L¹ norm over the layer box
is at most the `|𝓕ψ|`-average of the time-L¹ norms over the translated boxes (`filt_L1_le`). If the translated
bound grows at most like `∏ (1 + |ξ_a|)²`, the cost is `∏ 𝔟(ψ_a)`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.LadFilt
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay MeasureTheory Set Finset
open scoped FourierTransform

/-! ### Schwartz profiles -/

/-- Fourier inversion for a Schwartz profile, in the form used below. -/
lemma schwartz_inv (ψ : SchwartzMap ℝ ℂ) (y : ℝ) :
    ψ y = ∫ ξ : ℝ, Complex.exp (((2 * Real.pi * (ξ * y) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑ψ) ξ := by
  calc ψ y = (𝓕⁻ (𝓕 ψ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) y := by
        rw [FourierTransform.fourierInv_fourier_eq]
    _ = 𝓕⁻ (⇑(𝓕 ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ) y := by rw [SchwartzMap.fourierInv_coe]
    _ = _ := by
      rw [Real.fourierInv_eq', SchwartzMap.fourier_coe]
      simp only [Real.inner_apply, smul_eq_mul]

lemma integrable_fourier (ψ : SchwartzMap ℝ ℂ) : Integrable (𝓕 (⇑ψ)) := by
  rw [← SchwartzMap.fourier_coe]; exact (𝓕 ψ).integrable

lemma continuous_fourier (ψ : SchwartzMap ℝ ℂ) : Continuous (𝓕 (⇑ψ)) := by
  rw [← SchwartzMap.fourier_coe]; exact (𝓕 ψ).continuous

lemma integrable_filterB (ψ : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ => (1 + |ξ|) ^ 2 * ‖𝓕 (⇑ψ) ξ‖) := by
  have h0 := (𝓕 ψ).integrable_pow_mul volume 0
  have h1 := (𝓕 ψ).integrable_pow_mul volume 1
  have h2 := (𝓕 ψ).integrable_pow_mul volume 2
  have e : (fun ξ : ℝ => (1 + |ξ|) ^ 2 * ‖𝓕 (⇑ψ) ξ‖) = fun ξ =>
      ‖ξ‖ ^ 0 * ‖(𝓕 ψ) ξ‖ + 2 * (‖ξ‖ ^ 1 * ‖(𝓕 ψ) ξ‖) + ‖ξ‖ ^ 2 * ‖(𝓕 ψ) ξ‖ := by
    funext ξ
    rw [SchwartzMap.fourier_coe, Real.norm_eq_abs]
    ring
  rw [e]
  exact (h0.add (h1.const_mul 2)).add h2

lemma filterB_nonneg (ψ : ℝ → ℂ) : 0 ≤ filterB ψ :=
  integral_nonneg (fun ξ => mul_nonneg (sq_nonneg _) (norm_nonneg _))

variable {w d : ℕ} {G : Garden w}

/-! ### The translation -/

/-- The time shift of filter frequency `ξ_a` at atom `a`: `τ_a = 2 ζ_a ξ_a / (c R_a)`, `c = δ L^{2γ}`. -/
noncomputable def filtShift (S : Finset (GBranch G.tree)) (c : ℝ) (Rv : GBranch G.tree → ℝ) (ξ : S → ℝ) :
    S → ℝ :=
  fun a => 2 * ((((G.sign a.1.toNode : ℤˣ) : ℤ) : ℝ)) * ξ a / (c * Rv a.1)

/-- The unimodular constant of the translation, `e^{-πi f_a τ_a}`. -/
noncomputable def filtPhase (D : SplicedKernelData G d) (S : Finset (GBranch G.tree)) (c : ℝ)
    (Rv : GBranch G.tree → ℝ) (ξ : S → ℝ) (a : S) : ℂ :=
  Complex.exp ((((-(Real.pi * D.frequency a.1 * filtShift S c Rv ξ a)) : ℝ) : ℂ) * Complex.I)

/-- The filter amplitude `∏_a 𝓕ψ_a(ξ_a) e^{-πi f_a τ_a}`. -/
noncomputable def filtAmp (ψ : GBranch G.tree → SchwartzMap ℝ ℂ) (D : SplicedKernelData G d)
    (S : Finset (GBranch G.tree)) (c : ℝ) (Rv : GBranch G.tree → ℝ) (ξ : S → ℝ) : ℂ :=
  ∏ a : S, 𝓕 (⇑(ψ a.1)) (ξ a) * filtPhase D S c Rv ξ a

lemma norm_filtPhase (D : SplicedKernelData G d) (S : Finset (GBranch G.tree)) (c : ℝ)
    (Rv : GBranch G.tree → ℝ) (ξ : S → ℝ) (a : S) : ‖filtPhase D S c Rv ξ a‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma norm_filtAmp (ψ : GBranch G.tree → SchwartzMap ℝ ℂ) (D : SplicedKernelData G d)
    (S : Finset (GBranch G.tree)) (c : ℝ) (Rv : GBranch G.tree → ℝ) (ξ : S → ℝ) :
    ‖filtAmp ψ D S c Rv ξ‖ = ∏ a : S, ‖𝓕 (⇑(ψ a.1)) (ξ a)‖ := by
  unfold filtAmp
  rw [norm_prod]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  rw [norm_mul, norm_filtPhase, mul_one]

lemma continuous_filtShift (S : Finset (GBranch G.tree)) (c : ℝ) (Rv : GBranch G.tree → ℝ) :
    Continuous (filtShift S c Rv) := by
  unfold filtShift
  exact continuous_pi (fun a => ((continuous_const.mul (continuous_apply a)).div_const _))

lemma continuous_filtAmp (ψ : GBranch G.tree → SchwartzMap ℝ ℂ) (D : SplicedKernelData G d)
    (S : Finset (GBranch G.tree)) (c : ℝ) (Rv : GBranch G.tree → ℝ) :
    Continuous (filtAmp ψ D S c Rv) := by
  unfold filtAmp filtPhase
  refine continuous_finsetProd _ (fun a _ => ?_)
  refine ((continuous_fourier (ψ a.1)).comp (continuous_apply a)).mul ?_
  refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
  refine Complex.continuous_ofReal.comp ?_
  exact ((continuous_const.mul ((continuous_apply a).comp (continuous_filtShift S c Rv)))).neg

/-- One atom: the filter character is a translation of the time. -/
lemma atom_identity (u : ℤˣ) (δ Lg Ω f R ξ t : ℝ) (F : ℂ) (hc : δ * Lg ≠ 0) (hR : R ≠ 0) :
    Complex.exp (((2 * Real.pi * (ξ * (Ω / R)) : ℝ) : ℂ) * Complex.I) * F *
      Complex.exp (((Real.pi * ((((u : ℤ) : ℝ) * δ * Lg * Ω + f) * t) : ℝ) : ℂ) * Complex.I) =
    F * Complex.exp ((((-(Real.pi * f * (2 * ((u : ℤ) : ℝ) * ξ / (δ * Lg * R)))) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((Real.pi * ((((u : ℤ) : ℝ) * δ * Lg * Ω + f) *
        (t + 2 * ((u : ℤ) : ℝ) * ξ / (δ * Lg * R))) : ℝ) : ℂ) * Complex.I) := by
  have hδ : δ ≠ 0 := left_ne_zero_of_mul hc
  have hLg : Lg ≠ 0 := right_ne_zero_of_mul hc
  have key : 2 * Real.pi * (ξ * (Ω / R)) + Real.pi * ((((u : ℤ) : ℝ) * δ * Lg * Ω + f) * t) =
      -(Real.pi * f * (2 * ((u : ℤ) : ℝ) * ξ / (δ * Lg * R))) +
        Real.pi * ((((u : ℤ) : ℝ) * δ * Lg * Ω + f) * (t + 2 * ((u : ℤ) : ℝ) * ξ / (δ * Lg * R))) := by
    rcases Int.units_eq_one_or u with h | h <;> subst h <;>
      simp only [Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg] <;> field_simp <;> ring
  have e1 : ∀ x y : ℝ, Complex.exp (((x : ℝ) : ℂ) * Complex.I) * Complex.exp (((y : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((x + y : ℝ) : ℂ) * Complex.I) := by
    intro x y
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc Complex.exp (((2 * Real.pi * (ξ * (Ω / R)) : ℝ) : ℂ) * Complex.I) * F *
        Complex.exp (((Real.pi * ((((u : ℤ) : ℝ) * δ * Lg * Ω + f) * t) : ℝ) : ℂ) * Complex.I)
      = F * (Complex.exp (((2 * Real.pi * (ξ * (Ω / R)) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((Real.pi * ((((u : ℤ) : ℝ) * δ * Lg * Ω + f) * t) : ℝ) : ℂ) * Complex.I)) := by ring
    _ = F * Complex.exp (((-(Real.pi * f * (2 * ((u : ℤ) : ℝ) * ξ / (δ * Lg * R))) +
        Real.pi * ((((u : ℤ) : ℝ) * δ * Lg * Ω + f) * (t + 2 * ((u : ℤ) : ℝ) * ξ / (δ * Lg * R))) : ℝ) : ℂ) *
          Complex.I) := by rw [e1, key]
    _ = _ := by rw [← e1]; ring

/-- **Lemma T (pointwise).** The product of filter characters times the time phase is the time phase at the
translated times, times the translation constants. -/
lemma phase_identity (D : SplicedKernelData G d) (S : Finset (GBranch G.tree)) (L γ δ : ℝ) (base : Mom d)
    (Rv : GBranch G.tree → ℝ) (hR : ∀ a, Rv a ≠ 0) (hc : δ * L ^ (2 * γ) ≠ 0)
    (z : GNode G.tree → (Fin d → ℤ)) (t ξ : S → ℝ) (Fv : S → ℂ) :
    (∏ a : S, Complex.exp (((2 * Real.pi * (ξ a * (omegaNode G (cosetDecoration G L base z) a.1 / Rv a.1)) :
        ℝ) : ℂ) * Complex.I) * Fv a) * ladderPhase D S L γ δ base z t =
      (∏ a : S, Fv a * filtPhase D S (δ * L ^ (2 * γ)) Rv ξ a) *
        ladderPhase D S L γ δ base z (t + filtShift S (δ * L ^ (2 * γ)) Rv ξ) := by
  unfold ladderPhase
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  unfold filtPhase filtShift
  simp only [Pi.add_apply]
  exact atom_identity _ δ (L ^ (2 * γ)) _ _ _ _ _ _ hc (hR a.1)

lemma integrable_prod_norm_fourier (ψ : GBranch G.tree → SchwartzMap ℝ ℂ) (S : Finset (GBranch G.tree)) :
    Integrable (fun ξ : S → ℝ => ∏ a : S, ‖𝓕 (⇑(ψ a.1)) (ξ a)‖) :=
  Integrable.fintype_prod (f := fun (a : S) (x : ℝ) => ‖𝓕 (⇑(ψ a.1)) x‖)
    (fun a => (integrable_fourier (ψ a.1)).norm)

lemma integrable_prod_filterB (ψ : GBranch G.tree → SchwartzMap ℝ ℂ) (S : Finset (GBranch G.tree)) :
    Integrable (fun ξ : S → ℝ => ∏ a : S, (1 + |ξ a|) ^ 2 * ‖𝓕 (⇑(ψ a.1)) (ξ a)‖) :=
  Integrable.fintype_prod (f := fun (a : S) (x : ℝ) => (1 + |x|) ^ 2 * ‖𝓕 (⇑(ψ a.1)) x‖)
    (fun a => integrable_filterB (ψ a.1))

lemma integral_prod_filterB (ψ : GBranch G.tree → SchwartzMap ℝ ℂ) (S : Finset (GBranch G.tree)) :
    ∫ ξ : S → ℝ, ∏ a : S, (1 + |ξ a|) ^ 2 * ‖𝓕 (⇑(ψ a.1)) (ξ a)‖ = ∏ a ∈ S, filterB ⇑(ψ a) := by
  rw [integral_fintype_prod_volume_eq_prod (fun (a : S) (x : ℝ) => (1 + |x|) ^ 2 * ‖𝓕 (⇑(ψ a.1)) x‖)]
  exact Finset.prod_coe_sort S (fun a => filterB ⇑(ψ a))

/-- **Lemma T (one decoration).** -/
lemma prod_filter_eq_integral (ψ : GBranch G.tree → SchwartzMap ℝ ℂ) (D : SplicedKernelData G d)
    (S : Finset (GBranch G.tree)) (L γ δ : ℝ) (base : Mom d) (Rv : GBranch G.tree → ℝ) (hR : ∀ a, Rv a ≠ 0)
    (hc : δ * L ^ (2 * γ) ≠ 0) (z : GNode G.tree → (Fin d → ℤ)) (t : S → ℝ) :
    (∏ a ∈ S, ψ a (omegaNode G (cosetDecoration G L base z) a / Rv a)) * ladderPhase D S L γ δ base z t =
      ∫ ξ : S → ℝ, filtAmp ψ D S (δ * L ^ (2 * γ)) Rv ξ *
        ladderPhase D S L γ δ base z (t + filtShift S (δ * L ^ (2 * γ)) Rv ξ) := by
  set g : S → ℝ → ℂ := fun a x => Complex.exp (((2 * Real.pi *
    (x * (omegaNode G (cosetDecoration G L base z) a.1 / Rv a.1)) : ℝ) : ℂ) * Complex.I) *
      𝓕 (⇑(ψ a.1)) x with hg
  have h1 : ∏ a ∈ S, ψ a (omegaNode G (cosetDecoration G L base z) a / Rv a) =
      ∫ ξ : S → ℝ, ∏ a : S, g a (ξ a) := by
    calc ∏ a ∈ S, ψ a (omegaNode G (cosetDecoration G L base z) a / Rv a)
        = ∏ a : S, ψ a.1 (omegaNode G (cosetDecoration G L base z) a.1 / Rv a.1) :=
          (Finset.prod_coe_sort S (fun a => ψ a (omegaNode G (cosetDecoration G L base z) a / Rv a))).symm
      _ = ∏ a : S, ∫ x : ℝ, g a x := Finset.prod_congr rfl (fun a _ => schwartz_inv _ _)
      _ = ∫ ξ : S → ℝ, ∏ a : S, g a (ξ a) := (integral_fintype_prod_volume_eq_prod g).symm
  rw [h1, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
  exact phase_identity D S L γ δ base Rv hR hc z t ξ (fun a => 𝓕 (⇑(ψ a.1)) (ξ a))

/-- The translated summands are integrable in the filter frequencies. -/
lemma integrable_filt_term (ψ : GBranch G.tree → SchwartzMap ℝ ℂ) (D : SplicedKernelData G d)
    (S : Finset (GBranch G.tree)) (L γ δ : ℝ) (base : Mom d) (Rv : GBranch G.tree → ℝ)
    (z : GNode G.tree → (Fin d → ℤ)) (t : S → ℝ) :
    Integrable (fun ξ : S → ℝ => filtAmp ψ D S (δ * L ^ (2 * γ)) Rv ξ *
      ladderPhase D S L γ δ base z (t + filtShift S (δ * L ^ (2 * γ)) Rv ξ)) := by
  refine (integrable_prod_norm_fourier ψ S).mono' ?_ (Filter.Eventually.of_forall (fun ξ => ?_))
  · refine Continuous.aestronglyMeasurable ?_
    exact (continuous_filtAmp ψ D S _ Rv).mul ((continuous_ladderPhase D S L γ δ base z).comp
      (continuous_const.add (continuous_filtShift S _ Rv)))
  · rw [norm_mul, norm_ladderPhase, mul_one, norm_filtAmp]

end WaveTurbulence.Flower.LadFilt
