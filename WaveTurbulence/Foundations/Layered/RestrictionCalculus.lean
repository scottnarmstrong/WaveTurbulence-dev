/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Regref.Trace00
public import WaveTurbulence.Foundations.Fourier.Norm00VCutoff
public import WaveTurbulence.Foundations.Incoh.ParameterTimeTranslation
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Calculus of the order-zero restriction norms `𝔛^{θ,0,0}(ℬ)` (TARGET (locnorm), L589)

For the restriction norm `mixedRestrictionNorm00 θ ℬ K h` (an infimum over all extensions agreeing with `h` on
`ℬ × K`):

* `mixedRestrictionNorm00_eq_iInf_finite`: when finite, the infimum may be taken over finite-norm extensions;
* **`mixedRestrictionNorm00_mul_le`**: the product estimate `‖h₁h₂‖ ≤ 2^θ ‖h₁‖ ‖h₂‖` (`θ ≥ 0`, `h₂` continuous in
  time, `ℬ ⊆ closure (interior ℬ)`), through the continuous representatives `Regref.rep`;
* `mixedRestrictionNorm00_mul_momentum_le`: a multiplier `M(v)` independent of time costs `sup |M|`;
* `mixedRestrictionNorm00_translate_le`: time translations;
* `chiUnit`: a smooth bump equal to `1` on `[0, 1]`, for the trace estimates of `Regref.Trace00` on the unit box.

No measurability of higher-derivative integrands is used.
-/

@[expose] public section

open MeasureTheory Set WaveTurbulence.Fourier Metric
open scoped ENNReal ContDiff

namespace WaveTurbulence.Layered

variable {r : ℕ} {V : Type*}

/-! ### Infima of products -/

/-- A bound by all products bounds the product of the infima (all terms finite). -/
theorem le_mul_iInf_mul_iInf {ι κ : Type*} [Nonempty ι] [Nonempty κ] {f : ι → ℝ≥0∞}
    {g : κ → ℝ≥0∞} (hf : ∀ i, f i ≠ ⊤) (hg : ∀ j, g j ≠ ⊤) {c Z : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : ∀ i j, Z ≤ c * f i * g j) : Z ≤ c * (⨅ i, f i) * ⨅ j, g j := by
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  have hG : (⨅ j, g j) ≠ ⊤ := ne_top_of_le_ne_top (hg j₀) (iInf_le _ j₀)
  rw [ENNReal.mul_iInf (fun h => absurd h hc), ENNReal.iInf_mul (fun h => absurd h hG)]
  refine le_iInf fun i => ?_
  rw [ENNReal.mul_iInf (fun h => absurd h (ENNReal.mul_ne_top hc (hf i)))]
  exact le_iInf fun j => h i j

/-! ### Finite extensions -/

/-- The finite-norm extensions of `h` on `ℬ × K`. -/
abbrev FiniteExt (θ : ℝ) (B : Set (Fin r → ℝ)) (K : Set V) (h : (Fin r → ℝ) → V → ℂ) : Type _ :=
  {G : (Fin r → ℝ) → V → ℂ // (∀ t ∈ B, ∀ v ∈ K, G t v = h t v) ∧ mixedFourierNorm00 θ G < ⊤}

theorem mixedRestrictionNorm00_eq_iInf_finite (θ : ℝ) (B : Set (Fin r → ℝ)) (K : Set V)
    (h : (Fin r → ℝ) → V → ℂ) :
    mixedRestrictionNorm00 θ B K (fun t v => h t v) =
      ⨅ G : FiniteExt θ B K h, mixedFourierNorm00 θ G.1 := by
  rw [mixedRestrictionNorm00_eq_agreement]
  apply le_antisymm
  · exact le_iInf fun G => iInf₂_le G.1 G.2.1
  · refine le_iInf₂ fun G hG => ?_
    by_cases hN : mixedFourierNorm00 θ G < ⊤
    · exact iInf_le_of_le ⟨G, hG, hN⟩ le_rfl
    · rw [not_lt, top_le_iff] at hN
      rw [hN]
      exact le_top

theorem nonempty_finiteExt {θ : ℝ} {B : Set (Fin r → ℝ)} {K : Set V} {h : (Fin r → ℝ) → V → ℂ}
    (hfin : mixedRestrictionNorm00 θ B K (fun t v => h t v) < ⊤) : Nonempty (FiniteExt θ B K h) := by
  rw [mixedRestrictionNorm00_eq_agreement] at hfin
  obtain ⟨G, hG⟩ := iInf_lt_iff.mp hfin
  obtain ⟨hGa, hGn⟩ := iInf_lt_iff.mp hG
  exact ⟨⟨G, hGa, hGn⟩⟩

/-! ### Products -/

/-- The continuous representative of a finite-norm family has the same norm. -/
theorem mixedFourierNorm00_rep_eq {θ : ℝ} (hθ : 0 ≤ θ) {G : (Fin r → ℝ) → V → ℂ}
    (hG : mixedFourierNorm00 θ G < ⊤) :
    mixedFourierNorm00 θ (fun t v => Regref.rep (fun u => G u v) t) = mixedFourierNorm00 θ G := by
  have hslice : ∀ v, timeFourierNorm θ (fun u => G u v) < ⊤ := fun v =>
    (timeFourierNorm_slice_le_mixedFourierNorm00 θ G v).trans_lt hG
  have hrep := fun v => Regref.rep_props hθ (hslice v)
  rw [mixedFourierNorm00_eq_lintegral (fun v => (hrep v).2.2.1),
    mixedFourierNorm00_eq_lintegral (fun v => integrable_of_mixedFourierNorm00_lt_top hG v)]
  refine lintegral_congr fun ξ => ?_
  unfold mixedFourierEnvelope00
  congr 1
  refine iSup_congr fun v => ?_
  have e := congrFun (hrep v).2.2.2.1 ξ
  exact congrArg _ e

/-- **The product estimate for restriction norms.** -/
theorem mixedRestrictionNorm00_mul_le {θ : ℝ} (hθ : 0 ≤ θ) {B : Set (Fin r → ℝ)}
    (hB : ∀ t ∈ B, t ∈ closure (interior B)) (K : Set V) (h₁ h₂ : (Fin r → ℝ) → V → ℂ)
    (hc : ∀ v ∈ K, Continuous fun t => h₂ t v)
    (hfin₁ : mixedRestrictionNorm00 θ B K (fun t v => h₁ t v) < ⊤)
    (hfin₂ : mixedRestrictionNorm00 θ B K (fun t v => h₂ t v) < ⊤) :
    mixedRestrictionNorm00 θ B K (fun t v => h₁ t v * h₂ t v) ≤
      ENNReal.ofReal (2 ^ θ) * mixedRestrictionNorm00 θ B K (fun t v => h₁ t v) *
        mixedRestrictionNorm00 θ B K (fun t v => h₂ t v) := by
  have := nonempty_finiteExt hfin₁
  have := nonempty_finiteExt hfin₂
  rw [mixedRestrictionNorm00_eq_iInf_finite θ B K h₁, mixedRestrictionNorm00_eq_iInf_finite θ B K h₂]
  refine le_mul_iInf_mul_iInf (fun G => G.2.2.ne) (fun G => G.2.2.ne) ENNReal.ofReal_ne_top
    fun G₁ G₂ => ?_
  have hslice : ∀ v, timeFourierNorm θ (fun u => G₂.1 u v) < ⊤ := fun v =>
    (timeFourierNorm_slice_le_mixedFourierNorm00 θ G₂.1 v).trans_lt G₂.2.2
  let G₂' : (Fin r → ℝ) → V → ℂ := fun t v => Regref.rep (fun u => G₂.1 u v) t
  have hcont : ∀ v, Continuous fun t => G₂' t v := fun v => (Regref.rep_props hθ (hslice v)).1
  have hN : mixedFourierNorm00 θ G₂' = mixedFourierNorm00 θ G₂.1 := mixedFourierNorm00_rep_eq hθ G₂.2.2
  have hagree : ∀ t ∈ B, ∀ v ∈ K, G₂' t v = h₂ t v := fun t ht v hv =>
    Regref.rep_eq_of_mem_closure_interior hθ (hslice v) (fun u hu => G₂.2.1 u hu v hv) (hc v hv) (hB t ht)
  refine (mixedRestrictionNorm00_eq_agreement θ B K (fun t v => h₁ t v * h₂ t v)).le.trans ?_
  refine (iInf₂_le (fun t v => G₁.1 t v * G₂' t v) fun t ht v hv => by
    show G₁.1 t v * G₂' t v = h₁ t v * h₂ t v
    rw [G₁.2.1 t ht v hv, hagree t ht v hv]).trans ?_
  rw [← hN]
  exact mixedFourierNorm00_mul_le hθ hcont G₁.2.2 (hN ▸ G₂.2.2)

/-! ### Multipliers independent of time -/

theorem mixedFourierNorm00_mul_momentum_le (θ : ℝ) (M : V → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ v, ‖M v‖ ≤ C) (F : (Fin r → ℝ) → V → ℂ) :
    mixedFourierNorm00 θ (fun t v => M v * F t v) ≤ ENNReal.ofReal C * mixedFourierNorm00 θ F := by
  rcases hC.eq_or_lt with hC0 | hCpos
  · have hM0 : ∀ v, M v = 0 := fun v => norm_le_zero_iff.mp (hC0 ▸ hM v)
    have h0 : (fun t v => M v * F t v) = fun (_ : Fin r → ℝ) (_ : V) => (0 : ℂ) := by
      funext t v
      rw [hM0 v, zero_mul]
    rw [h0]
    simp
  by_cases hi : ∀ v, Integrable fun t => F t v
  · rw [mixedFourierNorm00_eq_lintegral (fun v => (hi v).const_mul (M v)),
      mixedFourierNorm00_eq_lintegral hi, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ξ => ?_
    have hb : mixedFourierEnvelope00 (fun t v => M v * F t v) ξ ≤
        ENNReal.ofReal C * mixedFourierEnvelope00 F ξ := by
      unfold mixedFourierEnvelope00
      refine iSup_le fun v => ?_
      have he := congrFun (timeFourier_smul (M v) (fun t => F t v)) ξ
      simp only [smul_eq_mul] at he
      rw [he, enorm_mul, ENNReal.mul_iSup]
      refine le_iSup_of_le v (mul_le_mul_left ?_ _)
      simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hM v)
    calc timeWeight θ ξ * mixedFourierEnvelope00 (fun t v => M v * F t v) ξ
        ≤ timeWeight θ ξ * (ENNReal.ofReal C * mixedFourierEnvelope00 F ξ) := mul_le_mul_right hb _
      _ = _ := by ring
  · rw [mixedFourierNorm00_of_not_integrable hi,
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hCpos))]
    exact le_top

theorem mixedRestrictionNorm00_mul_momentum_le (θ : ℝ) (B : Set (Fin r → ℝ)) (K : Set V)
    (M : V → ℂ) {C : ℝ} (hC : 0 ≤ C) (hM : ∀ v ∈ K, ‖M v‖ ≤ C) (h : (Fin r → ℝ) → V → ℂ) :
    mixedRestrictionNorm00 θ B K (fun t v => M v * h t v) ≤
      ENNReal.ofReal C * mixedRestrictionNorm00 θ B K (fun t v => h t v) := by
  classical
  let M' : V → ℂ := fun v => if v ∈ K then M v else 0
  have hM' : ∀ v, ‖M' v‖ ≤ C := fun v => by
    by_cases hv : v ∈ K
    · simp only [M', hv, ↓reduceIte]
      exact hM v hv
    · simp only [M', hv, ↓reduceIte, norm_zero]
      exact hC
  rcases hC.eq_or_lt with hC0 | hCpos
  · have h0 : ∀ t ∈ B, ∀ v ∈ K, M v * h t v = 0 := fun t _ v hv => by
      have hm := hM v hv
      rw [← hC0] at hm
      rw [norm_le_zero_iff.mp hm, zero_mul]
    rw [mixedRestrictionNorm00_eq_agreement θ B K (fun t v => M v * h t v)]
    refine (iInf₂_le (fun _ _ => (0 : ℂ)) fun t ht v hv => (h0 t ht v hv).symm).trans ?_
    simp
  rw [mixedRestrictionNorm00_eq_agreement θ B K (fun t v => M v * h t v),
    mixedRestrictionNorm00_eq_agreement θ B K h,
    ENNReal.mul_iInf_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr hCpos)) ENNReal.ofReal_ne_top]
  refine le_iInf fun G => ?_
  rw [ENNReal.mul_iInf_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr hCpos)) ENNReal.ofReal_ne_top]
  refine le_iInf fun hG => ?_
  refine (iInf₂_le (fun t v => M' v * G t v) fun t ht v hv => by
    show M' v * G t v = M v * h t v
    simp only [M', hv, ↓reduceIte]
    rw [hG t ht v hv]).trans ?_
  exact mixedFourierNorm00_mul_momentum_le θ M' hC hM' G

/-! ### Translations -/

theorem mixedRestrictionNorm00_translate_le (θ : ℝ) {B B' : Set (Fin r → ℝ)} (K : Set V)
    (h : (Fin r → ℝ) → V → ℂ) (a : Fin r → ℝ) (hBB : ∀ t ∈ B, t + a ∈ B') :
    mixedRestrictionNorm00 θ B K (fun t v => h (t + a) v) ≤
      mixedRestrictionNorm00 θ B' K (fun t v => h t v) := by
  rw [mixedRestrictionNorm00_eq_agreement θ B K (fun t v => h (t + a) v),
    mixedRestrictionNorm00_eq_agreement θ B' K h]
  refine le_iInf₂ fun G hG => ?_
  refine (iInf₂_le (fun t v => G (t + a) v) fun t ht v hv => hG _ (hBB t ht) v hv).trans ?_
  by_cases hi : ∀ v, Integrable fun t => G t v
  · exact (Incoh.mixedFourierNorm00_translate_of_integrable θ G a hi).le
  · rw [mixedFourierNorm00_of_not_integrable hi]
    exact le_top

/-! ### A unit cutoff -/

/-- A smooth bump on `ℝ`, equal to `1` on `[0, 1]`. -/
noncomputable def unitBump : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- `χ₀ = 1` on `[0, 1]`, smooth and compactly supported. -/
noncomputable def chiUnit : ℝ → ℝ := ⇑unitBump

theorem chiUnit_contDiff : ContDiff ℝ ∞ chiUnit := unitBump.contDiff

theorem chiUnit_hasCompactSupport : HasCompactSupport chiUnit := unitBump.hasCompactSupport

theorem chiUnit_eq_one {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : chiUnit x = 1 := by
  apply unitBump.one_of_mem_closedBall
  rw [Real.closedBall_eq_Icc]
  change x ∈ Icc (1 / 2 - 1 / 2) (1 / 2 + 1 / 2)
  norm_num
  exact hx

theorem coordinateCutoff_chiUnit_eq_one {t : Fin r → ℝ} (ht : ∀ i, t i ∈ Icc (0 : ℝ) 1) :
    coordinateCutoff chiUnit t = 1 := by
  unfold coordinateCutoff
  refine Finset.prod_eq_one fun i _ => ?_
  rw [chiUnit_eq_one (ht i), Complex.ofReal_one]

end WaveTurbulence.Layered
