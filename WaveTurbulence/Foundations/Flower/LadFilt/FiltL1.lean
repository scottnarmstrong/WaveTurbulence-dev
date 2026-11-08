/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.LadFilt.Fourier

/-! # C3 LAD-FILT: the filtered time-L¹ norm as an average over translated boxes (o83 (4.5))

`filt_L1_le`: if the unfiltered time-L¹ norm over every translated box `𝔅 + τ` is at most `Wt(τ) B₀`, and the
weight of the translation `τ(ξ)` of frequencies `ξ` is at most `∏_a (1 + |ξ_a|)²`, then the filtered time-L¹ norm
over the layer box is at most `∏_a 𝔟(ψ_a) · B₀`. Steps: Lemma T per decoration (`prod_filter_eq_integral`), sum
over decorations, Minkowski, Fubini (`integral_integral_swap`), translation invariance of Lebesgue measure, and
`∫ ∏_a (1+|ξ_a|)² |𝓕ψ_a(ξ_a)| = ∏_a 𝔟(ψ_a)`.

`ladderWt_filtShift_le` verifies the weight hypothesis for the ladder weight of `CoreT` (`κ = δ L^{2γ}/2`,
`R_a ≥ 1`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.LadFilt
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay MeasureTheory Set Finset
open scoped FourierTransform

variable {w d : ℕ} {G : Garden w}

lemma timeBox_shift_mem (layer : GBranch G.tree → ℕ) (S : Finset (GBranch G.tree)) (τ t : S → ℝ) :
    t + τ ∈ timeBoxT G layer S τ ↔ t ∈ LadderDecay.timeBox G layer S := by
  simp only [timeBoxT, LadderDecay.timeBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
    Pi.add_apply]
  constructor
  · intro h a
    obtain ⟨h1, h2⟩ := h a
    constructor <;> linarith
  · intro h a
    obtain ⟨h1, h2⟩ := h a
    constructor <;> linarith

/-- Translation of the layer box. -/
lemma integral_timeBox_shift (layer : GBranch G.tree → ℕ) (S : Finset (GBranch G.tree))
    (f : (S → ℝ) → ℝ) (τ : S → ℝ) :
    ∫ t in LadderDecay.timeBox G layer S, f (t + τ) = ∫ t in timeBoxT G layer S τ, f t := by
  have hm1 : MeasurableSet (LadderDecay.timeBox G layer S) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hm2 : MeasurableSet (timeBoxT G layer S τ) := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  rw [← integral_indicator hm1, ← integral_indicator hm2,
    ← integral_add_right_eq_self ((timeBoxT G layer S τ).indicator f) τ]
  congr 1
  funext t
  by_cases ht : t ∈ LadderDecay.timeBox G layer S
  · rw [indicator_of_mem ht, indicator_of_mem ((timeBox_shift_mem layer S τ t).mpr ht)]
  · rw [indicator_of_notMem ht, indicator_of_notMem (fun h => ht ((timeBox_shift_mem layer S τ t).mp h))]

/-- **The filtered sum is an average of translated sums** (o83 (4.5), before taking norms). -/
lemma filtered_sum_eq {Z : Type*} (ψ : GBranch G.tree → SchwartzMap ℝ ℂ) (D : SplicedKernelData G d)
    (S : Finset (GBranch G.tree)) (L γ δ : ℝ) (base : Mom d) (Rv : GBranch G.tree → ℝ) (hR : ∀ a, Rv a ≠ 0)
    (hc : δ * L ^ (2 * γ) ≠ 0) (T0 : Finset Z) (dec : Z → GNode G.tree → (Fin d → ℤ)) (W : Z → ℂ)
    (t : S → ℝ) :
    ∑ z ∈ T0, (∏ a ∈ S, ψ a (omegaNode G (cosetDecoration G L base (dec z)) a / Rv a)) * W z *
        ladderPhase D S L γ δ base (dec z) t =
      ∫ ξ : S → ℝ, filtAmp ψ D S (δ * L ^ (2 * γ)) Rv ξ *
        ∑ z ∈ T0, W z * ladderPhase D S L γ δ base (dec z) (t + filtShift S (δ * L ^ (2 * γ)) Rv ξ) := by
  have hz : ∀ z ∈ T0, (∏ a ∈ S, ψ a (omegaNode G (cosetDecoration G L base (dec z)) a / Rv a)) * W z *
      ladderPhase D S L γ δ base (dec z) t =
      ∫ ξ : S → ℝ, W z * (filtAmp ψ D S (δ * L ^ (2 * γ)) Rv ξ *
        ladderPhase D S L γ δ base (dec z) (t + filtShift S (δ * L ^ (2 * γ)) Rv ξ)) := by
    intro z _
    rw [integral_const_mul, ← prod_filter_eq_integral ψ D S L γ δ base Rv hR hc (dec z) t]
    ring
  rw [Finset.sum_congr rfl hz, ← integral_finsetSum]
  · refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    ring
  · intro z _
    exact (integrable_filt_term ψ D S L γ δ base Rv (dec z) t).const_mul (W z)

/-- **Filtered time-L¹ norm ≤ `∏ 𝔟(ψ_a)` × translated bound.** -/
theorem filt_L1_le {Z : Type*} (ψ : GBranch G.tree → SchwartzMap ℝ ℂ) (D : SplicedKernelData G d)
    (S : Finset (GBranch G.tree)) (L γ δ : ℝ) (base : Mom d) (Rv : GBranch G.tree → ℝ)
    (hRv : ∀ a, 1 ≤ Rv a) (hc : 0 < δ * L ^ (2 * γ)) (T0 : Finset Z) (dec : Z → GNode G.tree → (Fin d → ℤ))
    (W : Z → ℂ) (k0 B0 : ℝ) (hk0 : 0 ≤ k0) (hB0 : 0 ≤ B0) (Wt : (S → ℝ) → ℝ)
    (hK : ∀ τ : S → ℝ, k0 * ∫ t in timeBoxT G D.layer S τ,
      ‖∑ z ∈ T0, W z * ladderPhase D S L γ δ base (dec z) t‖ ≤ Wt τ * B0)
    (hWt : ∀ ξ : S → ℝ, Wt (filtShift S (δ * L ^ (2 * γ)) Rv ξ) ≤ ∏ a : S, (1 + |ξ a|) ^ 2) :
    k0 * ∫ t in LadderDecay.timeBox G D.layer S,
        ‖∑ z ∈ T0, (∏ a ∈ S, ψ a (omegaNode G (cosetDecoration G L base (dec z)) a / Rv a)) * W z *
          ladderPhase D S L γ δ base (dec z) t‖ ≤ (∏ a ∈ S, filterB ⇑(ψ a)) * B0 := by
  have hR : ∀ a, Rv a ≠ 0 := fun a => (lt_of_lt_of_le one_pos (hRv a)).ne'
  set c := δ * L ^ (2 * γ) with hcdef
  set box := LadderDecay.timeBox G D.layer S with hbox
  set Sf : (S → ℝ) → ℂ := fun t => ∑ z ∈ T0, W z * ladderPhase D S L γ δ base (dec z) t with hSf
  have hSc : Continuous Sf :=
    continuous_finsetSum _ (fun z _ => continuous_const.mul (continuous_ladderPhase D S L γ δ base (dec z)))
  set gF : (S → ℝ) → ℝ := fun ξ => ∏ a : S, ‖𝓕 (⇑(ψ a.1)) (ξ a)‖ with hgF
  have hgFc : Continuous gF :=
    continuous_finsetProd _ (fun a _ => ((continuous_fourier (ψ a.1)).comp (continuous_apply a)).norm)
  have hgFi : Integrable gF := integrable_prod_norm_fourier ψ S
  have hgF0 : ∀ ξ, 0 ≤ gF ξ := fun ξ => Finset.prod_nonneg (fun a _ => norm_nonneg _)
  set τf := filtShift S c Rv with hτf
  have hτc : Continuous τf := continuous_filtShift S c Rv
  set M : ℝ := ∑ z ∈ T0, ‖W z‖ with hM
  have hSM : ∀ t, ‖Sf t‖ ≤ M := by
    intro t
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun z _ => ?_)))
    rw [norm_mul, norm_ladderPhase, mul_one]
  -- step 1: pointwise Minkowski
  have step1 : ∀ t : S → ℝ, ‖∑ z ∈ T0, (∏ a ∈ S, ψ a (omegaNode G (cosetDecoration G L base (dec z)) a /
      Rv a)) * W z * ladderPhase D S L γ δ base (dec z) t‖ ≤ ∫ ξ : S → ℝ, gF ξ * ‖Sf (t + τf ξ)‖ := by
    intro t
    rw [filtered_sum_eq ψ D S L γ δ base Rv hR hc.ne' T0 dec W t]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
    simp only [hgF, hSf, hτf]
    rw [norm_mul, norm_filtAmp]
  -- the product integrand
  set F2 : (S → ℝ) × (S → ℝ) → ℝ := fun p => gF p.2 * ‖Sf (p.1 + τf p.2)‖ with hF2
  have hF2c : Continuous F2 :=
    (hgFc.comp continuous_snd).mul ((hSc.comp (continuous_fst.add (hτc.comp continuous_snd))).norm)
  have hboxfin : volume box ≠ ⊤ := (isCompact_timeBox G D.layer S).measure_lt_top.ne
  have hF2i : Integrable F2 ((volume.restrict box).prod volume) := by
    refine Integrable.mono' ((integrableOn_const hboxfin (C := M)).mul_prod hgFi)
      hF2c.aestronglyMeasurable (Filter.Eventually.of_forall (fun p => ?_))
    simp only [hF2]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hgF0 _) (norm_nonneg _)), mul_comm M]
    exact mul_le_mul_of_nonneg_left (hSM _) (hgF0 _)
  -- step 2: integrate in time
  have step2 : ∫ t in box, ‖∑ z ∈ T0, (∏ a ∈ S, ψ a (omegaNode G (cosetDecoration G L base (dec z)) a /
      Rv a)) * W z * ladderPhase D S L γ δ base (dec z) t‖ ≤ ∫ t in box, ∫ ξ : S → ℝ, F2 (t, ξ) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _))
      hF2i.integral_prod_left (Filter.Eventually.of_forall step1)
  -- step 3: Fubini and translation
  have step3 : ∫ t in box, ∫ ξ : S → ℝ, F2 (t, ξ) =
      ∫ ξ : S → ℝ, gF ξ * ∫ t in timeBoxT G D.layer S (τf ξ), ‖Sf t‖ := by
    rw [integral_integral_swap (f := fun t ξ => F2 (t, ξ)) hF2i]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
    simp only [hF2]
    rw [integral_const_mul]
    congr 1
    exact integral_timeBox_shift D.layer S (fun t => ‖Sf t‖) (τf ξ)
  -- step 4: the translated bound and the ξ-integral
  have hK0 : ∀ ξ, 0 ≤ ∫ t in timeBoxT G D.layer S (τf ξ), ‖Sf t‖ := fun ξ =>
    integral_nonneg (fun t => norm_nonneg _)
  have step4 : k0 * ∫ ξ : S → ℝ, gF ξ * ∫ t in timeBoxT G D.layer S (τf ξ), ‖Sf t‖ ≤
      ∫ ξ : S → ℝ, B0 * ∏ a : S, (1 + |ξ a|) ^ 2 * ‖𝓕 (⇑(ψ a.1)) (ξ a)‖ := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ξ => ?_))
      ((integrable_prod_filterB ψ S).const_mul B0) (Filter.Eventually.of_forall (fun ξ => ?_))
    · exact mul_nonneg hk0 (mul_nonneg (hgF0 ξ) (hK0 ξ))
    · have h1 := hK (τf ξ)
      have h2 := hWt ξ
      have e : B0 * ∏ a : S, (1 + |ξ a|) ^ 2 * ‖𝓕 (⇑(ψ a.1)) (ξ a)‖ =
          gF ξ * ((∏ a : S, (1 + |ξ a|) ^ 2) * B0) := by
        rw [Finset.prod_mul_distrib]; simp only [hgF]; ring
      dsimp only
      rw [e]
      calc k0 * (gF ξ * ∫ t in timeBoxT G D.layer S (τf ξ), ‖Sf t‖)
          = gF ξ * (k0 * ∫ t in timeBoxT G D.layer S (τf ξ), ‖Sf t‖) := by ring
        _ ≤ gF ξ * (Wt (τf ξ) * B0) := mul_le_mul_of_nonneg_left h1 (hgF0 ξ)
        _ ≤ gF ξ * ((∏ a : S, (1 + |ξ a|) ^ 2) * B0) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hB0) (hgF0 ξ)
  calc k0 * ∫ t in box, ‖∑ z ∈ T0, (∏ a ∈ S, ψ a (omegaNode G (cosetDecoration G L base (dec z)) a /
        Rv a)) * W z * ladderPhase D S L γ δ base (dec z) t‖
      ≤ k0 * ∫ t in box, ∫ ξ : S → ℝ, F2 (t, ξ) := mul_le_mul_of_nonneg_left step2 hk0
    _ = k0 * ∫ ξ : S → ℝ, gF ξ * ∫ t in timeBoxT G D.layer S (τf ξ), ‖Sf t‖ := by rw [step3]
    _ ≤ ∫ ξ : S → ℝ, B0 * ∏ a : S, (1 + |ξ a|) ^ 2 * ‖𝓕 (⇑(ψ a.1)) (ξ a)‖ := step4
    _ = (∏ a ∈ S, filterB ⇑(ψ a)) * B0 := by
        rw [integral_const_mul, integral_prod_filterB, mul_comm]

section weight
open WaveTurbulence.LadderDecay.LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree}

/-- `κ |τ_a(ξ)| ≤ |ξ_a|` for `κ = c/2`, `R_a ≥ 1`. -/
lemma kappa_filtShift_le (S : Finset (GBranch G.tree)) {c : ℝ} (hc : 0 < c) (Rv : GBranch G.tree → ℝ)
    (hRv : ∀ a, 1 ≤ Rv a) (ξ : S → ℝ) (a : S) : c / 2 * |filtShift S c Rv ξ a| ≤ |ξ a| := by
  unfold filtShift
  have hR : 0 < Rv a.1 := lt_of_lt_of_le one_pos (hRv a.1)
  have hζ : |((((G.sign a.1.toNode : ℤˣ) : ℤ) : ℝ))| = 1 := by
    rcases Int.units_eq_one_or (G.sign a.1.toNode) with h | h <;> rw [h] <;> simp
  rw [abs_div, abs_mul, abs_mul, hζ, abs_of_pos (mul_pos hc hR), abs_two]
  have e : c / 2 * (2 * 1 * |ξ a| / (c * Rv a.1)) = |ξ a| / Rv a.1 := by
    field_simp
  rw [e, div_le_iff₀ hR]
  exact le_mul_of_one_le_right (abs_nonneg _) (hRv a.1)

/-- **The weight hypothesis of `filt_L1_le` for the ladder weight.** -/
lemma ladderWt_filtShift_le (C : LadderDecay.LadderDarts.Ctx G.molecule u v) {c : ℝ} (hc : 0 < c)
    (Rv : GBranch G.tree → ℝ) (hRv : ∀ a, 1 ≤ Rv a) (ξ : (Molecule.ladderAtoms u v) → ℝ) :
    ladderWt (u := u) (v := v) (c / 2) (filtShift (Molecule.ladderAtoms u v) c Rv ξ) ≤
      ∏ a : (Molecule.ladderAtoms u v), (1 + |ξ a|) ^ 2 := by
  classical
  set φ : (Molecule.ladderAtoms u v) → ℝ := fun a => (1 + |ξ a|) ^ 2 with hφ
  have hφ1 : ∀ a, 1 ≤ φ a := fun a => one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _))
  have hφ0 : ∀ a, 0 ≤ φ a := fun a => (zero_le_one).trans (hφ1 a)
  have hc2 : 0 ≤ c / 2 := by positivity
  have hfac : ∀ a, (1 + c / 2 * |filtShift (Molecule.ladderAtoms u v) c Rv ξ a|) ^ 2 ≤ φ a := by
    intro a
    have h := kappa_filtShift_le (Molecule.ladderAtoms u v) hc Rv hRv ξ a
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  set e := Sum.elim (evIdx (u := u) (v := v)) (euIdx (u := u) (v := v)) with he
  have hinj : Function.Injective e := C.idx_injective
  calc ladderWt (u := u) (v := v) (c / 2) (filtShift (Molecule.ladderAtoms u v) c Rv ξ)
      ≤ ∏ k : Fin n, φ (evIdx (u := u) (v := v) k) * φ (euIdx (u := u) (v := v) k) := by
        unfold ladderWt rungWt
        refine Finset.prod_le_prod₀ (fun k _ => by positivity) (fun k _ => ?_)
        exact mul_le_mul (hfac _) (hfac _) (by positivity) (hφ0 _)
    _ = ∏ i : Fin n ⊕ Fin n, φ (e i) := by
        rw [Fintype.prod_sum_type, Finset.prod_mul_distrib]
        rfl
    _ = ∏ a ∈ Finset.univ.image e, φ a :=
        (Finset.prod_image (fun i _ j _ h => hinj h)).symm
    _ ≤ ∏ a : (Molecule.ladderAtoms u v), φ a := by
        rw [← Finset.prod_sdiff (Finset.subset_univ (Finset.univ.image e))]
        exact le_mul_of_one_le_left (Finset.prod_nonneg (fun a _ => hφ0 a))
          (Finset.one_le_prod₀ (fun a _ => hφ1 a))

end weight

end WaveTurbulence.Flower.LadFilt
