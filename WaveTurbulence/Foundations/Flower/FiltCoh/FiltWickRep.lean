/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.FiltRep
public import WaveTurbulence.Foundations.Flower.FiltLink.Lemma141

/-! # FILT-COH (d2a): resonance filters as Fourier multipliers of the NT profile

o82 Prop. 15.1: the filters `χ(|Ω_b|/M_b)` of a coherent object are functions of the link energies and enter the
profile of Thm 10.1 with their Fourier-measure costs. Here:
* `GoodFactor d K f`: `f(u) = ∫ fh(t) e(tu) dt` with `∫ ‖fh‖ (1 + t²)^d ≤ K`; `FiltMul d K N ψ`: `ψ` is a product
  of at most `N` good factors;
* `exists_rep_mul_filtMul`: a profile with a weighted Fourier representation, multiplied by `∏_j ψ_j(Ω_j)`, keeps
  one with the weights multiplied by `(2^d K)^{N n}` (iterating `isFourierRep_mul_filter`, `shearConv_weight_le`);
* `goodFactor_filtProf`: `u ↦ χ(u/S)` (`χ ∈ {χ₀, χD}`, `S ≥ 1`) is good with a constant `Kfilt d` uniform in `S`;
* `filtMul_linkFiltWeight`: D5a's two-layer link multiplier at `|Ω| = |2Ω/μ|` is a product of at most
  `#(F ∩ E) + #(Fu ∩ E)` such factors once `μ M/2 ≥ 1`;
* `filtRes J Ψ₁ ψ = resProfile J Ψ₁ · ∏_j ψ_j(Ω_j)`: the filtered NT profile. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open MeasureTheory WaveTurbulence.ApproxNT Finset
open scoped ENNReal FourierTransform SchwartzMap ContDiff

/-! ### Good factors and their products -/

/-- A one-dimensional factor with a `d`-weighted Fourier density of mass at most `K`. -/
@[expose] def GoodFactor (d : ℕ) (K : ℝ) (f : ℝ → ℂ) : Prop :=
  ∃ fh : ℝ → ℂ, Integrable fh ∧ Integrable (fun t => ‖fh t‖ * (1 + t ^ 2) ^ d) ∧
    (∫ t, ‖fh t‖ * (1 + t ^ 2) ^ d) ≤ K ∧ ∀ u, f u = ∫ t, fh t * (Real.fourierChar (t * u) : ℂ)

/-- A product of at most `N` good factors. -/
@[expose] def FiltMul (d : ℕ) (K : ℝ) (N : ℕ) (ψ : ℝ → ℂ) : Prop :=
  ∃ (m : ℕ) (f : Fin m → ℝ → ℂ), m ≤ N ∧ (∀ i, GoodFactor d K (f i)) ∧ ∀ u, ψ u = ∏ i, f i u

variable {d : ℕ}

theorem GoodFactor.norm_le {K : ℝ} {f : ℝ → ℂ} (h : GoodFactor d K f) (u : ℝ) : ‖f u‖ ≤ K := by
  obtain ⟨fh, hfi, hfw, hK, hf⟩ := h
  rw [hf u]
  calc ‖∫ t, fh t * (Real.fourierChar (t * u) : ℂ)‖
      ≤ ∫ t, ‖fh t * (Real.fourierChar (t * u) : ℂ)‖ := norm_integral_le_integral_norm _
    _ = ∫ t, ‖fh t‖ := by
        congr 1
        funext t
        rw [norm_mul, Circle.norm_coe, mul_one]
    _ ≤ ∫ t, ‖fh t‖ * (1 + t ^ 2) ^ d := integral_mono hfi.norm hfw fun t =>
        le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (by nlinarith [sq_nonneg t]))
    _ ≤ K := hK

theorem FiltMul.norm_le {K : ℝ} {N : ℕ} {ψ : ℝ → ℂ} (h : FiltMul d K N ψ) (hK : 1 ≤ K) (u : ℝ) :
    ‖ψ u‖ ≤ K ^ N := by
  obtain ⟨m, f, hm, hf, hψ⟩ := h
  rw [hψ u, norm_prod]
  calc ∏ i, ‖f i u‖ ≤ ∏ _i : Fin m, K :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => (hf i).norm_le u)
    _ = K ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ K ^ N := pow_le_pow_right₀ hK hm

theorem FiltMul.mono {K : ℝ} {N N' : ℕ} {ψ : ℝ → ℂ} (h : FiltMul d K N ψ) (hN : N ≤ N') : FiltMul d K N' ψ := by
  obtain ⟨m, f, hm, hf, hψ⟩ := h
  exact ⟨m, f, hm.trans hN, hf, hψ⟩

theorem FiltMul.mul {K : ℝ} {N₁ N₂ : ℕ} {ψ₁ ψ₂ : ℝ → ℂ} (h₁ : FiltMul d K N₁ ψ₁) (h₂ : FiltMul d K N₂ ψ₂) :
    FiltMul d K (N₁ + N₂) (fun u => ψ₁ u * ψ₂ u) := by
  obtain ⟨m₁, f₁, hm₁, hf₁, hψ₁⟩ := h₁
  obtain ⟨m₂, f₂, hm₂, hf₂, hψ₂⟩ := h₂
  refine ⟨m₁ + m₂, Fin.append f₁ f₂, by omega, fun i => ?_, fun u => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hf₁ i
    · rw [Fin.append_right]; exact hf₂ i
  · show ψ₁ u * ψ₂ u = _
    rw [hψ₁ u, hψ₂ u, Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem filtMul_finset_prod {ι : Type*} {K : ℝ} (S : Finset ι) (g : ι → ℝ → ℂ)
    (hg : ∀ i ∈ S, GoodFactor d K (g i)) : FiltMul d K S.card (fun u => ∏ i ∈ S, g i u) := by
  classical
  refine ⟨S.card, fun k u => g (S.equivFin.symm k) u, le_rfl, fun k => hg _ (S.equivFin.symm k).2,
    fun u => ?_⟩
  show ∏ i ∈ S, g i u = ∏ k : Fin S.card, g (S.equivFin.symm k) u
  rw [← Finset.prod_coe_sort S]
  exact (Equiv.prod_comp S.equivFin.symm (fun i : S => g i u)).symm

/-! ### Multiplying a Fourier representation by filter products -/

theorem isFourierRep_congr {ι : Type} [Fintype ι] {Φ Φ' Φh : (ι → ℝ) → ℂ} (hΦ : ∀ Ω, Φ Ω = Φ' Ω)
    (h : IsFourierRep Φ Φh) : IsFourierRep Φ' Φh :=
  ⟨h.1, fun Ω => (hΦ Ω).symm.trans (h.2 Ω)⟩

/-- **`m` good factors in one coordinate.** -/
theorem exists_rep_mul_factors {ι : Type} [Fintype ι] [DecidableEq ι] {K : ℝ}
    {Φ Φh : (ι → ℝ) → ℂ} (hrep : IsFourierRep Φ Φh) (A : Finset ι → ℝ)
    (hA : ∀ F s, ‖Φh s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤ A F) (j : ι) :
    ∀ (m : ℕ) (f : Fin m → ℝ → ℂ), (∀ i, GoodFactor d K (f i)) →
      ∃ Φh' : (ι → ℝ) → ℂ, IsFourierRep (fun Ω => Φ Ω * ∏ i, f i (Ω j)) Φh' ∧
        ∀ F s, ‖Φh' s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤ (2 ^ d * K) ^ m * A F := by
  intro m
  induction m with
  | zero =>
    intro f _
    refine ⟨Φh, isFourierRep_congr (fun Ω => by simp) hrep, fun F s => ?_⟩
    simpa using hA F s
  | succ m ih =>
    intro f hf
    obtain ⟨Φh₁, hrep₁, hA₁⟩ := ih (fun i => f (Fin.castSucc i)) (fun i => hf _)
    obtain ⟨fh, hfi, hfw, hK, hfe⟩ := hf (Fin.last m)
    have hrep₂ := isFourierRep_mul_filter hrep₁ hfi hfe j
    refine ⟨shearConv Φh₁ fh j, isFourierRep_congr (fun Ω => ?_) hrep₂, fun F s => ?_⟩
    · simp only [Fin.prod_univ_castSucc, mul_assoc]
    · have h := shearConv_weight_le d hfw hK (fun F => (2 ^ d * K) ^ m * A F) hA₁ j F s
      calc _ ≤ 2 ^ d * ((2 ^ d * K) ^ m * A F) * K := h
        _ = (2 ^ d * K) ^ (m + 1) * A F := by ring

/-- **A filter product in every coordinate of a finite set.** -/
theorem exists_rep_mul_filtMul {ι : Type} [Fintype ι] [DecidableEq ι] {K : ℝ} (hK : 1 ≤ K)
    {Φ Φh : (ι → ℝ) → ℂ} (hrep : IsFourierRep Φ Φh) (A : Finset ι → ℝ)
    (hA : ∀ F s, ‖Φh s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤ A F) (N : ℕ) (ψ : ι → ℝ → ℂ)
    (hψ : ∀ j, FiltMul d K N (ψ j)) (T : Finset ι) :
    ∃ Φh' : (ι → ℝ) → ℂ, IsFourierRep (fun Ω => Φ Ω * ∏ j ∈ T, ψ j (Ω j)) Φh' ∧
      ∀ F s, ‖Φh' s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤ (2 ^ d * K) ^ (N * T.card) * A F := by
  have hA0 : ∀ F, 0 ≤ A F := fun F =>
    (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => by positivity)).trans (hA F 0)
  have h2K : 1 ≤ 2 ^ d * K := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hK
  induction T using Finset.induction_on with
  | empty => exact ⟨Φh, isFourierRep_congr (fun Ω => by simp) hrep, fun F s => by simpa using hA F s⟩
  | @insert a T ha ih =>
    obtain ⟨Φh₁, hrep₁, hA₁⟩ := ih
    obtain ⟨m, f, hm, hf, hψe⟩ := hψ a
    obtain ⟨Φh₂, hrep₂, hA₂⟩ := exists_rep_mul_factors hrep₁ (fun F => (2 ^ d * K) ^ (N * T.card) * A F) hA₁ a
      m f hf
    refine ⟨Φh₂, isFourierRep_congr (fun Ω => ?_) hrep₂, fun F s => (hA₂ F s).trans ?_⟩
    · rw [Finset.prod_insert ha, hψe]
      ring
    · rw [Finset.card_insert_of_notMem ha, ← mul_assoc, ← pow_add]
      refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h2K (by nlinarith)) (hA0 F)

/-! ### The two filter profiles as dilated Schwartz factors -/

theorem contDiff_chiD : ContDiff ℝ ∞ FlShell.chiD := by
  have h : ContDiff ℝ ∞ Fourier.chi0 := Fourier.chi0_contDiff
  have hd : ContDiff ℝ ∞ (deriv Fourier.chi0) := (contDiff_infty_iff_deriv.mp h).2
  have he : FlShell.chiD = fun u => -u * deriv Fourier.chi0 u := by
    funext u
    simp only [FlShell.chiD, FlShell.chi0_eq_fourier]
  rw [he]
  exact contDiff_id.neg.mul hd

theorem contDiff_filtProf (a : Bool) : ContDiff ℝ ∞ (FiltLink.filtProf a) := by
  cases a
  · simp only [FiltLink.filtProf, Bool.false_eq_true, ↓reduceIte]
    rw [FlShell.chi0_eq_fourier]
    exact Fourier.chi0_contDiff
  · simp only [FiltLink.filtProf, ↓reduceIte]
    exact contDiff_chiD

/-- A filter profile as a complex Schwartz map. -/
@[expose] def filtSchwartz (a : Bool) : 𝓢(ℝ, ℂ) :=
  ((FiltLink.smoothFilter_filtProf a).compact.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (contDiff_filtProf a))

theorem filtSchwartz_apply (a : Bool) (u : ℝ) : filtSchwartz a u = ((FiltLink.filtProf a u : ℝ) : ℂ) := rfl

/-- The weighted Fourier mass of both filter profiles. -/
@[expose] def Kfilt (d : ℕ) : ℝ :=
  max 1 (max (∫ v, ‖𝓕 (filtSchwartz false) v‖ * (1 + v ^ 2) ^ d)
    (∫ v, ‖𝓕 (filtSchwartz true) v‖ * (1 + v ^ 2) ^ d))

theorem one_le_Kfilt (d : ℕ) : 1 ≤ Kfilt d := le_max_left _ _

theorem mass_le_Kfilt (d : ℕ) (a : Bool) : ∫ v, ‖𝓕 (filtSchwartz a) v‖ * (1 + v ^ 2) ^ d ≤ Kfilt d := by
  cases a
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- **A dilated filter profile is a good factor, uniformly in the scale `S ≥ 1`.** -/
theorem goodFactor_filtProf (a : Bool) {S : ℝ} (hS : 1 ≤ S) :
    GoodFactor d (Kfilt d) (fun u => ((FiltLink.filtProf a (u / S) : ℝ) : ℂ)) := by
  have hS0 : 0 < S := zero_lt_one.trans_le hS
  obtain ⟨hw, hm⟩ := dilate_weight_le (filtSchwartz a) hS d
  refine ⟨fun t => (S : ℂ) * 𝓕 (filtSchwartz a) (S * t), ?_, hw, hm.trans (mass_le_Kfilt d a), fun u => ?_⟩
  · refine hw.mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
    · exact (continuous_const.mul ((𝓕 (filtSchwartz a)).continuous.comp
        (continuous_const.mul continuous_id))).aestronglyMeasurable
    · exact le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (by nlinarith [sq_nonneg t]))
  · have h := dilate_eq_integral (filtSchwartz a) hS0 u
    rw [filtSchwartz_apply] at h
    exact h

/-! ### The link multiplier in profile coordinates -/

theorem filtProf_abs_div (a : Bool) {μ M : ℝ} (hμ : 0 < μ) (hM : 0 < M) (Ω : ℝ) :
    FiltLink.filtProf a (|2 * (Ω / μ)| / M) = FiltLink.filtProf a (Ω / (μ * M / 2)) := by
  have h2 : Ω / (μ * M / 2) = 2 * (Ω / μ) / M := by
    field_simp
  have he : |2 * (Ω / μ)| / M = |Ω / (μ * M / 2)| := by
    rw [h2, abs_div, abs_of_pos hM]
  rw [he, (FiltLink.smoothFilter_filtProf a).abs_eq]

/-- **D5a's link multiplier is a filter product in the profile coordinate `Ω = μ u`.** -/
theorem filtMul_linkFiltWeight {ι : Type*} [DecidableEq ι] (E F Fu : Finset ι) (ann : ι → Bool) (M Mu : ι → ℝ)
    {μ : ℝ} (hμ : 0 < μ) (hM : ∀ i ∈ F, 1 ≤ μ * M i / 2) (hMu : ∀ i ∈ Fu, 1 ≤ μ * Mu i / 2) :
    FiltMul d (Kfilt d) ((F ∩ E).card + (Fu ∩ E).card)
      (fun Ω => FiltLink.linkFiltWeight E F Fu ann M Mu (Ω / μ)) := by
  have hM0 : ∀ i ∈ F, 0 < M i := fun i hi => by
    have := hM i hi
    by_contra h
    have h' := le_of_not_gt h
    nlinarith
  have hMu0 : ∀ i ∈ Fu, 0 < Mu i := fun i hi => by
    have := hMu i hi
    by_contra h
    have h' := le_of_not_gt h
    nlinarith
  have h1 := filtMul_finset_prod (d := d) (K := Kfilt d) (F ∩ E)
    (fun i Ω => ((FiltLink.filtProf (ann i) (Ω / (μ * M i / 2)) : ℝ) : ℂ))
    (fun i hi => goodFactor_filtProf (ann i) (hM i (Finset.mem_inter.mp hi).1))
  have h2 := filtMul_finset_prod (d := d) (K := Kfilt d) (Fu ∩ E)
    (fun i Ω => ((FiltLink.filtProf false (Ω / (μ * Mu i / 2)) : ℝ) : ℂ))
    (fun i hi => goodFactor_filtProf false (hMu i (Finset.mem_inter.mp hi).1))
  obtain ⟨m, f, hm, hf, he⟩ := h1.mul h2
  refine ⟨m, f, hm, hf, fun Ω => ?_⟩
  rw [← he Ω]
  simp only [FiltLink.linkFiltWeight, FiltLink.linkFiltMult]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [filtProf_abs_div _ hμ (hM0 i (Finset.mem_inter.mp hi).1)]
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [filtProf_abs_div _ hμ (hMu0 i (Finset.mem_inter.mp hi).1)]

/-! ### The filtered NT profile -/

/-- The NT profile of DH23 times the link filters `∏_j ψ_j(Ω_j)`. -/
@[expose] def filtRes {n : ℕ} (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ)
    (ψ : Fin n → ℝ → ℂ) (Ω : Fin n → ℝ) : ℂ :=
  resProfile J Ψ₁ Ω * ∏ j, ψ j (Ω j)

end WaveTurbulence.Flower.FiltCoh
