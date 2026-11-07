/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.DegenVinePar.MixNorm
public import WaveTurbulence.Foundations.SumintPar.SourceLabelExpression
public import WaveTurbulence.Foundations.SumintPar.SourceLabelWeightPartition

/-! # The counted source extension with a character-mixture multiplier (DEGEN-VINE)

Summation over the localization labels of `mixLocalized`, its agreement with the multiplied source expression
`exprMix`, and its norm bound (countable Minkowski), exactly as for `SumintPar.countedSourceExtension`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.DegenVinePar
open WaveTurbulence.DegenVine
open WaveTurbulence.SumintPar MeasureTheory Set
open scoped ENNReal

variable {d : ℕ} {D : SumintPar.SumintDatum d}

/-- The multiplied source expression: `D.expr` with the lattice sum weighted by the mixture `m(E, x)`. -/
noncomputable def exprMix (M : CharMix D.S d) (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ)
    (efgh : Fin 4 → Mom d) : ℂ :=
  ((‖efgh 0 - efgh 1‖ ^ (Finset.univ.filter fun i => D.S.nor i = false ∧ D.badKind i = 1).card : ℝ) : ℂ) *
  ∑' x : D.S.VIdx → (Fin d → ℤ),
    (M.val L efgh x * ∏ v, D.wK v (efgh 0 - efgh 1) (D.kVec L x efgh v) * D.wL v (D.ℓVec L x efgh v)) *
      ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2), D.phase L γ δ η x (efgh 0 - efgh 1) (tt 0) τ

theorem norm_mul_mul_le (M : CharMix D.S d) (w φ m : ℂ) (hm : ‖m‖ ≤ M.mass) :
    ‖w * m * φ‖ ≤ M.mass * ‖w * φ‖ := by
  rw [norm_mul, norm_mul, norm_mul]
  have h0 := norm_nonneg w
  have h1 := norm_nonneg φ
  nlinarith [mul_nonneg h0 h1, mul_le_mul_of_nonneg_left hm (mul_nonneg h0 h1)]

/-- Summability of the multiplied time masses over the localization family. -/
theorem tsum_mixLocalized_mass_lt_top (hd : 1 ≤ d) (M : CharMix D.S d) (hI : 0 < D.S.I) (N : ℕ) (h : ℝ)
    {A L γ δ η : ℝ} {Dsteps : ℕ}
    (hA : 1 ≤ A) (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps)
    (p : SourceLocalizationLabel D hD → D.S.VIdx → Fin d → ℝ)
    (E : Fin 4 → Mom d) (hE : ∀ j, ‖E j-D.centre j‖ ≤ 1) :
    (∑' j : SourceLocalizationLabel D hD, ∫⁻ t,
      ‖mixLocalized M hI N h L γ δ η j.1 j.2.val (p j) E t‖ₑ) < ⊤ := by
  obtain ⟨C,hC,hbound⟩ := exists_mixLocalized_mass_bound (δ := δ) hd M hI N h hL hη hD
  calc
    _ ≤ ∑' j : SourceLocalizationLabel D hD,
        ENNReal.ofReal (‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card*
          (C * M.mass)) *
          ∑' x : D.S.VIdx → Fin d → ℤ, ‖localizedSourceWeight D L j.1 j.2.val E x‖ₑ :=
      ENNReal.tsum_le_tsum (fun j => hbound j.1 j.2.val (p j) E)
    _ = ENNReal.ofReal (‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card*
          (C * M.mass)) *
        ∑' a, ∑ b ∈ sourceAlternativeLabels D hD a,
          ∑' x : D.S.VIdx → Fin d → ℤ, ‖localizedSourceWeight D L a b E x‖ₑ := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      exact tsum_sourceLocalizationLabel D hD (fun a b => ∑' x : D.S.VIdx → Fin d → ℤ, ‖localizedSourceWeight D L a b E x‖ₑ)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (localized_source_weight_mass_lt_top hd D hA hL hD E hE)

/-- The complete multiplied ambient extension for a chosen family of cutoff centres. -/
noncomputable def mixCounted (M : CharMix D.S d) (hI : 0 < D.S.I) (N : ℕ) (h L γ δ η : ℝ) {A : ℝ}
    {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (p : SourceLocalizationLabel D hD → D.S.VIdx → Fin d → ℝ)
    (E : Fin 4 → Mom d) (t : Fin 3 → ℝ) : ℂ :=
  ∫ j : SourceLocalizationLabel D hD,
    mixLocalized M hI N h L γ δ η j.1 j.2.val (p j) E t ∂Measure.count

/-- Absolute regrouping with the multiplier. -/
theorem tsum_sourceLabel_expression_mix (hd : 1 ≤ d) (M : CharMix D.S d) (hI : 0 < D.S.I) {A L γ δ η : ℝ}
    {N : ℕ} (hA : 1 ≤ A) (hL : 0 < L) (hD : D.Admissible A L γ η N) (E : Fin 4 → Mom d)
    (hE : ∀ j, ‖E j-D.centre j‖ ≤ 1) (t : Fin 3 → ℝ) :
    (∑' j : SourceLocalizationLabel D hD, ∑' x : D.S.VIdx → Fin d → ℤ,
      localizedSourceWeight D L j.1 j.2.val E x * M.val L E x *
        (∫ τ in D.timeDom hI (t 0) (t 1) (t 2), D.phase L γ δ η x (E 0-E 1) (t 0) τ)) =
      ∑' x : D.S.VIdx → Fin d → ℤ,
        (M.val L E x * ∏ v, D.wK v (E 0 - E 1) (D.kVec L x E v)*D.wL v (D.ℓVec L x E v)) *
          (∫ τ in D.timeDom hI (t 0) (t 1) (t 2), D.phase L γ δ η x (E 0-E 1) (t 0) τ) := by
  have hs0 := summable_norm_sourceLabel_expression (δ := δ) hd D hI hA hL hD E hE t
  have hs : Summable (fun q : SourceLocalizationLabel D hD × (D.S.VIdx → Fin d → ℤ) =>
      localizedSourceWeight D L q.1.1 q.1.2.val E q.2 * M.val L E q.2 *
        (∫ τ in D.timeDom hI (t 0) (t 1) (t 2), D.phase L γ δ η q.2 (E 0-E 1) (t 0) τ)) := by
    refine Summable.of_norm ?_
    refine (hs0.mul_left M.mass).of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
    exact norm_mul_mul_le M _ _ _ (M.norm_val_le L E q.2)
  rw [← hs.tsum_comm]
  apply tsum_congr
  intro x
  have : ∀ j : SourceLocalizationLabel D hD,
      localizedSourceWeight D L j.1 j.2.val E x * M.val L E x *
        (∫ τ in D.timeDom hI (t 0) (t 1) (t 2), D.phase L γ δ η x (E 0-E 1) (t 0) τ) =
      localizedSourceWeight D L j.1 j.2.val E x *
        (M.val L E x * ∫ τ in D.timeDom hI (t 0) (t 1) (t 2), D.phase L γ δ η x (E 0-E 1) (t 0) τ) :=
    fun j => by ring
  simp_rw [this]
  rw [tsum_mul_right, tsum_sourceLabel_weight D hD E hE x]
  ring

/-- Agreement of the counted multiplied extension with the multiplied source expression. -/
theorem exists_mixCounted_agreement (hd : 1 ≤ d) (M : CharMix D.S d) (hI : 0 < D.S.I) (N : ℕ) {h : ℝ}
    (hh : 0 < h) {A L γ δ η : ℝ} {Dsteps : ℕ} (hA : 1 ≤ A) (hL : 0 < L) (hη : η ≤ 1/3)
    (hD : D.Admissible A L γ η Dsteps) :
    ∃ p : SourceLocalizationLabel D hD → D.S.VIdx → Fin d → ℝ,
      ∀ E : Fin 4 → Mom d, (∀ j, ‖E j-D.centre j‖ ≤ 1) →
      ∀ t : Fin 3 → ℝ, (∀ j, t j ∈ Icc (0:ℝ) N) →
        mixCounted M hI N h L γ δ η hD p E t = exprMix M hI L γ δ η t E := by
  classical
  choose p hp using fun j : SourceLocalizationLabel D hD =>
    exists_mixLocalized_agreement (δ := δ) M hI N hh hL hD j.1 j.2.val
  refine ⟨p,?_⟩
  intro E hE t ht
  let G := fun (j : SourceLocalizationLabel D hD) (x : D.S.VIdx → Fin d → ℤ) =>
    localizedSourceWeight D L j.1 j.2.val E x * M.val L E x *
      (∫ τ in D.timeDom hI (t 0) (t 1) (t 2), D.phase L γ δ η x (E 0-E 1) (t 0) τ)
  have hs0 := summable_norm_sourceLabel_expression (δ := δ) hd D hI hA hL hD E hE t
  have hs : Summable (fun q : SourceLocalizationLabel D hD × (D.S.VIdx → Fin d → ℤ) => ‖G q.1 q.2‖) := by
    refine (hs0.mul_left M.mass).of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
    change ‖localizedSourceWeight D L q.1.1 q.1.2.val E q.2 * M.val L E q.2 *
        (∫ τ in D.timeDom hI (t 0) (t 1) (t 2), D.phase L γ δ η q.2 (E 0-E 1) (t 0) τ)‖ ≤ _
    exact norm_mul_mul_le M _ _ _ (M.norm_val_le L E q.2)
  have hm : Summable (fun j => ‖∑' x, G j x‖) :=
    hs.prod.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => norm_tsum_le_tsum_norm (hs.prod_factor j))
  have he (j : SourceLocalizationLabel D hD) :
      mixLocalized M hI N h L γ δ η j.1 j.2.val (p j) E t =
        ((‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card : ℝ):ℂ)*
          ∑' x, G j x := hp j E hE t ht
  have hseries : Summable (fun j : SourceLocalizationLabel D hD =>
      ‖mixLocalized M hI N h L γ δ η j.1 j.2.val (p j) E t‖) := by
    simp_rw [he,norm_mul]
    exact hm.mul_left _
  unfold mixCounted
  rw [count_integral_eq_tsum _ hseries]
  simp_rw [he]
  rw [tsum_mul_left]
  have hsum := tsum_sourceLabel_expression_mix (δ := δ) hd M hI hA hL hD E hE t
  change (∑' j, ∑' x, G j x) = _ at hsum
  rw [hsum]
  rfl

/-- Conditional linear recombination estimate for the complete multiplied extension. -/
theorem XNorm00_mixCounted_le (hd : 1 ≤ d) (M : CharMix D.S d) (hI : 0 < D.S.I) (N : ℕ) (h : ℝ)
    {A L γ δ η : ℝ} {Dsteps : ℕ}
    (hA : 1 ≤ A) (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps)
    (p : SourceLocalizationLabel D hD → D.S.VIdx → Fin d → ℝ)
    {V : Type*} [Countable V] (E : V → Fin 4 → Mom d)
    (hE : ∀ v j, ‖E v j-D.centre j‖ ≤ 1) (θ : ℝ) (B : ℝ≥0∞)
    (hF : ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d),
      XNorm00 θ (fun t v => weightedSourceExtension D hI N h L γ δ η p ν (E v 0-E v 1) t) ≤ B) :
    XNorm00 θ (fun t v => mixCounted M hI N h L γ δ η hD p (E v) t) ≤
      ENNReal.ofReal ((((9:ℝ)^d*A^d)*summedCellFourierFactor d (d+1)*cellFourierFactor d)^D.S.M) *
        (ENNReal.ofReal M.mass * B) := by
  let F := fun (j : SourceLocalizationLabel D hD) t v =>
    mixLocalized M hI N h L γ δ η j.1 j.2.val (p j) (E v) t
  apply (XNorm00_count_integral_le θ F
    (fun j v => measurable_mixLocalized M hI N h L γ δ η j.1 j.2.val (p j) (E v))
    (fun j v => integrable_mixLocalized M hI N h hL hη j.1 j.2.val (p j) (E v))
    (fun v => tsum_mixLocalized_mass_lt_top hd M hI N h hA hL hη hD p (E v) (hE v))).trans
  calc
    _ ≤ ∑' j : SourceLocalizationLabel D hD,
        (ENNReal.ofReal (∫ ξ, (sourceWeightDecay D L γ η)⁻¹ * coefMajor D L γ η j.1 j.2.val ξ) *
          ENNReal.ofReal M.mass) * B :=
      ENNReal.tsum_le_tsum (fun j => XNorm00_mixLocalized_le hd M hI N h hL hη hD
        j.1 j.2.val (p j) E θ B (hF (p j)))
    _ = (∑' a, ∑ b ∈ sourceAlternativeLabels D hD a,
        ENNReal.ofReal (∫ ξ, (sourceWeightDecay D L γ η)⁻¹ * coefMajor D L γ η a b ξ)) *
          (ENNReal.ofReal M.mass * B) := by
      simp_rw [mul_assoc]
      rw [ENNReal.tsum_mul_right]
      congr 1
      exact tsum_sourceLocalizationLabel D hD (fun a b =>
        ENNReal.ofReal (∫ ξ, (sourceWeightDecay D L γ η)⁻¹ * coefMajor D L γ η a b ξ))
    _ ≤ _ := mul_le_mul' (tsum_normalizedCoefMajor_mass_le hd D hA hL hD) le_rfl

end WaveTurbulence.DegenVinePar
