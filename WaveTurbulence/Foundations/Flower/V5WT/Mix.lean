/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Vine.DegenVinePar.MixRecomb
public import WaveTurbulence.Foundations.Vine.DegenVine.MixAlgebra

/-! # V5W-T T2 (part 1): output-dependent character mixtures and the multiplied extension norm

`OutCharMix` (S-V5W probe §3, supplement Lemma 4.2): a character mixture on the input lattice of a `sumint` shape whose
input frequencies `ζ a E` and phases `u a E` may depend on the output `E`, over ONE common finite measure.
`N.freeze E : CharMix` freezes the output: `(N.freeze E).val L E' = N.val L E`.  Every identity of main's mix chain
that is pointwise in the output is reused from main at `N.freeze E`; only the estimates that keep the output supremum
inside the time-Fourier integral are copied here, with the modulation `ν v` depending on the output `v`:

* `XNorm00_integral_weightedSourceExtension_leOut` (main `SumintPar/SourceExtensionIntegralBound.lean`);
* `XNorm00_weightedSourceExtension_leOut` (main `SumintPar/WeightedSourceExtension.lean`);
* `XNorm00_mixLocalized_leOut` (main `DegenVinePar/MixNorm.lean`);
* `XNorm00_mixCounted_leOut` (main `DegenVinePar/MixCounted.lean`);
* `XNorm00Restr_mix_of_kernel_boundOut` (main `DegenVinePar/MixRecomb.lean`).

The agreement lemmas `exists_mixLocalized_agreement_unif`, `exists_mixCounted_agreement_unif` are main's
`exists_mixLocalized_agreement`, `exists_mixCounted_agreement` with the cutoff centres chosen before the mixture (main's
proof already chooses them from the datum alone).  Copied by source from main 416902c8 (sha256 in `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.V5WT
open WaveTurbulence WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
open WaveTurbulence.SumintPar MeasureTheory Set
open scoped ENNReal

/-! ## Output-dependent character mixtures -/

/-- A character mixture whose input frequencies and phases may depend on the output `E` (common finite measure). -/
structure OutCharMix (S : SumintShape) (d : ℕ) where
  α : Type
  [mα : MeasurableSpace α]
  μ : Measure α
  [hμ : IsFiniteMeasure μ]
  ζ : α → (Fin 4 → Mom d) → S.VIdx → Mom d
  hζ : ∀ E, Measurable fun a => ζ a E
  u : α → (Fin 4 → Mom d) → ℂ
  hu : ∀ E, Measurable fun a => u a E
  hu1 : ∀ a E, ‖u a E‖ ≤ 1

attribute [instance] OutCharMix.mα OutCharMix.hμ

namespace OutCharMix
variable {S : SumintShape} {d : ℕ}

/-- The multiplier. -/
noncomputable def val (N : OutCharMix S d) (L : ℝ) (E : Fin 4 → Mom d) (x : S.VIdx → Fin d → ℤ) : ℂ :=
  ∫ a, N.u a E * charOf S L (N.ζ a E) x ∂N.μ

/-- The mass. -/
noncomputable def mass (N : OutCharMix S d) : ℝ := N.μ.real Set.univ

theorem mass_nonneg (N : OutCharMix S d) : 0 ≤ N.mass := measureReal_nonneg

/-- The mixture with the output frozen at `E`. -/
noncomputable def freeze (N : OutCharMix S d) (E : Fin 4 → Mom d) : CharMix S d where
  α := N.α
  μ := N.μ
  ζ := fun a => N.ζ a E
  hζ := N.hζ E
  u := fun a _ => N.u a E
  hu := fun _ => N.hu E
  hu1 := fun a _ => N.hu1 a E

theorem freeze_val (N : OutCharMix S d) (E E' : Fin 4 → Mom d) (L : ℝ) (x : S.VIdx → Fin d → ℤ) :
    (N.freeze E).val L E' x = N.val L E x := rfl

theorem freeze_mass (N : OutCharMix S d) (E : Fin 4 → Mom d) : (N.freeze E).mass = N.mass := rfl

theorem norm_val_le (N : OutCharMix S d) (L : ℝ) (E : Fin 4 → Mom d) (x : S.VIdx → Fin d → ℤ) :
    ‖N.val L E x‖ ≤ N.mass :=
  (N.freeze E).norm_val_le L E x

/-- Every `CharMix` is an `OutCharMix` (constant frequencies). -/
noncomputable def ofCharMix (M : CharMix S d) : OutCharMix S d where
  α := M.α
  μ := M.μ
  ζ := fun a _ => M.ζ a
  hζ := fun _ => M.hζ
  u := M.u
  hu := M.hu
  hu1 := M.hu1

theorem ofCharMix_val (M : CharMix S d) (L : ℝ) (E : Fin 4 → Mom d) (x : S.VIdx → Fin d → ℤ) :
    (ofCharMix M).val L E x = M.val L E x := rfl

theorem ofCharMix_mass (M : CharMix S d) : (ofCharMix M).mass = M.mass := rfl

/-- The product of a `CharMix` and an `OutCharMix`. -/
noncomputable def mulC (M : CharMix S d) (N : OutCharMix S d) : OutCharMix S d where
  α := M.α × N.α
  μ := M.μ.prod N.μ
  ζ := fun q E => M.ζ q.1 + N.ζ q.2 E
  hζ := fun E => (M.hζ.comp measurable_fst).add ((N.hζ E).comp measurable_snd)
  u := fun q E => M.u q.1 E * N.u q.2 E
  hu := fun E => ((M.hu E).comp measurable_fst).mul ((N.hu E).comp measurable_snd)
  hu1 := fun q E => by
    rw [norm_mul]
    calc _ ≤ 1 * 1 := mul_le_mul (M.hu1 _ _) (N.hu1 _ _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- Freezing commutes with the product (values). -/
theorem mulC_val_freeze (M : CharMix S d) (N : OutCharMix S d) (L : ℝ) (E : Fin 4 → Mom d)
    (x : S.VIdx → Fin d → ℤ) : (mulC M N).val L E x = (M.mul (N.freeze E)).val L E x := rfl

theorem mulC_val (M : CharMix S d) (N : OutCharMix S d) (L : ℝ) (E : Fin 4 → Mom d)
    (x : S.VIdx → Fin d → ℤ) : (mulC M N).val L E x = M.val L E x * N.val L E x := by
  rw [mulC_val_freeze, CharMix.val_mul, freeze_val]

theorem mulC_mass (M : CharMix S d) (N : OutCharMix S d) : (mulC M N).mass = M.mass * N.mass := by
  have h : (mulC M N).mass = (M.mul (N.freeze 0)).mass := rfl
  rw [h, CharMix.mass_mul, freeze_mass]

end OutCharMix

/-! ## The Minkowski step with an output-dependent modulation -/

/-- Copy of `SumintPar.XNorm00_integral_weightedSourceExtension_le` with the modulation `ν a v` depending on the
output `v`. -/
theorem XNorm00_integral_weightedSourceExtension_leOut {α V : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] [Countable V] {d : ℕ} (D : SumintPar.SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h : ℝ) {L : ℝ} (hL : 0 < L) (γ δ η : ℝ)
    (hη : η ≤ 1/3) (p : D.S.VIdx → Fin d → ℝ) (ν : α → V → D.S.VIdx → Mom d)
    (hν : ∀ v, Measurable fun a => ν a v) (r : V → Mom d) (C : α → ℂ) (hCm : Measurable C)
    (hCi : Integrable C μ) (χ : α → V → ℂ) (hχ : ∀ v, Measurable (fun a => χ a v))
    (hχnorm : ∀ a v, ‖χ a v‖ ≤ 1) (θ : ℝ) (B : ℝ≥0∞)
    (hF : ∀ a, XNorm00 θ (fun t v => weightedSourceExtension D hI N h L γ δ η p (ν a v) (r v) t) ≤ B) :
    XNorm00 θ (fun t v => ∫ a, C a*χ a v*
      weightedSourceExtension D hI N h L γ δ η p (ν a v) (r v) t ∂μ) ≤
      (∫⁻ a, ‖C a‖ₑ ∂μ)*B := by
  let F := fun a t v => C a*χ a v*weightedSourceExtension D hI N h L γ δ η p (ν a v) (r v) t
  have hm (v : V) : Measurable (fun q : α × (Fin 3 → ℝ) => F q.1 q.2 v) := by
    have hp : Measurable (Prod.fst : α × (Fin 3 → ℝ) → α) := measurable_fst
    have hc := (hCm.mul (hχ v)).comp hp
    exact hc.mul (measurable_weightedSourceExtension_joint D hI N h hL γ δ η hη p (fun a => ν a v) (hν v) (r v))
  have hi (v : V) : Integrable (fun q : α × (Fin 3 → ℝ) => F q.1 q.2 v) (μ.prod volume) :=
    integrable_coefficient_weightedSourceExtension D hI N h hL γ δ η hη p (fun a => ν a v) (hν v) (r v) C
      (fun a => χ a v) hCi (hχ v) (fun a => hχnorm a v)
  have hs (a : α) (v : V) : Integrable (fun t => F a t v) :=
    (integrable_weightedSourceExtension D hI N h hL γ δ η hη p (ν a v) (r v)).const_mul _
  apply (XNorm00_integral_le θ F hm hi hs).trans
  calc
    _ ≤ ∫⁻ a, ‖C a‖ₑ*B ∂μ := by
      apply lintegral_mono
      intro a
      change XNorm00 θ (F a) ≤ ‖C a‖ₑ*B
      have he : F a = fun t v => C a • (χ a v*
          weightedSourceExtension D hI N h L γ δ η p (ν a v) (r v) t) := by
        funext t v
        dsimp [F]
        simp only [mul_assoc]
      rw [he,XNorm00_smul]
      apply mul_le_mul' le_rfl
      exact (XNorm00_output_mul_le θ _ (χ a) (fun v => by
        rw [← ofReal_norm]
        exact (ENNReal.ofReal_le_ofReal (hχnorm a v)).trans_eq ENNReal.ofReal_one)).trans (hF a)
    _ = _ := lintegral_mul_const _ hCm.enorm

/-- Copy of `SumintPar.XNorm00_weightedSourceExtension_le` with the modulation `ν v` depending on the output. -/
theorem XNorm00_weightedSourceExtension_leOut {d : ℕ} {V : Type*} (D : SumintPar.SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) {h θ : ℝ} (hh : h ∈ Ioc (0:ℝ) 1)
    (hθ : θ ∈ Icc (0:ℝ) 1) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : V → D.S.VIdx → Mom d) (r : V → Mom d)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hF : ∀ j : ℤ, XNorm00 θ (fun z v => kernelExtension D hI ((j:ℝ)*h) h
      (weightedCutoffInput D L γ δ η p (ν v) (r v)) z) ≤ B) :
    XNorm00 θ (fun t v => weightedSourceExtension D hI N h L γ δ η p (ν v) (r v) t) ≤
      ENNReal.ofReal (2^θ)*
        ENNReal.ofReal ((((D.S.M:ℝ)+1)*parameterMaximum D)^θ)*
        (ENNReal.ofReal (4^θ)*
          (ENNReal.ofReal (cellMultiplierRealConstant N*((N:ℝ)+5)*h⁻¹*h⁻¹)*B)) := by
  have hc := XNorm00_timeCellExtension_le D hI N hh
    (by simpa only [abs_of_nonneg hθ.1] using hθ.2)
    (fun v => weightedCutoffInput D L γ δ η p (ν v) (r v)) B hB hF
  have hs := (XNorm00_sourceTimeShear_le hθ.1
    (fun z v => timeCellExtension D hI N h (weightedCutoffInput D L γ δ η p (ν v) (r v)) z)).trans
      (mul_le_mul' le_rfl hc)
  exact (XNorm00_source_modulate_le D hI θ _).trans (by
    simpa only [abs_of_nonneg hθ.1] using mul_le_mul' le_rfl hs)

variable {d : ℕ} {D : SumintPar.SumintDatum d}

/-! ## Agreement with the cutoff centres chosen before the mixture -/

/-- `exists_mixLocalized_agreement` with the centres `p` chosen before the mixture. -/
theorem exists_mixLocalized_agreement_unif (hI : 0 < D.S.I) (N : ℕ) {h : ℝ} (hh : 0 < h)
    {A L γ δ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) :
    ∃ p : D.S.VIdx → Fin d → ℝ, ∀ (M : CharMix D.S d) (E : Fin 4 → Mom d),
      (∀ j, ‖E j-D.centre j‖ ≤ 1) → ∀ t : Fin 3 → ℝ,
      (∀ j, t j ∈ Icc (0:ℝ) N) →
      mixLocalized M hI N h L γ δ η a b p E t =
        ((‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card : ℝ):ℂ)*
          ∑' x : D.S.VIdx → Fin d → ℤ, localizedSourceWeight D L a b E x * M.val L E x *
            (∫ τ in D.timeDom hI (t 0) (t 1) (t 2), D.phase L γ δ η x (E 0-E 1) (t 0) τ) := by
  classical
  obtain ⟨p,hp⟩ := exists_inputCutoff_insertion D hD a b
  refine ⟨p,?_⟩
  intro M E hE t ht
  have hinsert (x : D.S.VIdx → Fin d → ℤ) : localizedSourceWeight D L a b E x =
      ((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ):ℂ)*localizedSourceWeight D L a b E x :=
    hp E hE x
  have hzero (x : D.S.VIdx → Fin d → ℤ) (hx : x ∉ inputCutoffBox L p) :
      localizedSourceWeight D L a b E x = 0 := by
    rw [hinsert x,inputCutoff_product_eq_zero hL p x hx,Complex.ofReal_zero,zero_mul]
  unfold mixLocalized
  congr 1
  rw [tsum_eq_sum (s := inputCutoffBox L p) (fun x hx => by rw [hzero x hx,zero_mul,zero_mul])]
  apply Finset.sum_congr rfl
  intro x _
  rw [phaseCellExtension_agreement D hI N hh L γ δ η x (E 0-E 1) t ht, ← hinsert x]

/-- `exists_mixCounted_agreement` with the centres `p` chosen before the mixture. -/
theorem exists_mixCounted_agreement_unif (hd : 1 ≤ d) (hI : 0 < D.S.I) (N : ℕ) {h : ℝ}
    (hh : 0 < h) {A L γ δ η : ℝ} {Dsteps : ℕ} (hA : 1 ≤ A) (hL : 0 < L) (hη : η ≤ 1/3)
    (hD : D.Admissible A L γ η Dsteps) :
    ∃ p : SourceLocalizationLabel D hD → D.S.VIdx → Fin d → ℝ, ∀ (M : CharMix D.S d),
      ∀ E : Fin 4 → Mom d, (∀ j, ‖E j-D.centre j‖ ≤ 1) →
      ∀ t : Fin 3 → ℝ, (∀ j, t j ∈ Icc (0:ℝ) N) →
        mixCounted M hI N h L γ δ η hD p E t = exprMix M hI L γ δ η t E := by
  classical
  choose p hp using fun j : SourceLocalizationLabel D hD =>
    exists_mixLocalized_agreement_unif (δ := δ) hI N hh hL hD j.1 j.2.val
  refine ⟨p,?_⟩
  intro M E hE t ht
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
          ∑' x, G j x := hp j M E hE t ht
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

/-! ## The multiplied localized and counted extensions, output-dependent mixture -/

/-- Copy of `DegenVinePar.XNorm00_mixLocalized_le` for an output-dependent mixture: the mixture frozen at each
output, the Minkowski step over `(ξ, a)` with the output-dependent modulation `ν(ξ) + ζ(a, E v)`. -/
theorem XNorm00_mixLocalized_leOut (hd : 1 ≤ d) (Mo : OutCharMix D.S d) (hI : 0 < D.S.I) (N : ℕ) (h : ℝ)
    {A L γ δ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (p : D.S.VIdx → Fin d → ℝ)
    {V : Type*} [Countable V] (E : V → Fin 4 → Mom d) (θ : ℝ) (B : ℝ≥0∞)
    (hF : ∀ ν : V → D.S.VIdx → Mom d,
      XNorm00 θ (fun t v => weightedSourceExtension D hI N h L γ δ η p (ν v) (E v 0-E v 1) t) ≤ B) :
    XNorm00 θ (fun t v => mixLocalized (Mo.freeze (E v)) hI N h L γ δ η a b p (E v) t) ≤
      (ENNReal.ofReal (∫ ξ, (sourceWeightDecay D L γ η)⁻¹ * coefMajor D L γ η a b ξ) *
        ENNReal.ofReal Mo.mass) * B := by
  classical
  let Cm : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) → ℝ := fun ξ =>
    (sourceWeightDecay D L γ η)⁻¹ * coefMajor D L γ η a b ξ
  have hCmc : Continuous Cm := continuous_const.mul (continuous_coefMajor D hD a b)
  have hCm0 : ∀ ξ, 0 ≤ Cm ξ := fun ξ =>
    mul_nonneg (inv_nonneg.mpr (sourceWeightDecay_pos D hL γ η).le) (coefMajor_nonneg D hL γ η a b ξ)
  let c : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) → V → ℂ := fun ξ v =>
    normalizedSourceCoefficient D L γ η a b (E v 0 - E v 1) ξ
  have hcle : ∀ ξ v, ‖c ξ v‖ ≤ Cm ξ := fun ξ v =>
    norm_normalizedSourceCoefficient_le D hL hD a b _ ξ
  let ω : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) → V → ℂ := fun ξ v =>
    if Cm ξ = 0 then 0 else c ξ v / (Cm ξ : ℂ)
  have hωnorm : ∀ ξ v, ‖ω ξ v‖ ≤ 1 := by
    intro ξ v
    by_cases h0 : Cm ξ = 0
    · simp [ω, h0]
    · simp only [ω, h0, ite_false, norm_div, Complex.norm_real, Real.norm_of_nonneg (hCm0 ξ)]
      exact (div_le_one (lt_of_le_of_ne (hCm0 ξ) (Ne.symm h0))).mpr (hcle ξ v)
  have hωm : ∀ v, Measurable (fun ξ => ω ξ v) := by
    intro v
    apply Measurable.ite (hCmc.measurable (measurableSet_singleton 0)) measurable_const
    exact ((continuous_normalizedSourceCoefficient hd D hD a b _).measurable.div
      (Complex.measurable_ofReal.comp hCmc.measurable))
  have hc_eq : ∀ ξ v, c ξ v = (Cm ξ : ℂ) * ω ξ v := by
    intro ξ v
    by_cases h0 : Cm ξ = 0
    · have : c ξ v = 0 := norm_le_zero_iff.mp ((hcle ξ v).trans h0.le)
      simp [ω, h0, this]
    · simp only [ω, h0, ite_false]
      have : (Cm ξ : ℂ) ≠ 0 := by exact_mod_cast h0
      field_simp
  have hint : Integrable Cm := (integrable_coefMajor D hL hD a b).const_mul _
  have hcongr : (fun t (v : V) => mixLocalized (Mo.freeze (E v)) hI N h L γ δ η a b p (E v) t) =
      fun t v => ∫ q : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) × Mo.α,
        (Cm q.1 : ℂ) * (ω q.1 v *
          ((Real.fourierChar (externalModulation D (fun v' => q.1 (.inl v')) (fun v' => q.1 (.inr v')) (E v)) : ℂ) *
            Mo.u q.2 (E v))) *
          weightedSourceExtension D hI N h L γ δ η p
            (inputModulation D (fun v' => q.1 (.inl v')) (fun v' => q.1 (.inr v')) + Mo.ζ q.2 (E v))
              (E v 0-E v 1) t ∂(volume.prod Mo.μ) := by
    funext t v
    rw [mixLocalized_eq_integral hd (Mo.freeze (E v)) hI N h hL hη hD a b p (E v) t]
    apply integral_congr_ae
    apply ae_of_all
    intro q
    change c q.1 v * _ * _ = _
    rw [hc_eq]
    simp only [OutCharMix.freeze]
    ring
  rw [hcongr]
  have hmain := XNorm00_integral_weightedSourceExtension_leOut (μ := volume.prod Mo.μ) D hI N h hL γ δ η hη p
    (fun (q : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) × Mo.α) (v : V) =>
      inputModulation D (fun v' => q.1 (.inl v')) (fun v' => q.1 (.inr v')) + Mo.ζ q.2 (E v))
    (fun v => ((continuous_sourceInputModulation D).measurable.comp measurable_fst).add
      ((Mo.hζ (E v)).comp measurable_snd))
    (fun v => E v 0 - E v 1)
    (fun q => (Cm q.1 : ℂ)) ((Complex.measurable_ofReal.comp hCmc.measurable).comp measurable_fst)
    (by simpa using (hint.ofReal (𝕜 := ℂ)).mul_prod (integrable_const (1 : ℂ) : Integrable (fun _ : Mo.α => (1:ℂ)) Mo.μ))
    (fun q v => ω q.1 v * ((Real.fourierChar (externalModulation D (fun v' => q.1 (.inl v')) (fun v' => q.1 (.inr v')) (E v)) : ℂ) *
      Mo.u q.2 (E v)))
    (fun v => ((hωm v).comp measurable_fst).mul
      (((continuous_sourceExternalCharacter D (E v)).measurable.comp measurable_fst).mul
        ((Mo.hu (E v)).comp measurable_snd)))
    (fun q v => by
      rw [norm_mul, norm_mul]
      calc _ ≤ 1 * (1 * 1) := mul_le_mul (hωnorm q.1 v)
              (mul_le_mul (norm_source_external_character D q.1 (E v)).le (Mo.hu1 _ _) (norm_nonneg _) zero_le_one)
              (by positivity) zero_le_one
        _ = 1 := by norm_num)
    θ B (fun q => hF _)
  refine hmain.trans ?_
  have hl : (∫⁻ q : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) × Mo.α, ‖(Cm q.1 : ℂ)‖ₑ ∂(volume.prod Mo.μ)) =
      ENNReal.ofReal (∫ a, Cm a) * ENNReal.ofReal Mo.mass := by
    have hCmm : Measurable (fun ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d => ‖(Cm ξ : ℂ)‖ₑ) :=
      (Complex.measurable_ofReal.comp hCmc.measurable).enorm
    rw [lintegral_prod (fun q : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) × Mo.α => ‖(Cm q.1 : ℂ)‖ₑ)
      (hCmm.comp measurable_fst).aemeasurable]
    simp only [lintegral_const]
    rw [lintegral_mul_const _ hCmm]
    congr 1
    · rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hCm0)]
      apply lintegral_congr
      intro a
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hCm0 a)]
    · unfold OutCharMix.mass
      rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hl]

/-- Copy of `DegenVinePar.XNorm00_mixCounted_le` for an output-dependent mixture. -/
theorem XNorm00_mixCounted_leOut (hd : 1 ≤ d) (Mo : OutCharMix D.S d) (hI : 0 < D.S.I) (N : ℕ) (h : ℝ)
    {A L γ δ η : ℝ} {Dsteps : ℕ}
    (hA : 1 ≤ A) (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps)
    (p : SourceLocalizationLabel D hD → D.S.VIdx → Fin d → ℝ)
    {V : Type*} [Countable V] (E : V → Fin 4 → Mom d)
    (hE : ∀ v j, ‖E v j-D.centre j‖ ≤ 1) (θ : ℝ) (B : ℝ≥0∞)
    (hF : ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : V → D.S.VIdx → Mom d),
      XNorm00 θ (fun t v => weightedSourceExtension D hI N h L γ δ η p (ν v) (E v 0-E v 1) t) ≤ B) :
    XNorm00 θ (fun t v => mixCounted (Mo.freeze (E v)) hI N h L γ δ η hD p (E v) t) ≤
      ENNReal.ofReal ((((9:ℝ)^d*A^d)*summedCellFourierFactor d (d+1)*cellFourierFactor d)^D.S.M) *
        (ENNReal.ofReal Mo.mass * B) := by
  let F := fun (j : SourceLocalizationLabel D hD) t v =>
    mixLocalized (Mo.freeze (E v)) hI N h L γ δ η j.1 j.2.val (p j) (E v) t
  apply (XNorm00_count_integral_le θ F
    (fun j v => measurable_mixLocalized (Mo.freeze (E v)) hI N h L γ δ η j.1 j.2.val (p j) (E v))
    (fun j v => integrable_mixLocalized (Mo.freeze (E v)) hI N h hL hη j.1 j.2.val (p j) (E v))
    (fun v => tsum_mixLocalized_mass_lt_top hd (Mo.freeze (E v)) hI N h hA hL hη hD p (E v) (hE v))).trans
  calc
    _ ≤ ∑' j : SourceLocalizationLabel D hD,
        (ENNReal.ofReal (∫ ξ, (sourceWeightDecay D L γ η)⁻¹ * coefMajor D L γ η j.1 j.2.val ξ) *
          ENNReal.ofReal Mo.mass) * B :=
      ENNReal.tsum_le_tsum (fun j => XNorm00_mixLocalized_leOut hd Mo hI N h hL hη hD
        j.1 j.2.val (p j) E θ B (hF (p j)))
    _ = (∑' a, ∑ b ∈ sourceAlternativeLabels D hD a,
        ENNReal.ofReal (∫ ξ, (sourceWeightDecay D L γ η)⁻¹ * coefMajor D L γ η a b ξ)) *
          (ENNReal.ofReal Mo.mass * B) := by
      simp_rw [mul_assoc]
      rw [ENNReal.tsum_mul_right]
      congr 1
      exact tsum_sourceLocalizationLabel D hD (fun a b =>
        ENNReal.ofReal (∫ ξ, (sourceWeightDecay D L γ η)⁻¹ * coefMajor D L γ η a b ξ))
    _ ≤ _ := mul_le_mul' (tsum_normalizedCoefMajor_mass_le hd D hA hL hD) le_rfl

/-- **T2.** Copy of `DegenVinePar.XNorm00Restr_mix_of_kernel_bound` for an output-dependent mixture, from the kernel
bound with an output-dependent modulation. -/
theorem XNorm00Restr_mix_of_kernel_boundOut (hd : 1 ≤ d) (Mo : OutCharMix D.S d)
    (hI : 0 < D.S.I) {A L γ δ η : ℝ} {N : ℕ} (hA : 1 ≤ A) (hL : 0 < L)
    (hη : η ≤ 1/3) (hD : D.Admissible A L γ η N) {h θ : ℝ}
    (hh : h ∈ Ioc (0:ℝ) 1) (hθ : θ ∈ Icc (0:ℝ) 1)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hkernel : ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : sourceOutputSet D L γ η → D.S.VIdx → Mom d) (c : ℝ),
      XNorm00 θ (fun z (v : sourceOutputSet D L γ η) => kernelExtension D hI c h
        (weightedCutoffInput D L γ δ η p (ν v) (v.1 0-v.1 1)) z) ≤ B) :
    XNorm00Restr θ (sourceOutputTimeSet D) (sourceOutputSet D L γ η)
      (fun t v => exprMix (Mo.freeze v) hI L γ δ η t v) ≤
      ENNReal.ofReal ((((9:ℝ)^d*A^d)*summedCellFourierFactor d (d+1)*cellFourierFactor d)^D.S.M)*
        (ENNReal.ofReal Mo.mass *
        (ENNReal.ofReal (2^θ)*ENNReal.ofReal ((((D.S.M:ℝ)+1)*parameterMaximum D)^θ)*
          (ENNReal.ofReal (4^θ)*
            (ENNReal.ofReal (cellMultiplierRealConstant N*((N:ℝ)+5)*h⁻¹*h⁻¹)*B)))) := by
  classical
  let : Fintype (sourceOutputSet D L γ η) := (finite_sourceOutputSet D hL γ η).fintype
  obtain ⟨p,hp⟩ := exists_mixCounted_agreement_unif (δ := δ) hd hI N hh.1 hA hL hη hD
  let F := fun t (v : sourceOutputSet D L γ η) => mixCounted (Mo.freeze v.1) hI N h L γ δ η hD p v.1 t
  have hrestrict : XNorm00Restr θ (sourceOutputTimeSet D) (sourceOutputSet D L γ η)
      (fun t v => exprMix (Mo.freeze v) hI L γ δ η t v) ≤ XNorm00 θ F := by
    apply XNorm00Restr_le_family_extension θ _ _ _ (fun _ h => h) _ F
    intro t ht v hv
    exact hp (Mo.freeze v) v (fun j => (hv.1 j).2) t (sourceOutputTimeSet_subset_cube D hD ht)
  apply hrestrict.trans
  apply XNorm00_mixCounted_leOut hd Mo hI N h hA hL hη hD p
    (fun v : sourceOutputSet D L γ η => v.1) (fun v j => (v.2.1 j).2) θ
  intro q ν
  exact XNorm00_weightedSourceExtension_leOut D hI N hh hθ L γ δ η q ν
    (fun v : sourceOutputSet D L γ η => v.1 0-v.1 1) B hB (fun j => hkernel q ν ((j:ℝ)*h))

end WaveTurbulence.Flower.V5WT
