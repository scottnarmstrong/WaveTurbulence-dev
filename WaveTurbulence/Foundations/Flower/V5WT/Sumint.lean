/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WT.Kernel
public import WaveTurbulence.Foundations.Flower.V5WT.Mix
public import WaveTurbulence.Foundations.Vine.DegenVinePar.ScaledSumintMix
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Mono

/-! # V5W-T T2 (part 2): `sumint` with an output-dependent character-mixture multiplier

Copies by source of main 416902c8 `DegenVinePar/MixSumint.lean`, `SumintMix.lean`, `SumintMixDoubled.lean`,
`ScaledSumintMix.lean` (from `SumintMixParDoubledAt` on) and `VineEstS5C/P4/Final/Mono.lean` (`sumintMixPar_mono`), with
the mixture `M : CharMix` replaced by `Mo : OutCharMix`, frozen at each output in `exprMix (Mo.freeze v)`, the kernel
input `exists_source_kernel_interpolated_boundOut` (T1) and the recombination `XNorm00Restr_mix_of_kernel_boundOut`.
Names gain the suffix `Out`; the algebraic step `exprMix_reweight_scale` is main's, at the frozen mixture.

Exports: `sumintMixParDoubledOut : SumintMixParDoubledOut` (the prefix statement),
`sumintMixParDoubledOut_iff`, `scaledSumintMixOutAt_of`, `sumintMixParOut_mono`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.V5WT

section MixSumint
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
open WaveTurbulence.SumintPar MeasureTheory Set
open scoped ENNReal

/-- TARGET sumint Steps 1--3 for a multiplied sum, before numerical absorption. -/
theorem exists_mix_restriction_interpolated_boundOut (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : SumintSmallness d γ η)
    (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R, ∀ (D : SumintPar.SumintDatum d) (hI : 0 < D.S.I) (A : ℝ),
      1 ≤ A → D.Admissible A L γ η N → ∀ Mo : OutCharMix D.S d,
      XNorm00Restr (2*η^8) (sourceOutputTimeSet D) (sourceOutputSet D L γ η)
        (fun t v => exprMix (Mo.freeze v) hI L γ δ η t v) ≤
      ENNReal.ofReal ((((9:ℝ)^d*A^d)*summedCellFourierFactor d (d+1)*cellFourierFactor d)^D.S.M)*
        (ENNReal.ofReal Mo.mass *
        (ENNReal.ofReal (2^(2*η^8))*ENNReal.ofReal ((((D.S.M:ℝ)+1)*parameterMaximum D)^(2*η^8))*
          (ENNReal.ofReal (4^(2*η^8))*
            (ENNReal.ofReal (cellMultiplierRealConstant N*((N:ℝ)+5)*
              (L^(-partitionExponent η))⁻¹*(L^(-partitionExponent η))⁻¹)*
              ENNReal.ofReal (G^D.S.M*δ^(-(D.S.M:ℝ)/2)*
                L^((D.S.M:ℝ)*((d:ℝ)-γ)-
                  (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))-
                  (1-interpolationWeight η)*(partitionExponent η/20)*(D.M₀:ℝ)+
                  14*(d:ℝ)*interpolationWeight η)))))) := by
  obtain ⟨G,hG,hbound⟩ := exists_source_kernel_interpolated_boundOut d hd γ hγ η hη.eta_pos hη.eta_base
    hη.eta_small hη.gamma_eta hη.sqrt_base τstar hτstar (partitionExponent η)
    (partitionExponent_pos hη.eta_pos) hη.beta_linear hη.beta_pair hη.beta_normal hη.beta_high hη.eight_lt
  refine ⟨G,hG,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hbound⟩ := hbound δ N hδ hτ
  refine ⟨R,hR,?_⟩
  intro L hL D hI A hA hD Mo
  have hLp : 0 < L := by linarith only [hR,hL]
  have hL1 : 1 ≤ L := by linarith only [hR,hL]
  have hh : L^(-partitionExponent η) ∈ Ioc (0:ℝ) 1 :=
    ⟨Real.rpow_pos_of_pos hLp _,Real.rpow_le_one_of_one_le_of_nonpos hL1 (by
      linarith only [partitionExponent_pos hη.eta_pos])⟩
  have hθ : 2*η^8 ∈ Icc (0:ℝ) 1 := ⟨by positivity,by linarith only [hη.eight_lt]⟩
  let : Fintype (sourceOutputSet D L γ η) := (finite_sourceOutputSet D hLp γ η).fintype
  apply XNorm00Restr_mix_of_kernel_boundOut (by omega) Mo hI hA hLp
    (by linarith only [hη.eta_small]) hD hh hθ _ ENNReal.ofReal_lt_top
  intro p ν c
  exact hbound L hL D A hD p (sourceOutputSet D L γ η) ν (fun v => v.1 0-v.1 1)
    (sourceOutputSet_momentum_bounds D hLp γ η) (card_sourceOutputSet_le D hL1 γ η) hI c

/-- **`sumint` for multiplied sums**: the exact restriction estimate, with `C₁` independent of `δ`
and the step count, and the mass of the mixture as a factor. -/
theorem exists_mix_sumint_boundOut (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0:ℝ) 1)
    (η : ℝ) (hη : SumintSmallness d γ η) (A : ℝ) (hA : 1 ≤ A)
    (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R, ∀ (D : SumintPar.SumintDatum d) (hI : 0 < D.S.I),
      D.Admissible A L γ η N → ∀ Mo : OutCharMix D.S d,
      XNorm00Restr (2*η^8) (sourceOutputTimeSet D) (sourceOutputSet D L γ η)
        (fun t v => exprMix (Mo.freeze v) hI L γ δ η t v) ≤
      ENNReal.ofReal (Mo.mass * (C1*parameterMaximum D^(η^6)*(C1*δ^(-(1:ℝ)/2))^D.S.M*
        L^(sourceTargetExponent D γ η))) := by
  obtain ⟨G,hG,hbound⟩ := exists_mix_restriction_interpolated_boundOut d hd γ hγ η hη τstar hτstar
  let C1 := sourceAssemblyConstant d A G
  refine ⟨C1,one_le_sourceAssemblyConstant _ _ _,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hbound⟩ := hbound δ N hδ hτ
  have hηpos := hη.eta_pos
  obtain ⟨Rstep,hRstep,hstep⟩ := exists_constant_le_rpow
    (cellMultiplierRealConstant N*((N:ℝ)+5)) (show 0 < η^7/2 by positivity)
  refine ⟨max R Rstep,hR.trans (le_max_left _ _),?_⟩
  intro L hL D hI hD Mo
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLS : Rstep ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := by linarith only [hR,hLR]
  have hL1 : 1 ≤ L := by linarith only [hR,hLR]
  have hS : 0 ≤ sourceCoefficientBase d A := sourceCoefficientBase_nonneg d hA
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hP : 0 < parameterMaximum D := zero_lt_one.trans_le (one_le_parameterMaximum D hI)
  have hcell : 0 < cellMultiplierRealConstant N := zero_lt_one.trans_le (one_le_cellMultiplierRealConstant N)
  apply (hbound L hLR D hI A hA hD Mo).trans
  have hbudget := source_real_budget_le D hI hA hG hL1 hδ.1 hη N (hstep L hLS)
  change ENNReal.ofReal (sourceCoefficientBase d A^D.S.M)*
    (ENNReal.ofReal Mo.mass *
    (ENNReal.ofReal (2^(2*η^8))*ENNReal.ofReal ((((D.S.M:ℝ)+1)*parameterMaximum D)^(2*η^8))*
      (ENNReal.ofReal (4^(2*η^8))*
        (ENNReal.ofReal (cellMultiplierRealConstant N*((N:ℝ)+5)*
          (L^(-partitionExponent η))⁻¹*(L^(-partitionExponent η))⁻¹)*
          ENNReal.ofReal (G^D.S.M*δ^(-(D.S.M:ℝ)/2)*L^(sourceKernelExponent D γ η)))))) ≤ _
  rw [mul_left_comm]
  have hm := Mo.mass_nonneg
  repeat rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc _ = Mo.mass * (sourceCoefficientBase d A ^ D.S.M * (2 ^ (2 * η ^ 8) * ((((D.S.M : ℝ) + 1) * parameterMaximum D) ^ (2 * η ^ 8)) *
        (4 ^ (2 * η ^ 8) * (cellMultiplierRealConstant N * ((N : ℝ) + 5) * (L ^ (-partitionExponent η))⁻¹ * (L ^ (-partitionExponent η))⁻¹ *
          (G ^ D.S.M * δ ^ (-(D.S.M : ℝ) / 2) * L ^ sourceKernelExponent D γ η))))) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hm
      convert hbudget using 1; ring


/-- `sumint` (parametric weights) with an output-dependent character-mixture multiplier, prefix form. -/
def SumintMixParOut : Prop := WTPrefixA fun A P =>
    ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I), D.Admissible A P.L P.γ P.η P.D →
      D.S.M ≤ P.N 1 ^ 4 → ∀ Mo : OutCharMix D.S P.d,
      let B : Set (Fin 3 → ℝ) := {tt | (∀ c, (D.qOut c : ℝ) ≤ tt c ∧ tt c ≤ D.qOut c + 1) ∧
        max (tt 1) (tt 2) < tt 0}
      let K : Set (Fin 4 → Mom P.d) := {v | (∀ c, (∃ nv : Fin P.d → ℤ, v c = D.wBar +
          latticePoint P.L nv) ∧ ‖v c - D.centre c‖ ≤ 1) ∧ v 0 - v 1 = v 3 - v 2 ∧ v 0 ≠ v 1 ∧
        ‖v 0 - v 1‖ ≤ P.L ^ (-P.γ + P.η)}
      let maxPar : ℝ := ⨆ v, jbr (d := 1) (WithLp.toLp 2 fun _ => D.param v)
      XNorm00Restr (2 * P.η ^ 8) B K (fun tt v => exprMix (Mo.freeze v) hI P.L P.γ P.δ P.η tt v) ≤
        ENNReal.ofReal (Mo.mass * (P.C₁ * maxPar ^ (P.η ^ 6) * (P.C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M *
          P.L ^ ((D.S.M : ℝ) * (P.d - P.γ) -
            P.η ^ 2 * ((Finset.univ.filter fun i => D.S.nor i = false).card + D.M₁) -
            P.η ^ 8 * D.M₀ + P.η ^ 7)))

theorem sumintMixOut : SumintMixParOut := by
  unfold SumintMixParOut
  intro d hd γ hγ
  obtain ⟨η0,hη0,hsmall⟩ := exists_sumintSmallness_threshold d hd γ hγ
  refine ⟨η0,hη0,?_⟩
  intro η hη A hA φin hφin τstar hτstar φ hφ
  obtain ⟨C1,hC1,hbound⟩ := exists_mix_sumint_boundOut d hd γ hγ η (hsmall η hη) A hA τstar hτstar
  refine ⟨C1,hC1,1,by norm_num,?_⟩
  intro ν hν
  refine ⟨1/16,by norm_num,?_⟩
  intro δ hδ N hN hτ
  obtain ⟨R,hR,hbound⟩ := hbound δ N hδ hτ
  refine ⟨1,by norm_num,R,hR,?_⟩
  intro L hL D hI hD hsize Mo
  simpa only [sourceOutputTimeSet,sourceOutputSet,parameterMaximum,sourceTargetExponent,Nat.cast_add]
    using hbound L hL D hI hD Mo

end MixSumint

section Doubled
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
open WaveTurbulence.SumintPar WaveTurbulence WaveTurbulence.VineEstS3 MeasureTheory Finset Set
open scoped ENNReal SchwartzMap

/-- `SumintMixParOut` with the phase at the step `2δ`. -/
def SumintMixParDoubledOut : Prop := WTPrefixA fun A P =>
    ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I), D.Admissible A P.L P.γ P.η P.D →
      D.S.M ≤ P.N 1 ^ 4 → ∀ Mo : OutCharMix D.S P.d,
      let B : Set (Fin 3 → ℝ) := {tt | (∀ c, (D.qOut c : ℝ) ≤ tt c ∧ tt c ≤ D.qOut c + 1) ∧
        max (tt 1) (tt 2) < tt 0}
      let K : Set (Fin 4 → Mom P.d) := {v | (∀ c, (∃ nv : Fin P.d → ℤ, v c = D.wBar +
          latticePoint P.L nv) ∧ ‖v c - D.centre c‖ ≤ 1) ∧ v 0 - v 1 = v 3 - v 2 ∧ v 0 ≠ v 1 ∧
        ‖v 0 - v 1‖ ≤ P.L ^ (-P.γ + P.η)}
      let maxPar : ℝ := ⨆ v, jbr (d := 1) (WithLp.toLp 2 fun _ => D.param v)
      XNorm00Restr (2 * P.η ^ 8) B K (fun tt v => exprMix (Mo.freeze v) hI P.L P.γ (2 * P.δ) P.η tt v) ≤
        ENNReal.ofReal (Mo.mass * (P.C₁ * maxPar ^ (P.η ^ 6) * (P.C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M *
          P.L ^ ((D.S.M : ℝ) * (P.d - P.γ) -
            P.η ^ 2 * ((Finset.univ.filter fun i => D.S.nor i = false).card + D.M₁) -
            P.η ^ 8 * D.M₀ + P.η ^ 7)))

theorem sumintMixParDoubledOut_of (hS : SumintMixParOut) : SumintMixParDoubledOut := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hη⟩ := hS d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη' A hA φin hφin τstar hτ φ hφ => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, hν⟩ := hη η hη' A hA (0 : 𝓢(Mom d, ℝ)) (fun k => le_refl _) (2 * τstar)
    (by linarith) (fun _ => 0) (isWKESolution_zero _)
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν' => ?_⟩
  obtain ⟨δ₀, hδ₀, hδ⟩ := hν ν hν'
  refine ⟨δ₀ / 2, by linarith, fun δ hδ' D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, hL⟩ := hδ (2 * δ) ⟨by linarith [hδ'.1], by linarith [hδ'.2]⟩ D hD
    (by rw [hτD]; ring)
  refine ⟨C₂, hC₂, L₀, hL₀, fun L hLL => ?_⟩
  intro D' hI hAdm hM Mo
  have hN : ∀ k, (WTParams.mk d γ η φin τstar φ C₁ ν δ D C₂ L).Rdown k =
      (WTParams.mk d γ η (0 : 𝓢(Mom d, ℝ)) (2 * τstar) (fun _ => 0) C₁ ν (2 * δ) D C₂ L).Rdown k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp only [WTParams.Rdown, ih]
  have hM' : D'.S.M ≤ (WTParams.mk d γ η (0 : 𝓢(Mom d, ℝ)) (2 * τstar) (fun _ => 0) C₁ ν (2 * δ) D C₂ L).N 1 ^ 4 := by
    have := hM
    simp only [WTParams.N, WTParams.R] at this ⊢
    rwa [← hN]
  have key := hL L hLL D' hI hAdm hM' Mo
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hδpos : 0 < δ := hδ'.1
  have hC : 0 < C₁ := by linarith
  have hpar : 0 ≤ ⨆ v, jbr (d := 1) (WithLp.toLp 2 fun _ => D'.param v) :=
    Real.iSup_nonneg (fun v => Real.sqrt_nonneg _)
  have hrpow : (2 * δ) ^ (-(1 : ℝ) / 2) ≤ δ ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hδpos (by linarith) (by norm_num)
  have hX : 0 ≤ C₁ * (2 * δ) ^ (-(1 : ℝ) / 2) := by positivity
  have hpow : (C₁ * (2 * δ) ^ (-(1 : ℝ) / 2)) ^ D'.S.M ≤ (C₁ * δ ^ (-(1 : ℝ) / 2)) ^ D'.S.M :=
    pow_le_pow_left₀ hX (by gcongr) _
  have hL0 : 0 ≤ L ^ (((D'.S.M : ℝ) * (d - γ) -
            η ^ 2 * ((Finset.univ.filter fun i => D'.S.nor i = false).card + D'.M₁) -
            η ^ 8 * D'.M₀ + η ^ 7)) := Real.rpow_nonneg (by linarith) _
  have hP : 0 ≤ C₁ * (⨆ v, jbr (d := 1) (WithLp.toLp 2 fun _ => D'.param v)) ^ (η ^ 6) :=
    mul_nonneg hC.le (Real.rpow_nonneg hpar _)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hP) hL0)
    Mo.mass_nonneg

/-- **`sumint` with output-dependent character mixtures at the doubled step, for parametric `r`-dependent weights (unconditional).** -/
theorem sumintMixParDoubledOut : SumintMixParDoubledOut := sumintMixParDoubledOut_of sumintMixOut

end Doubled

section Scaled
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
open WaveTurbulence WaveTurbulence.SumintPar WaveTurbulence.VineEstS3Par WaveTurbulence.VineEstS3Par.Eng
  WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS Finset MeasureTheory
open scoped ENNReal

/-- The pointwise form of `SumintMixParDoubledOut`. -/
def SumintMixParDoubledOutAt (A : ℝ) (P : WTParams) : Prop :=
  ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I), D.Admissible A P.L P.γ P.η P.D → D.S.M ≤ P.N 1 ^ 4 →
    ∀ Mo : OutCharMix D.S P.d,
      XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
          (fun tt v => exprMix (Mo.freeze v) hI P.L P.γ (2 * P.δ) P.η tt v) ≤
        ENNReal.ofReal (Mo.mass * sumintRHS P D)

theorem sumintMixParDoubledOut_iff : SumintMixParDoubledOut ↔ WTPrefixA SumintMixParDoubledOutAt := Iff.rfl

/-- **`sumint` for weights of arbitrary size.** -/
def ScaledSumintMixOutAt (A : ℝ) (P : WTParams) : Prop :=
  0 < P.L → ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (Mo : OutCharMix D.S P.d),
    (∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D.S.VIdx → Mom P.d → ℂ), WeightBounds D P.L P.γ P.η a b →
      ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D) →
    D.S.M ≤ P.N 1 ^ 4 →
    ∀ (w : Row D → Mom P.d → Mom P.d → ℂ) (s : Row D → ℝ), (∀ ρ, 0 ≤ s ρ) → RowBounds D w s →
      XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt v => exprMix (D := reweight D w) (Mo.freeze v) hI P.L P.γ (2 * P.δ) P.η tt v) ≤
      ENNReal.ofReal (∏ ρ, (s ρ * P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ENNReal.ofReal (Mo.mass * sumintRHS P D)


theorem scaledSumintMixOutAt_of {A : ℝ} {P : WTParams} (h : SumintMixParDoubledOutAt A P) : ScaledSumintMixOutAt A P := by
  intro hL D hI Mo hAdm hM w s hs0 hS
  by_cases hz : ∃ ρ, s ρ = 0
  · -- a zero weight kills the expression
    obtain ⟨ρ₀, hρ₀⟩ := hz
    have hw0 : (∃ v, ∀ r, w (Sum.inl v) r = 0) ∨ (∃ v, w (Sum.inr v) 0 = 0) := by
      cases ρ₀ with
      | inl v =>
        refine Or.inl ⟨v, fun r => VineEstS3.Eng.eq_zero_of_SNorm_eq_zero (Λ₁ := D.wN) (Λ₂ := D.wDec)
          (le_antisymm ?_ bot_le)⟩
        simpa [hρ₀] using hS.1 v r
      | inr v =>
        refine Or.inr ⟨v, VineEstS3.Eng.eq_zero_of_SNorm_eq_zero (Λ₁ := D.wN) (Λ₂ := 0) (le_antisymm ?_ bot_le)⟩
        simpa [hρ₀] using hS.2 v
    have hprod : ∏ ρ, (s ρ * P.L ^ (weightExp P.d P.γ P.η * rowG D ρ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ ρ₀) (by simp [hρ₀])
    rw [hprod]
    simp only [ENNReal.ofReal_zero, zero_mul]
    have hz2 : (fun tt v => exprMix (D := reweight D w) (Mo.freeze v) hI P.L P.γ (2 * P.δ) P.η tt v) =
        fun _ _ => (0 : ℂ) := by
      funext tt v
      unfold exprMix
      have : ∀ x : D.S.VIdx → (Fin P.d → ℤ),
          (∏ v', (reweight D w).wK v' (v 0 - v 1) ((reweight D w).kVec P.L x v v') *
            (reweight D w).wL v' ((reweight D w).ℓVec P.L x v v')) = 0 := by
        intro x
        rcases hw0 with ⟨v', h0⟩ | ⟨v', h0⟩
        · exact Finset.prod_eq_zero (Finset.mem_univ v') (by simp [reweight, h0])
        · exact Finset.prod_eq_zero (Finset.mem_univ v') (by simp [reweight, h0])
      simp only [this, mul_zero, zero_mul, tsum_zero]
    rw [hz2]
    exact (VineEstS3.Eng.XNorm00Restr_zero _ _ _).le
  · have hz' : ∀ ρ, s ρ ≠ 0 := fun ρ h0 => hz ⟨ρ, h0⟩
    have hpos : ∀ ρ, 0 < s ρ := fun ρ => lt_of_le_of_ne (hs0 ρ) (Ne.symm (hz' ρ))
    set nn : Row D → ℝ := fun ρ => s ρ * P.L ^ (weightExp P.d P.γ P.η * rowG D ρ) with hnn
    have hnpos : ∀ ρ, 0 < nn ρ := fun ρ => mul_pos (hpos ρ) (Real.rpow_pos_of_pos hL _)
    set w' : Row D → Mom P.d → Mom P.d → ℂ := fun ρ r k => ((nn ρ)⁻¹ : ℝ) * w ρ r k with hw'
    have key : ∀ ρ (Λ₁ Λ₂ : ℕ) (r : Mom P.d), SNorm Λ₁ Λ₂ (w ρ r) ≤ ENNReal.ofReal (s ρ) →
        SNorm Λ₁ Λ₂ (w' ρ r) ≤ ENNReal.ofReal (P.L ^ (-weightExp P.d P.γ P.η * rowG D ρ)) := by
      intro ρ Λ₁ Λ₂ r hb
      have h1 := VineEstS3.Eng.SNorm_smul_le Λ₁ Λ₂ (((nn ρ)⁻¹ : ℝ) : ℂ) (w ρ r)
      refine h1.trans ?_
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (hnpos ρ).le)]
      refine (mul_le_mul_right hb _).trans ?_
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 (hnpos ρ).le)]
      refine le_of_eq (congrArg ENNReal.ofReal ?_)
      rw [hnn]
      simp only
      rw [neg_mul, Real.rpow_neg hL.le]
      have hs' := hz' ρ
      have hX : P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
      field_simp
    have hwb : WeightBounds D P.L P.γ P.η (fun v => w' (Sum.inl v)) (fun v => w' (Sum.inr v) 0) :=
      fun v => ⟨fun r => key (Sum.inl v) _ _ r (hS.1 v r), key (Sum.inr v) _ _ 0 (hS.2 v)⟩
    have hAdm' := hAdm D.param (fun v => w' (Sum.inl v)) (fun v => w' (Sum.inr v) 0) hwb
    have key2 := h (reweight D w') hI hAdm' hM Mo
    have hww : w = fun ρ r k => ((nn ρ : ℝ) : ℂ) * w' ρ r k := by
      funext ρ r k
      simp only [hw']
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (hnpos ρ).ne', Complex.ofReal_one, one_mul]
    have hscale : (fun tt v => exprMix (D := reweight D w) (Mo.freeze v) hI P.L P.γ (2 * P.δ) P.η tt v) =
        fun tt v => (((∏ ρ, nn ρ : ℝ)) : ℂ) *
          exprMix (D := reweight D w') (Mo.freeze v) hI P.L P.γ (2 * P.δ) P.η tt v := by
      funext tt v
      conv_lhs => rw [hww]
      rw [exprMix_reweight_scale D (fun ρ => ((nn ρ : ℝ) : ℂ)) w' (Mo.freeze v) hI P.L P.γ (2 * P.δ) P.η tt v,
        Complex.ofReal_prod]
    rw [hscale]
    refine (VineEstS3.Eng.XNorm00Restr_const_mul_le _ _ _ _ _).trans ?_
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Finset.prod_nonneg fun ρ _ => (hnpos ρ).le)]
    exact mul_le_mul_right key2 _


end Scaled

section Mono
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVinePar MeasureTheory Set
open WaveTurbulence.VineEstS5C.P4.Final
open scoped ENNReal

/-- Copy of `VineEstS5C.P4.Final.sumintMixPar_mono` for the output-dependent statement. -/
theorem sumintMixParOut_mono (A : ℝ) : LargeConstantMonotone (SumintMixParDoubledOutAt A) := by
  intro P C₁ C₂ hC hC₂ hδ hL hCC hCC₂ hsource D hI hAdm hM Mo
  have hc0 : 0 ≤ P.C₁ := by linarith
  have hL0 : 0 ≤ P.L := by linarith
  have h := hsource D hI hAdm (by simpa using hM) Mo
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_left (sumintRHSPar_mono P D hc0 hCC hδ.le hL0) Mo.mass_nonneg

end Mono

end WaveTurbulence.Flower.V5WT
