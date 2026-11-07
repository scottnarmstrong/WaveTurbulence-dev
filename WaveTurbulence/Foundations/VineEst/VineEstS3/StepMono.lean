/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PrefixConjunction
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Gate30d
public import WaveTurbulence.Foundations.VineEst.VineEstS3.IncoherentGate
public import WaveTurbulence.Foundations.Vine.DegenVine.ScaledSumintMix
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ScaledSumint

/-! # Large-constant monotonicity of the three prefix statements used by Step 3

`LargeConstantMonotone A` (lg-spine `PrefixConjunction`) says that `A P` implies `A P'` for
`P' = {P with C₁ := c₁, C₂ := c₂}` with `c₁ ≥ C₁`, `c₂ ≥ C₂`.  It is what lets independently quantified
prefixes (the `sumint` statement with `ε`-mixtures, B2.2 and the 30d Prop 6.1 gate) be combined (`prefix_and`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine MeasureTheory Set
open scoped ENNReal

@[simp] theorem Rdown_largeConstants (P : WTParams) (C₁ C₂ : ℝ) (k : ℕ) :
    ({P with C₁ := C₁, C₂ := C₂} : WTParams).Rdown k = P.Rdown k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [WTParams.Rdown, ih]

@[simp] theorem N_largeConstants (P : WTParams) (C₁ C₂ : ℝ) (p : ℕ) :
    ({P with C₁ := C₁, C₂ := C₂} : WTParams).N p = P.N p := by
  simp only [WTParams.N, WTParams.R, Rdown_largeConstants]

theorem source_coefficient_mono {C C' δ : ℝ} (hC : 0 ≤ C) (hCC : C ≤ C')
    (hδ : 0 ≤ δ) (n : ℕ) : C * (C * δ) ^ n ≤ C' * (C' * δ) ^ n := by
  exact mul_le_mul hCC (pow_le_pow_left₀ (mul_nonneg hC hδ)
    (mul_le_mul_of_nonneg_right hCC hδ) n) (by positivity) (hC.trans hCC)

theorem regBound_largeConstants_mono (P : WTParams) {C₁ C₂ : ℝ}
    (hC : 0 ≤ P.C₁) (hCC : P.C₁ ≤ C₁) (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) (n g : ℕ) :
    regBound P n g ≤ regBound {P with C₁ := C₁, C₂ := C₂} n g := by
  unfold regBound
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (source_coefficient_mono hC hCC hδ n) (Real.rpow_nonneg hL _)

theorem sourceSeparated_mono (P : WTParams) {C₁ C₂ : ℝ} (hC : 0 ≤ P.C₁) (hCC : P.C₁ ≤ C₁) {n W : ℕ}
    {B : Set (Fin 2 → ℝ)} {f : (Fin 2 → ℝ) → Mom P.d → ℂ} (h : SourceSeparated P n W B f) :
    SourceSeparated {P with C₁ := C₁, C₂ := C₂} n W B f := by
  obtain ⟨m, J, M, hm, hf, hJ, hM⟩ := h
  have hmono : P.C₁ * P.C₁ ^ n ≤ C₁ * C₁ ^ n := by
    exact mul_le_mul hCC (pow_le_pow_left₀ hC hCC n) (by positivity) (hC.trans hCC)
  exact ⟨m, J, M, hm, hf, fun i => (hJ i).trans (ENNReal.ofReal_le_ofReal hmono),
    fun i => (hM i).trans (ENNReal.ofReal_le_ofReal hmono)⟩

theorem incoherentGate_mono : LargeConstantMonotone IncoherentGateAt := by
  intro P C₁ C₂ hC hC₂ hδ hL hCC hCC₂ hsource p hp R hR n hn
  rw [N_largeConstants] at hn
  have hc0 : 0 ≤ P.C₁ := by linarith
  have hL0 : 0 ≤ P.L := by linarith
  constructor
  · intro Q hw hsize LG hQ hlayer q q' hq hq' hroot hroot' hi
    apply ((hsource p hp R hR n hn).1 Q hw hsize LG hQ hlayer q q' hq hq' hroot hroot' hi).trans
    exact regBound_largeConstants_mono P hc0 hCC hδ.le hL0 n _
  · intro X hw hsize LG hX hlayer q q' hqq' hqp hroot hlone hi
    apply ((hsource p hp R hR n hn).2 X hw hsize LG hX hlayer q q' hqq' hqp hroot hlone hi).trans
    exact regBound_largeConstants_mono P hc0 hCC hδ.le hL0 n _

theorem coherentGate_mono : LargeConstantMonotone CoherentGateAt := by
  intro P C₁ C₂ hC hC₂ hδ hL hCC hCC₂ hsource p hp R hR n hn
  rw [N_largeConstants] at hn
  have hc0 : 0 ≤ P.C₁ := by linarith
  have hL0 : 0 ≤ P.L := by linarith
  obtain ⟨hc, ht⟩ := hsource p hp R hR n hn
  constructor
  · intro Q LG q q' hqq hqp hsize hcoh
    obtain ⟨h1, h2, h3⟩ := hc Q LG q q' hqq hqp hsize hcoh
    exact ⟨h1.trans (regBound_largeConstants_mono P hc0 hCC hδ.le hL0 n _), h2,
      sourceSeparated_mono P hc0 hCC h3⟩
  · intro X LG q q' hqq hqp hsize hcoh
    obtain ⟨h1, h2, h3⟩ := ht X LG q q' hqq hqp hsize hcoh
    exact ⟨h1.trans (regBound_largeConstants_mono P hc0 hCC hδ.le hL0 n _), h2,
      sourceSeparated_mono P hc0 hCC h3⟩

theorem sumintRHS_mono (P : WTParams) (D : SumintDatum P.d) {C₁ C₂ : ℝ} (hC : 0 ≤ P.C₁) (hCC : P.C₁ ≤ C₁)
    (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) :
    sumintRHS P D ≤ sumintRHS {P with C₁ := C₁, C₂ := C₂} D := by
  unfold sumintRHS
  have h1 : 0 ≤ maxPar D ^ (P.η ^ 6) := by
    unfold maxPar
    exact Real.rpow_nonneg (Real.iSup_nonneg fun v => by unfold jbr; positivity) _
  have h2 : 0 ≤ P.δ ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hδ _
  have h3 : 0 ≤ P.L ^ ((D.S.M : ℝ) * (P.d - P.γ) -
      P.η ^ 2 * ((Finset.univ.filter fun i => D.S.nor i = false).card + D.M₁) - P.η ^ 8 * D.M₀ + P.η ^ 7) :=
    Real.rpow_nonneg hL _
  have hC' : 0 ≤ C₁ := hC.trans hCC
  have hA : P.C₁ * maxPar D ^ (P.η ^ 6) ≤ C₁ * maxPar D ^ (P.η ^ 6) := mul_le_mul_of_nonneg_right hCC h1
  have hB : (P.C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M ≤ (C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M :=
    pow_le_pow_left₀ (mul_nonneg hC h2) (mul_le_mul_of_nonneg_right hCC h2) _
  exact mul_le_mul (mul_le_mul hA hB (pow_nonneg (mul_nonneg hC h2) _) (mul_nonneg hC' h1)) le_rfl h3
    (mul_nonneg (mul_nonneg hC' h1) (pow_nonneg (mul_nonneg hC' h2) _))

theorem sumintMix_mono (A : ℝ) : LargeConstantMonotone (SumintMixDoubledAt A) := by
  intro P C₁ C₂ hC hC₂ hδ hL hCC hCC₂ hsource D hI cfs cs hAdm hM M
  have hc0 : 0 ≤ P.C₁ := by linarith
  have hL0 : 0 ≤ P.L := by linarith
  have h := hsource D hI cfs cs hAdm (by simpa using hM) M
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_left (sumintRHS_mono P D hc0 hCC hδ.le hL0) M.mass_nonneg

end WaveTurbulence.VineEstS3
