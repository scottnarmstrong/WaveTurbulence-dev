/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Lead
public import WaveTurbulence.Foundations.Spine.PL2330Draft.Triangle
public import WaveTurbulence.Foundations.Spine.PL2330Draft.Step
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs
public import WaveTurbulence.Foundations.Stage1.Represents.RepSup2
public import WaveTurbulence.Foundations.Spine.RestrictionNormCalculus
public import WaveTurbulence.Foundations.Spine.LeafwiseSeparationBound
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the restriction norm of a leafwise separated approximation

`LeafwiseSeparated P n W B f cost` (TARGET Prop 6.1, L1103-L1110, leafwise) gives
`‖f‖_{𝔛^{θ,30d,W}(B)} ≤ 2ⁿ c_Leib δⁿ (C₁^{n+1})(C₁^{n+1} cost)` for `θ ≤ 1 - η`: this is
`VineEstS3.rN_sourceSeparated_le` with the momentum-factor bound `C₁^{n+1} cost` in place of `C₁^{n+1}`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.PL2330 WaveTurbulence.LGSpine WaveTurbulence.Fourier
  WaveTurbulence.NormBridgeScratch WaveTurbulence.VineEstS3 MeasureTheory Set
open WaveTurbulence.VineEstS3.FS
open scoped ENNReal

theorem spatialNorm_sep_le' {P : WTParams} (hd : 1 ≤ P.d) {n W : ℕ} {M : Mom P.d → ℝ} {Mb : ℝ}
    (hM : SNormR (30 * P.d) W M ≤ ENNReal.ofReal Mb) (hδ : 0 ≤ P.δ) :
    spatialNorm (30 * P.d) W (fun k => ((P.δ ^ n : ℂ) * (M k : ℂ))) ≤
      ENNReal.ofReal (P.δ ^ n * Mb) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  refine (spatialNorm_const_mul_le hΛ _ _).trans ?_
  have h1 : spatialNorm (30 * P.d) W (fun k => (M k : ℂ)) ≤ ENNReal.ofReal Mb := by
    unfold SNormR at hM
    rwa [SNorm_eq_spatialNorm] at hM
  have h2 : ‖((P.δ ^ n : ℂ))‖ₑ = ENNReal.ofReal (P.δ ^ n) := by
    rw [← ofReal_norm]; congr 1; simp [abs_of_nonneg hδ]
  rw [h2]
  calc ENNReal.ofReal (P.δ ^ n) * spatialNorm (30 * P.d) W (fun k => (M k : ℂ))
      ≤ ENNReal.ofReal (P.δ ^ n) * ENNReal.ofReal Mb := mul_le_mul_right h1 _
    _ = _ := (ENNReal.ofReal_mul (pow_nonneg hδ n)).symm

theorem rN_leafSepTerm_le {P : WTParams} (hd : 1 ≤ P.d) {n W : ℕ} {M : Mom P.d → ℝ}
    {J : (Fin 2 → ℝ) → ℂ} {B : Set (Fin 2 → ℝ)} {θ : ℝ} (hθ : θ ≤ 1 - P.η) (hC : 0 ≤ P.C₁)
    (hδ : 0 ≤ P.δ) {cost : ℝ} (hcost : 0 ≤ cost)
    (hM : SNormR (30 * P.d) W M ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n * cost))
    (hJ : XNorm00Restr (V := Unit) (1 - P.η) B Set.univ (fun ts _ => J ts) ≤
      ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) :
    rN θ (30 * P.d) W B (fun t k => ((P.δ ^ n : ℂ) * (M k : ℂ)) * J t) ≤
      ENNReal.ofReal (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n * cost)) *
        (P.C₁ * P.C₁ ^ n)) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hJi : rN θ (30 * P.d) 0 B (fun t (_ : Mom P.d) => J t) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n) := by
    refine (rN_const_param_le B J).trans ?_
    have h1 := mixedRestrictionNorm00_mono_time (V := Unit) hθ B Set.univ (fun ts _ => J ts)
    have h2 := (XNorm00Restr_eq_mixedRestrictionNorm00 (1 - P.η) B Set.univ
      (fun (ts : Fin 2 → ℝ) (_ : Unit) => J ts)).symm.le
    exact h1.trans (h2.trans hJ)
  have hCn : 0 ≤ P.δ ^ n * (P.C₁ * P.C₁ ^ n * cost) := by positivity
  exact restr_mul_w_le hΛ hd (θ := θ) W B (c := fun k => ((P.δ ^ n : ℂ) * (M k : ℂ)))
    (fun t _ => J t) hCn (spatialNorm_sep_le' hd hM hδ) hJi

theorem rN_leafwiseSeparated_le {P : WTParams} {n W : ℕ} {B : Set (Fin 2 → ℝ)}
    {f : (Fin 2 → ℝ) → Mom P.d → ℂ} {cost : ℝ} (hf : LeafwiseSeparated P n W B f cost)
    (hd : 1 ≤ P.d) {θ : ℝ} (hθ : θ ≤ 1 - P.η) (hC : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hcost : 0 ≤ cost) :
    rN θ (30 * P.d) W B f ≤
      ENNReal.ofReal (2 ^ n * (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n * cost)) *
        (P.C₁ * P.C₁ ^ n))) := by
  classical
  obtain ⟨m, J, M, hm, hfeq, hJ, hM⟩ := hf
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hsum : ∀ ts ∈ B, ∀ k ∈ (Set.univ : Set (Mom P.d)), f ts k =
      ∑ i ∈ (Finset.univ : Finset (Fin m)), ((P.δ ^ n : ℂ) * (M i k : ℂ)) * J i ts := by
    intro ts hts k _
    rw [hfeq ts hts k]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  set Fi : Fin m → (Fin 2 → ℝ) → Mom P.d → ℂ :=
    fun i t k => ((P.δ ^ n : ℂ) * (M i k : ℂ)) * J i t with hFi
  have e1 : rN θ (30 * P.d) W B f =
      rN θ (30 * P.d) W B (fun t k => ∑ i ∈ (Finset.univ : Finset (Fin m)), Fi i t k) :=
    restr_congr (θ := θ) (Λ := 30 * P.d) (Λ₂ := W) B Set.univ hsum
  have e2 : rN θ (30 * P.d) W B (fun t k => ∑ i ∈ (Finset.univ : Finset (Fin m)), Fi i t k) ≤
      ∑ i ∈ (Finset.univ : Finset (Fin m)), rN θ (30 * P.d) W B (Fi i) :=
    restr_finsetSum_le (θ := θ) (Λ := 30 * P.d) (Λ₂ := W) hΛ Finset.univ B Set.univ Fi
  have e3 : ∀ i ∈ (Finset.univ : Finset (Fin m)), rN θ (30 * P.d) W B (Fi i) ≤
      ENNReal.ofReal (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n * cost)) *
        (P.C₁ * P.C₁ ^ n)) :=
    fun i _ => rN_leafSepTerm_le hd hθ hC hδ hcost (hM i) (hJ i)
  refine e1.trans_le (e2.trans ((Finset.sum_le_sum e3).trans ?_))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnn : 0 ≤ cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n * cost)) *
      (P.C₁ * P.C₁ ^ n) := by
    have := cLeib_nonneg P.d (30 * P.d)
    positivity
  calc (m : ℝ≥0∞) * ENNReal.ofReal (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n * cost)) *
        (P.C₁ * P.C₁ ^ n))
      ≤ 2 ^ n * ENNReal.ofReal (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n * cost)) *
        (P.C₁ * P.C₁ ^ n)) := by
        gcongr; exact_mod_cast hm
    _ = _ := by
        rw [show (2 : ℝ≥0∞) ^ n = ENNReal.ofReal (2 ^ n) by
          rw [ENNReal.ofReal_pow (by norm_num)]; simp, ← ENNReal.ofReal_mul (by positivity)]

/-- The mass bound of a leafwise separated app, as an `ENNReal`. -/
noncomputable def sepMass (P : WTParams) (n : ℕ) (cost : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ n * (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n * cost)) *
    (P.C₁ * P.C₁ ^ n)))

end WaveTurbulence.Represents
