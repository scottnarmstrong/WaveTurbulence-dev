/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Fam.Gain
public import WaveTurbulence.Foundations.Flower.Cases.Top
public import WaveTurbulence.Foundations.FC23.ExtractionThresholds
public import WaveTurbulence.Foundations.FC23.PrefixTools
public import WaveTurbulence.Foundations.FC23.StageOrderGrowth
/-! # FL-FAM: from the prefix form of the cores to the prefix form of the families. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Fam
open Set Filter WaveTurbulence.Flower.Cases

theorem one_le_loB' (P : WTParams) : 1 ≤ loB P := by
  have h1 := one_le_Ulow P
  have h2 : 0 ≤ cgen P.d (40 * P.d) := by
    by_cases h : 1 ≤ P.d ∧ 40 * P.d ≤ 40 * P.d
    · exact cgen_nonneg h.1 _ h.2
    · unfold cgen; rw [dif_neg h]
  unfold loB; linarith

/-- A dummy parameter set carrying only `d, τ*, φ`. -/
def mkP (d : ℕ) (τ : ℝ) (φ : ℝ → SchwartzMap (Mom d) ℝ) : WTParams :=
  ⟨d, 0, 0, 0, τ, φ, 0, 0, 0, 0, 0, 0⟩

theorem loB_mkP (P : WTParams) : loB (mkP P.d P.τstar P.φ) = loB P := rfl

/-- The `δ`-threshold: `6 · loB · δ^{2ν} ≤ 1`. -/
def deltaThr (d : ℕ) (τ : ℝ) (φ : ℝ → SchwartzMap (Mom d) ℝ) (ν : ℝ) : ℝ :=
  (6 * loB (mkP d τ φ))⁻¹ ^ ((2 * ν)⁻¹)

theorem deltaThr_pos (d : ℕ) (τ : ℝ) (φ : ℝ → SchwartzMap (Mom d) ℝ) (ν : ℝ) : 0 < deltaThr d τ φ ν := by
  unfold deltaThr
  have := one_le_loB' (mkP d τ φ)
  exact Real.rpow_pos_of_pos (by positivity) _

theorem small_of_thr (P : WTParams) (hν : 0 < P.ν) (hδ : 0 < P.δ)
    (h : P.δ ≤ deltaThr P.d P.τstar P.φ P.ν) : 6 * loB P * P.δ ^ (2 * P.ν) ≤ 1 := by
  have hlo := one_le_loB' P
  have h1 : P.δ ^ (2 * P.ν) ≤ ((6 * loB P)⁻¹ ^ ((2 * P.ν)⁻¹)) ^ (2 * P.ν) := by
    have := Real.rpow_le_rpow hδ.le (by simpa only [deltaThr, loB_mkP] using h) (by positivity : (0 : ℝ) ≤ 2 * P.ν)
    exact this
  rw [← Real.rpow_mul (by positivity), inv_mul_cancel₀ (by positivity), Real.rpow_one] at h1
  have : 6 * loB P * P.δ ^ (2 * P.ν) ≤ 6 * loB P * (6 * loB P)⁻¹ :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  rwa [mul_inv_cancel₀ (by positivity)] at this

theorem prefixP_combo {Q S : ℕ → WTParams → Prop} (hQ : WTPrefixP Q)
    (hS : ∀ (Pm : ℕ), 1 ≤ Pm → ∀ (P : WTParams), 3 ≤ P.d → 0 < P.ν → 0 < P.δ →
      P.δ ≤ deltaThr P.d P.τstar P.φ P.ν → IsWKESolution P.φin P.τstar P.φ →
      P.τstar = (P.D : ℝ) * P.δ → 
      (∀ L : ℝ, P.L ≤ L → Q Pm {P with L := L}) →
      ∀ᶠ L : ℝ in atTop, S Pm {P with L := L}) : WTPrefixP S := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hQ⟩ := hQ d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  obtain ⟨C₁, hC₁, ν₀, hν₀, hQ⟩ := hQ η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨P₀, hQ⟩ := hQ ν hν
  refine ⟨max P₀ 1, fun Pm hPm => ?_⟩
  obtain ⟨δ₀, hδ₀, hQ⟩ := hQ Pm ((le_max_left _ _).trans hPm)
  refine ⟨min δ₀ (deltaThr d τ φ ν), lt_min hδ₀ (deltaThr_pos d τ φ ν), ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, hQ⟩ := hQ δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD htime
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp
    (hS Pm ((le_max_right _ _).trans hPm) ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L₀⟩ hd hν.1 hδ.1
      (hδ.2.trans (min_le_right _ _)) hsol htime (fun L hL => hQ L hL))
  exact ⟨C₂, hC₂, max L₀ L₁, hL₀.trans (le_max_left _ _),
    fun L hL => hL₁ L ((le_max_right _ _).trans hL)⟩

/-- The fixed-parameter side conditions of `filt_fixed` / `gain_fixed`. -/
def FixedHyps (Bc : ℕ → ℝ) (Pm : ℕ) (P : WTParams) : Prop :=
  3 ≤ P.d ∧ ContinuousOn P.φ (Icc 0 P.τstar) ∧ P.τstar = (P.D : ℝ) * P.δ ∧ 0 < P.δ ∧ 4 ≤ P.L ∧
  6 * loB P * P.δ ^ (2 * P.ν) ≤ 1 ∧
  (∀ p < P.D, ∀ N ≤ P.N (p + 1) ^ 4, 4 * ((2 * N + 1 : ℕ) : ℝ) ≤ P.L) ∧
  (∀ p < P.D, Mgen P.d (40 * P.d) ≤ P.L ∧ Mgen P.d (Wt P p) ≤ P.L) ∧
  (∀ p < P.D, Kconst P Pm p ≤ P.L ^ (epsBc Bc P.d * Pm))

/-- The side conditions hold for all large `L`. -/
theorem fixedHyps_eventually (Bc : ℕ → ℝ) (hBc : ∀ d, 3 ≤ d → Bc d + 80 * d + 3 < (100 * (d : ℝ)) ^ 3)
    (Pm : ℕ) (hPm : 1 ≤ Pm) (P : WTParams) (hd : 3 ≤ P.d) (hν : 0 < P.ν) (hδ : 0 < P.δ)
    (hthr : P.δ ≤ deltaThr P.d P.τstar P.φ P.ν) (hsol : IsWKESolution P.φin P.τstar P.φ)
    (htime : P.τstar = (P.D : ℝ) * P.δ) :
    ∀ᶠ L : ℝ in atTop, FixedHyps Bc Pm {P with L := L} := by
  have hd1 : 1 ≤ P.d := by omega
  let X := 4 * (40 * P.d) ^ (2 * P.D + 2)
  have hsm := small_of_thr P hν hδ hthr
  have hε : 0 < epsBc Bc P.d * Pm := by
    have := hBc P.d hd
    unfold epsBc
    have h1 : 0 < (100 * (P.d : ℝ)) ^ 3 - Bc P.d - 80 * P.d - 3 := by linarith
    have h2 : (0 : ℝ) < Pm := by exact_mod_cast hPm
    exact mul_pos h1 h2
  have hdeg := FC23.eventually_degree_cost (C := 4) (b := 1) (by norm_num) (by norm_num) 1 X
  have hM : ∀ᶠ L : ℝ in atTop, ∀ p ∈ Finset.range P.D,
      Mgen P.d (40 * P.d) ≤ L ∧ Mgen P.d (Wt P p) ≤ L := by
    apply (eventually_all_finset _).mpr
    intro p _
    filter_upwards [eventually_ge_atTop (Mgen P.d (40 * P.d)), eventually_ge_atTop (Mgen P.d (Wt P p))]
      with L h1 h2 using ⟨h1, h2⟩
  have hK : ∀ᶠ L : ℝ in atTop, ∀ p ∈ Finset.range P.D, Kconst P Pm p ≤ L ^ (epsBc Bc P.d * Pm) := by
    apply (eventually_all_finset _).mpr
    intro p _
    exact (tendsto_rpow_atTop hε).eventually_ge_atTop _
  filter_upwards [hdeg, hM, hK, eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with L hdeg hM hK hL4 hlog
  refine ⟨hd, hsol.1, htime, hδ, hL4, hsm, ?_, fun p hp => hM p (Finset.mem_range.mpr hp),
    fun p hp => hK p (Finset.mem_range.mpr hp)⟩
  intro p hp N hN
  have hNlog : (N : ℝ) ≤ Real.log L ^ X := by
    apply (show (N : ℝ) ≤ ({P with L := L} : WTParams).N (p + 1) ^ 4 by exact_mod_cast hN).trans
    exact FC23.N_quartic_le_log_pow {P with L := L} hd1 hlog (p + 1)
  have := hdeg N hNlog
  simpa only [pow_one, Real.rpow_one] using this

/-- The filtered family with the explicit constants `Cfam`, `Ufam`. -/
theorem filtFamily_explicit (Bc : ℕ → ℝ)
    (hBc : ∀ d, 3 ≤ d → Bc d + 80 * d + 3 < (100 * (d : ℝ)) ^ 3)
    (H : WTPrefixP (FlowerCoreFiltAt Bc)) : WTPrefixP (FlowerFiltFamilyAt Cfam Ufam) := by
  refine prefixP_combo H ?_
  intro Pm hPm P hd hν hδ hthr hsol htime hQ
  filter_upwards [fixedHyps_eventually Bc hBc Pm hPm P hd hν hδ hthr hsol htime,
    eventually_ge_atTop P.L] with L hF hL
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hF
  exact filt_fixed Bc Pm {P with L := L} h1 h2 h3 h4 h5 h6 h7 h8 h9 (hQ L hL)

/-- **`gainFamily_of_core`** (same `C`, `U`). -/
theorem gainFamily_of_core (Bc : ℕ → ℝ)
    (hBc : ∀ d, 3 ≤ d → Bc d + 80 * d + 3 < (100 * (d : ℝ)) ^ 3)
    (H : WTPrefixP (FlowerCoreGainAt Bc)) : WTPrefixP (FlowerGainFamilyAt Cfam Ufam) := by
  refine prefixP_combo H ?_
  intro Pm hPm P hd hν hδ hthr hsol htime hQ
  filter_upwards [fixedHyps_eventually Bc hBc Pm hPm P hd hν hδ hthr hsol htime,
    eventually_ge_atTop P.L] with L hF hL
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hF
  exact gain_fixed Bc Pm {P with L := L} h1 h2 h3 h4 h5 h6 h7 h8 h9 (hQ L hL)

/-- **`layergardenFlower_v3` from the two analytic cores.** -/
theorem layergardenFlower_v3_of_cores (Bc : ℕ → ℝ)
    (hBc : ∀ d, 3 ≤ d → Bc d + 80 * d + 3 < (100 * (d : ℝ)) ^ 3)
    (hF : WTPrefixP (FlowerCoreFiltAt Bc)) (hG : WTPrefixP (FlowerCoreGainAt Bc)) :
    V2Chain.LayergardenFlowerV3Gate := by
  exact layergardenFlower_v3_of_families Cfam Ufam Cfam_pos Ufam_pos (filtFamily_explicit Bc hBc hF)
    (gainFamily_of_core Bc hBc hG)

end WaveTurbulence.Flower.Fam
