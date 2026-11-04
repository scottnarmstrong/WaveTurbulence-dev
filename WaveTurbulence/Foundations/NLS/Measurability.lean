/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.AkFlowLink
public import WaveTurbulence.Foundations.NLS.Backward
public import WaveTurbulence.Foundations.NLS.Symmetry

/-!
# Measurability of the solvable event (packet NLS goal 6)

For `α = L^{-γ}` and `T > 0`, write `T = δ T_kin 𝔇` (here `δ = 1`). The set of data with a smooth
solution of (NLS) on `[0, T]` is (`smoothDataSet_eq`)

  `{c rapidly decreasing} ∩ ⋃_{R ∈ ℕ} {c | the truncated flow of radius R of (1+‖n‖)^{d+1} c
    stays in the ball of radius R on [0, 𝔇]}`,

by the reduction to the `a`-system in both directions and the continuation criterion
`exists_isAkSolution_iff`. Each set in the union is the preimage of a closed subset of `ℓ¹` under
the weighting map, which is measurable on the rapidly decreasing data (`ℓ¹`-limit of the
continuous finite truncations). Hence:

* `measurableSet_solvableEvent`: `MeasurableSet (solvableEvent L α T φin g)` for measurable `g`;
* `measurable_indicator_norm_torusFourierCoeff_sq`: for any selection `U` of solutions on the
  solvable event, `ω ↦ 1_E(ω) ‖û(U ω t, n)‖²` is measurable (it is the limit of the measurable
  functions built from the truncated flows of radius `R → ∞`);
* `norm_torusFourierCoeff_sq_le_tsum`: the bound `|û(t, n)|² ≤ ∑ₘ φin(m/L) |gₘ|²`
  (TARGET L818–L820).
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology Metric
open scoped ENNReal

namespace WaveTurbulence.NLS

variable {d : ℕ}

/-! ### Rapid decay and the weighting map -/

theorem measurableSet_isRapidDecay : MeasurableSet {c : (Fin d → ℤ) → ℂ | IsRapidDecay c} := by
  have h : {c : (Fin d → ℤ) → ℂ | IsRapidDecay c} =
      ⋂ N : ℕ, ⋃ C : ℕ, ⋂ n : Fin d → ℤ, {c | ‖c n‖ ≤ (C : ℝ) * (1 + ‖n‖) ^ (-(N : ℤ))} := by
    ext c
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · intro hc N
      obtain ⟨C, hC⟩ := hc N
      exact ⟨⌈C⌉₊, fun n => (hC n).trans (by gcongr; exact Nat.le_ceil C)⟩
    · intro hc N
      obtain ⟨C, hC⟩ := hc N
      exact ⟨C, hC⟩
  rw [h]
  exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun C => MeasurableSet.iInter fun n =>
    measurableSet_le (measurable_pi_apply n).norm measurable_const

theorem continuous_sum_single_weightUp (F : Finset (Fin d → ℤ)) :
    Continuous fun c : (Fin d → ℤ) → ℂ =>
      ∑ n ∈ F, lp.single (E := fun _ : Fin d → ℤ => ℂ) 1 n (weightUp c n) :=
  continuous_finsetSum _ fun n _ =>
    (lp.isometry_single (E := fun _ : Fin d → ℤ => ℂ) (p := 1) n).continuous.comp
      (continuous_const.mul (continuous_apply n))

/-- A continuous function of the weighted data, restricted to rapidly decreasing data, is
measurable (the weighted data are the `ℓ¹`-limit of their finite truncations). -/
theorem measurable_indicator_comp_ofFun {ψ : L1 d → ℝ} (hψ : Continuous ψ) :
    Measurable ({c : (Fin d → ℤ) → ℂ | IsRapidDecay c}.indicator
      fun c => ψ (L1.ofFun (weightUp c))) := by
  set S := {c : (Fin d → ℤ) → ℂ | IsRapidDecay c}
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset (Fin d → ℤ)))
    (f := fun F => S.indicator fun c =>
      ψ (∑ n ∈ F, lp.single (E := fun _ : Fin d → ℤ => ℂ) 1 n (weightUp c n)))
    (fun F => ((hψ.comp (continuous_sum_single_weightUp F)).measurable).indicator
      measurableSet_isRapidDecay) (tendsto_pi_nhds.2 fun c => ?_)
  by_cases hc : c ∈ S
  · simp only [indicator_of_mem hc]
    have h := lp.hasSum_single ENNReal.one_ne_top (L1.ofFun (weightUp c) : L1 d)
    simp only [L1.ofFun_apply (IsRapidDecay.summable_norm_weightUp hc)] at h
    exact (hψ.tendsto _).comp h
  · simp only [indicator_of_notMem hc]
    exact tendsto_const_nhds

/-- The rapidly decreasing data whose weighted version lies in a closed subset of `ℓ¹` form a
measurable set. -/
theorem measurableSet_isRapidDecay_inter {G : Set (L1 d)} (hG : IsClosed G) :
    MeasurableSet {c : (Fin d → ℤ) → ℂ | IsRapidDecay c ∧ L1.ofFun (weightUp c) ∈ G} := by
  rcases G.eq_empty_or_nonempty with rfl | hne
  · simp
  set S := {c : (Fin d → ℤ) → ℂ | IsRapidDecay c}
  have h : {c : (Fin d → ℤ) → ℂ | IsRapidDecay c ∧ L1.ofFun (weightUp c) ∈ G} =
      S ∩ (S.indicator fun c => infDist (L1.ofFun (weightUp c)) G) ⁻¹' {0} := by
    ext c
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hc, hcG⟩
      refine ⟨hc, ?_⟩
      rw [indicator_of_mem (show c ∈ S from hc)]
      exact infDist_zero_of_mem hcG
    · rintro ⟨hc, h0⟩
      rw [indicator_of_mem (show c ∈ S from hc)] at h0
      exact ⟨hc, (hG.mem_iff_infDist_zero hne).2 h0⟩
  rw [h]
  exact measurableSet_isRapidDecay.inter
    (measurable_indicator_comp_ofFun (continuous_infDist_pt G) (measurableSet_singleton 0))

/-! ### The set of smooth data -/

/-- The data whose truncated flow of radius `R` stays in the ball of radius `R` on `[0, 𝔇]`. -/
@[expose] def truncBallSet (L γ δ R 𝔇 : ℝ) : Set (L1 d) :=
  ⋂ t ∈ Icc 0 𝔇, {x | ‖truncFlow L γ δ R 𝔇 x t‖ ≤ R}

theorem isClosed_truncBallSet {L γ δ R 𝔇 : ℝ} (hR : 0 ≤ R) :
    IsClosed (truncBallSet (d := d) L γ δ R 𝔇) :=
  isClosed_biInter fun _ ht =>
    isClosed_le (continuous_norm.comp (continuous_truncFlow_data hR ht)) continuous_const

theorem _root_.WaveTurbulence.IsSmoothNLSSolution.isRapidDecay {L α T : ℝ}
    {c : (Fin d → ℤ) → ℂ} {u : ℝ → (Fin d → ℝ) → ℂ} (hL : 0 < L) (hT : 0 ≤ T)
    (hu : IsSmoothNLSSolution L α T c u) : IsRapidDecay c := fun N => by
  obtain ⟨C, hC⟩ := hu.exists_uniform_decay hL N
  exact ⟨C, fun n => by rw [← hu.2.2.1 n]; exact hC 0 ⟨le_rfl, hT⟩ n⟩

variable {L γ δ 𝔇 T : ℝ}

/-- The set of data with a smooth solution of (NLS) on `[0, T]`, `T = δ T_kin 𝔇`, described by
the truncated flows of the `a`-system. -/
theorem smoothDataSet_eq (hL : 0 < L) (hδ : 0 < δ) (h𝔇 : 0 < 𝔇)
    (hT : T = δ * kineticTime (L ^ (-γ)) * 𝔇) :
    smoothDataSet (d := d) L (L ^ (-γ)) T =
      ⋃ R : ℕ, {c | IsRapidDecay c ∧ L1.ofFun (weightUp c) ∈ truncBallSet L γ δ R 𝔇} := by
  have hT0 : 0 ≤ T := by rw [hT, kineticTime_rpow_neg hL]; positivity
  ext c
  simp only [smoothDataSet, mem_ofPred_eq, mem_iUnion, truncBallSet, mem_iInter]
  constructor
  · rintro ⟨u, hu⟩
    have hc := hu.isRapidDecay hL hT0
    obtain ⟨R, hR⟩ := (exists_isAkSolution_iff hL hc).1 ⟨_, hu.isAkSolution hL hδ.le hT⟩
    exact ⟨R, hc, hR⟩
  · rintro ⟨R, hc, hR⟩
    obtain ⟨a, ha⟩ := (exists_isAkSolution_iff (γ := γ) (δ := δ) (𝔇 := 𝔇) hL hc).2 ⟨R, hR⟩
    exact ⟨_, (ha.isSmoothNLSSolution hL hδ h𝔇 hT hc).1⟩

theorem measurableSet_smoothDataSet (hL : 0 < L) (hδ : 0 < δ) (h𝔇 : 0 < 𝔇)
    (hT : T = δ * kineticTime (L ^ (-γ)) * 𝔇) :
    MeasurableSet (smoothDataSet (d := d) L (L ^ (-γ)) T) := by
  rw [smoothDataSet_eq hL hδ h𝔇 hT]
  exact MeasurableSet.iUnion fun R =>
    measurableSet_isRapidDecay_inter (isClosed_truncBallSet (Nat.cast_nonneg R))

/-! ### The solvable event -/

theorem measurable_initialCoeff {Ω : Type*} [MeasurableSpace Ω] (L : ℝ) (φin : Mom d → ℝ)
    {g : (Fin d → ℤ) → Ω → ℂ} (hg : ∀ n, Measurable (g n)) :
    Measurable fun ω => initialCoeff L φin g ω :=
  measurable_pi_iff.2 fun n => (hg n).const_mul _

theorem kineticTime_rpow_neg_pos (hL : 0 < L) (γ : ℝ) : 0 < kineticTime (L ^ (-γ)) := by
  rw [kineticTime_rpow_neg hL]; positivity

/-- **Measurability of the solvable event** (packet NLS goal 6; the frozen conjunct
`MeasurableSet (solvableEvent …)` of Theorem 1.1). -/
theorem measurableSet_solvableEvent {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} (hL : 0 < L)
    (hT : 0 < T) (hα : α = L ^ (-γ)) (φin : Mom d → ℝ) {g : (Fin d → ℤ) → Ω → ℂ}
    (hg : ∀ n, Measurable (g n)) : MeasurableSet (solvableEvent L α T φin g) := by
  subst hα
  have hk := kineticTime_rpow_neg_pos hL γ
  rw [solvableEvent_eq_preimage]
  exact measurable_initialCoeff L φin hg
    (measurableSet_smoothDataSet hL one_pos (div_pos hT hk) (by field_simp))

/-- **Measurability of the integrand** of Theorem 1.1 (packet NLS goal 6): for any selection `U`
of smooth solutions on the solvable event `E`, `ω ↦ 1_E(ω) ‖û(U ω t, n)‖²` is measurable. -/
theorem measurable_indicator_norm_torusFourierCoeff_sq {Ω : Type*} [MeasurableSpace Ω] {α : ℝ}
    (hL : 0 < L) (hT : 0 < T) (hα : α = L ^ (-γ)) (φin : Mom d → ℝ)
    {g : (Fin d → ℤ) → Ω → ℂ} (hg : ∀ n, Measurable (g n)) (U : Ω → ℝ → (Fin d → ℝ) → ℂ)
    (hU : ∀ ω ∈ solvableEvent L α T φin g,
      IsSmoothNLSSolution L α T (initialCoeff L φin g ω) (U ω))
    {t : ℝ} (ht : t ∈ Icc 0 T) (n : Fin d → ℤ) :
    Measurable ((solvableEvent L α T φin g).indicator
      fun ω => ‖torusFourierCoeff L (U ω t) n‖ ^ 2) := by
  subst hα
  set k := kineticTime (L ^ (-γ))
  have hk : 0 < k := kineticTime_rpow_neg_pos hL γ
  set 𝔇 := T / k
  have h𝔇 : 0 < 𝔇 := div_pos hT hk
  have hT' : T = 1 * k * 𝔇 := by simp only [𝔇]; field_simp
  set s := t / k
  have hs : s ∈ Icc 0 𝔇 := ⟨div_nonneg ht.1 hk.le, div_le_div_of_nonneg_right ht.2 hk.le⟩
  have hts : 1 * k * s = t := by simp only [s]; field_simp
  set E := solvableEvent L (L ^ (-γ)) T φin g
  set P : ℕ → Set ((Fin d → ℤ) → ℂ) := fun R =>
    {c | IsRapidDecay c ∧ L1.ofFun (weightUp c) ∈ truncBallSet L γ 1 R 𝔇}
  have hPE : ∀ R, ∀ ω, initialCoeff L φin g ω ∈ P R → ω ∈ E := fun R ω hω => by
    show initialCoeff L φin g ω ∈ smoothDataSet (d := d) L (L ^ (-γ)) T
    rw [smoothDataSet_eq hL one_pos h𝔇 hT']
    exact mem_iUnion.2 ⟨R, hω⟩
  set ψ : ℕ → L1 d → ℝ := fun R x =>
    ‖lp.evalCLM ℝ (fun _ : Fin d → ℤ => ℂ) 1 n (truncFlow L γ 1 R 𝔇 x s) /
      (flowWeight n : ℂ)‖ ^ 2
  have hψ : ∀ R, Continuous (ψ R) := fun R =>
    ((((lp.evalCLM ℝ (fun _ : Fin d → ℤ => ℂ) 1 n).continuous.comp
      (continuous_truncFlow_data (Nat.cast_nonneg R) hs)).div_const _).norm).pow 2
  refine measurable_of_tendsto_metrizable (f := fun R ω =>
      (P R).indicator ({c | IsRapidDecay c}.indicator fun c => ψ R (L1.ofFun (weightUp c)))
        (initialCoeff L φin g ω))
    (fun R => ((measurable_indicator_comp_ofFun (hψ R)).indicator
      (measurableSet_isRapidDecay_inter (isClosed_truncBallSet (Nat.cast_nonneg R)))).comp
        (measurable_initialCoeff L φin hg)) (tendsto_pi_nhds.2 fun ω => ?_)
  by_cases hω : ω ∈ E
  · have hu := hU ω hω
    set c := initialCoeff L φin g ω
    have hc : IsRapidDecay c := hu.isRapidDecay hL hT.le
    have ha := hu.isAkSolution hL zero_le_one hT'
    obtain ⟨Y, hY⟩ := ha.exists_norm_ofFun_le hL hc
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈Y⌉₊) fun R hR => ?_
    have hRY : ∀ r ∈ Icc 0 𝔇,
        ‖(L1.ofFun (weightUp (reducedCoeff L γ 1 (U ω) r)) : L1 d)‖ ≤ (R : ℝ) :=
      fun r hr => (hY r hr).trans ((Nat.le_ceil Y).trans (Nat.cast_le.2 hR))
    have hflow := ha.truncFlow_eq hL hc hRY
    have hcP : c ∈ P R := ⟨hc, by
      simp only [truncBallSet, mem_iInter, mem_ofPred_eq]
      intro r hr
      rw [hflow r hr]
      exact hRY r hr⟩
    rw [indicator_of_mem hcP, indicator_of_mem (show c ∈ {c | IsRapidDecay c} from hc),
      indicator_of_mem hω]
    simp only [ψ]
    rw [hflow s hs]
    change ‖(L1.ofFun (weightUp (reducedCoeff L γ 1 (U ω) s)) : L1 d) n / (flowWeight n : ℂ)‖ ^ 2
      = _
    rw [L1.ofFun_apply (ha.summable_norm_weightUp hL hc hs), weightUp,
      mul_div_cancel_left₀ _ (ofReal_ne_zero.2 (flowWeight_pos n).ne'), norm_reducedCoeff, hts]
  · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun R _ => ?_
    rw [indicator_of_notMem hω, indicator_of_notMem fun h => hω (hPE R ω h)]

/-- The integrability bound used at TARGET L818–L820: on the solvable event,
`|û(t, n)|² ≤ ∑ₘ φin(m/L) |gₘ|²`. -/
theorem norm_torusFourierCoeff_sq_le_tsum {Ω : Type*} {α : ℝ} (hL : 0 < L) {φin : Mom d → ℝ}
    (hφ : ∀ k, 0 ≤ φin k) {g : (Fin d → ℤ) → Ω → ℂ} {ω : Ω} {u : ℝ → (Fin d → ℝ) → ℂ}
    (hu : IsSmoothNLSSolution L α T (initialCoeff L φin g ω) u) {t : ℝ} (ht : t ∈ Icc 0 T)
    (n : Fin d → ℤ) :
    ‖torusFourierCoeff L (u t) n‖ ^ 2 ≤ ∑' m, φin (latticePoint L m) * ‖g m ω‖ ^ 2 := by
  refine (hu.norm_torusFourierCoeff_sq_le hL ht n).trans (le_of_eq (tsum_congr fun m => ?_))
  rw [initialCoeff, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hφ _)]

end WaveTurbulence.NLS
