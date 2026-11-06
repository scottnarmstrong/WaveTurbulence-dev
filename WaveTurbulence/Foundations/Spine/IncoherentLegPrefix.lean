/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentConstantMonotonicity
public import WaveTurbulence.Foundations.Spine.IncoherentSmallParameters
public import WaveTurbulence.Foundations.Spine.IncoherentSpatialAbsorption
public import WaveTurbulence.Foundations.Spine.IncoherentOrderZero
public import WaveTurbulence.Foundations.Spine.StageInputBounds
public import WaveTurbulence.Foundations.Spine.CoherentStageThresholds
/-! Exact source-prefix assembly of the incoherent regular-couple spatial contribution. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Filter

abbrev IncoherentEvenComparisonAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ t ∈ Icc (p : ℝ) (p + 1),
    SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1))
      (incoherentCoupleSum P (inputsF P R) (p + 1) (2 * n) t) ≤
      ENNReal.ofReal (P.δ ^ ((n : ℝ) / 2) *
        P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))

theorem incoherent_even_comparison_prefix (hLeaf : LeafwiseIncoherentDecayGate) :
    WTPrefix IncoherentEvenComparisonAt := by
  have hsource := prefix_with_coherent_small_parameters
    (prefix_and (show WTPrefix LeafwiseIncoherentDecayAt from hLeaf) lowProfile_prefix
      leafwiseIncoherentDecay_largeConstantMonotone lowProfile_largeConstantMonotone)
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hsource⟩ := hsource d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  obtain ⟨C₁, hC₁, ν₀, hν₀, hsource⟩ := hsource η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨δ₀, hδ₀, hsource⟩ := hsource ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, Lsource, hLsource, hsource⟩ := hsource δ hδ D hD htime
  let P₀ : WTParams := ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, Lsource⟩
  have hs₀ : CoherentSmallParameters P₀ := (hsource Lsource le_rfl).2
  have ha : 0 < P₀.gamma1 - Real.sqrt P₀.η :=
    lt_of_le_of_lt (by positivity : 0 ≤ 2 * P₀.η ^ 20) hs₀.exponent_reserve
  obtain ⟨Cφ, hCφ, hφ⟩ := exists_uniform_SNormR hsol.1 (P₀.Lambda 0) (P₀.Lambda 0)
  let U : NNReal := ⟨Cφ + 1, by linarith⟩
  let B : NNReal := ⟨C₁, by linarith⟩
  let m : Fin D → ℕ := fun p => P₀.Lambda (p.1 + 1)
  let K : Fin D → NNReal := fun p => ⟨max 1
    (((2 : ℝ) ^ (40 * d) * (d : ℝ) ^ (40 * d)) ^ (4 * m p) *
      ((d : ℝ) ^ (40 * d + 4 * m p) * U)), by positivity⟩
  choose Dc hDc hchoice using fun p : Fin D => exists_coherent_choice_bound d (m p) (4 * m p)
  let H : Fin D → ℝ := fun p => Dc p * (K p : ℝ) ^ (4 * m p + 4 * m p) * (2 : ℝ) ^ (9 * p.1)
  have hH : ∀ p, 0 ≤ H p := by
    intro p
    have hp := hDc p
    dsimp only [H]
    positivity
  have hthreshold := eventually_coherent_stage_thresholds P₀ hs₀.eta_pos
    (C := C₂) hs₀.exponent_reserve H hH
  have hratio := eventually_uniform_incoherent_ratio D ha
  obtain ⟨Lfinal, hfinal⟩ := Filter.eventually_atTop.mp (hthreshold.and hratio)
  refine ⟨C₂, hC₂, max Lsource Lfinal, hLsource.trans (le_max_left _ _), ?_⟩
  intro L hL
  have hLs : Lsource ≤ L := (le_max_left _ _).trans hL
  have ht := hfinal L ((le_max_right _ _).trans hL)
  let P : WTParams := ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩
  have hs : CoherentSmallParameters P := (hsource L hLs).2
  change IncoherentEvenComparisonAt P
  intro p hp R hR n hn t htbox
  by_cases hn0 : n = 0
  · subst n
    have hz : incoherentCoupleSum P (inputsF P R) (p + 1) (2 * 0) t = fun _ => 0 :=
      funext (fun k => incoherentCoupleSum_eq_zero_order_zero P _ _ _ k)
    rw [hz, SNorm_zero_function]
    exact bot_le
  let i : Fin D := ⟨p, hp⟩
  have hstage := ht.1.2.2 i
  have hL1 : 1 ≤ P.L := by change 1 ≤ L; linarith [ht.1.1]
  have hd1 : 1 ≤ P.d := by change 1 ≤ d; omega
  have hinputs := all_stage_input_bounds P hd1 hL1 hs.delta_pos.le htime
    (hsource L hLs).1.2 hC₁ (zero_le_one.trans hCφ) hφ hp R hR
  have hmpos : 0 < m i := by
    have hh := forty_dim_le_Lambda P hd1 (show p + 1 ≤ P.D by omega)
    change 0 < P.Lambda (p + 1)
    omega
  apply SNorm_incoherentCoupleSum_absorbed P (hsource L hLs).1.1 hd1 hL1 hs.eta_pos.le hC₁
    hs.delta_pos.le hp hn (4 * m i) (m i) (by omega) (inputsF P R) B (K i) U hC₁
    (le_max_left _ _) (fun r hr => (hinputs r hr).1) (fun r hr => (hinputs r hr).2.2)
    (fun r hr => (hinputs r hr).2.1) (le_max_right _ _) t htbox (Dc i)
    (zero_le_one.trans (hDc i)) (hchoice i n) (ht.2 p hp.le) (by omega)
    (incoherent_smallness_of_coherent P hC₁ hs)
    ((3 * P.theta (p + 1) + 2 * P.theta p) / 5) ?_
  change H i * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ _
  exact (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith : 0 ≤ P.L) (-P.theta p))) (hH i)).trans
    hstage.2.2.1

end WaveTurbulence.LGSpine
