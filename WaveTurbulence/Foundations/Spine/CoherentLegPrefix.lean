/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentAllOrdersSpatialComparison
public import WaveTurbulence.Foundations.Spine.CoherentSourcePrefix
public import WaveTurbulence.Foundations.Spine.CoherentSmallParameters
public import WaveTurbulence.Foundations.Spine.CoherentStageThresholds
public import WaveTurbulence.Foundations.Spine.CoherentProfileInputBounds
/-! Parameter-prefix assembly of the coherent even-order leg of TARGET L2253–2255. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Filter

abbrev CoherentEvenComparisonAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ t ∈ Icc (p : ℝ) (p + 1),
    SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1))
      (fun k => coherentCoupleSum P (inputsF P R) (p + 1) (2 * n) t k -
        (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)) ≤
      ENNReal.ofReal (P.δ ^ ((n : ℝ) / 2) *
        P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))

theorem coherent_even_comparison_prefix
    (hLeaf : LeafwiseCoherentApproximationGate) (hTaylor : CoherentTaylorGate) :
    WTPrefix CoherentEvenComparisonAt := by
  have hsource := prefix_with_coherent_small_parameters (coherent_source_prefix hLeaf hTaylor)
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
  obtain ⟨Cφ, hCφ, hφ⟩ := exists_uniform_SNormR hsol.1 (P₀.Lambda 0) (P₀.Lambda 0)
  let U : NNReal := ⟨Cφ + 1, by linarith⟩
  let m : Fin D → ℕ := fun p => P₀.Lambda (p.1 + 1)
  let K : Fin D → NNReal := fun p => ⟨max 1
    (((2 : ℝ) ^ (40 * d) * (d : ℝ) ^ (40 * d)) ^ (4 * m p) *
      ((d : ℝ) ^ (40 * d + 4 * m p) * U)), by positivity⟩
  choose Dc hDc hchoice using fun p : Fin D => exists_coherent_choice_bound d (m p) (4 * m p)
  let H : Fin D → ℝ := fun p => max
    (Dc p * C₁ * (K p : ℝ) ^ (4 * m p + 4 * m p))
    (2 * Dc p * C₁ ^ 3 * (K p : ℝ) ^ (4 * m p + 4 * m p))
  have hH : ∀ p, 0 ≤ H p := by
    intro p
    have hp := hDc p
    dsimp only [H]
    positivity
  have hthreshold := eventually_coherent_stage_thresholds P₀ hs₀.eta_pos
    (C := C₂) hs₀.exponent_reserve H hH
  obtain ⟨Lfinal, hfinal⟩ := Filter.eventually_atTop.mp hthreshold
  refine ⟨C₂, hC₂, max Lsource Lfinal, hLsource.trans (le_max_left _ _), ?_⟩
  intro L hL
  have hLs : Lsource ≤ L := (le_max_left _ _).trans hL
  have ht := hfinal L ((le_max_right _ _).trans hL)
  let P : WTParams := ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩
  have hs : CoherentSmallParameters P := (hsource L hLs).2
  change CoherentEvenComparisonAt P
  intro p hp R hR n hn t htbox
  let i : Fin D := ⟨p, hp⟩
  have hstage := ht.2.2 i
  have hL1 : 1 ≤ P.L := by change 1 ≤ L; linarith [ht.1]
  have hd1 : 1 ≤ P.d := by change 1 ≤ d; omega
  have hphi := coherent_profile_high_bound P hd1 hs.delta_pos.le htime
    (zero_le_one.trans hCφ) hφ hp
  have hFhigh := coherent_input_high_bound P hd1 hL1 hp R hR (zero_le_one.trans hCφ) hphi
  have hRhigh := coherent_remainder_high_bound P hd1 hL1 hp R hR
  have hFlow := coherent_input_low_bound P hd1 hL1 hs.delta_pos.le htime
    (hsource L hLs).1.2.2 hC₁ hp R hR
  have htimep : δ * p ∈ Icc (0 : ℝ) τ := by
    refine ⟨mul_nonneg hδ.1.le (Nat.cast_nonneg p), ?_⟩
    rw [htime]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (show (p : ℝ) ≤ D by exact_mod_cast hp.le) hδ.1.le
  have hphilow : SNormR (40 * P.d) (40 * P.d) (P.φ (P.δ * p)) ≤ ENNReal.ofReal P.C₁ :=
    ((hsource L hLs).1.2.2 _ htimep).trans (ENNReal.ofReal_le_ofReal (by dsimp [P]; linarith))
  have hε : 0 < P.L ^ (-P.theta p) := Real.rpow_pos_of_pos (by linarith : 0 < P.L) _
  have hεone : P.L ^ (-P.theta p) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (neg_nonpos.mpr (theta_nonneg P p))
  have hmpos : 0 < m i := by
    have hh := forty_dim_le_Lambda P hd1 (show p + 1 ≤ P.D by omega)
    change 0 < P.Lambda (p + 1)
    omega
  have ha : 0 < P.gamma1 - Real.sqrt P.η :=
    lt_of_le_of_lt (by positivity : 0 ≤ 2 * P.η ^ 20) hs.exponent_reserve
  apply coherent_comparison_all_orders_SNorm_le P
    (fun L' hL' => (hsource L' (hLs.trans hL')).1.1.1)
    (fun L' hL' => (hsource L' (hLs.trans hL')).1.1.2)
    ht.1 (hsource L hLs).1.2.1 (zero_le_one.trans hC₂) ht.2.1
    hs.delta_pos hC₁ hs.eta_le hd1 hs.eta_pos ha hp hn (m i) rfl (by omega)
    (inputsF P R) U (K i) (le_max_left _ _) (by change 1 ≤ Cφ + 1; linarith)
    hFlow hFhigh (le_max_right _ _) (R p) rfl (P.L ^ (-P.theta p)) hε
    (hεone.trans hC₁) hphilow
    (hphi.trans (ENNReal.ofReal_le_ofReal (by change Cφ ≤ Cφ + 1; linarith))) hRhigh
    (Dc i) (zero_le_one.trans (hDc i)) (hchoice i n)
    ((3 * P.theta (p + 1) + 2 * P.theta p) / 5)
    (by dsimp only [WTParams.theta]; positivity) hstage.2.1
    ((le_max_left _ _).trans hstage.1) hs.tail_delta hs.low_delta
    ?_ hs.taylor_delta t htbox
  exact (mul_le_mul_of_nonneg_right (le_max_right _ _)
    (by positivity : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η)) + P.L ^ (-P.theta p))).trans hstage.2.2.1

end WaveTurbulence.LGSpine
