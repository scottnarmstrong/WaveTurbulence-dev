/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.FlowerReg.Family
public import WaveTurbulence.Foundations.FlowerTop.Port.FlowerReg.Carrier
public import WaveTurbulence.Foundations.FlowerTop.Port.FlowerReg.Thresholds
public import WaveTurbulence.Foundations.Spine.IncoherentConstantMonotonicity
public import WaveTurbulence.Foundations.Spine.LeafwiseCoherentConstantMonotonicity
public import WaveTurbulence.Foundations.Spine.LowProfilePrefix
public import WaveTurbulence.Foundations.Spine.StageInputBounds
public import WaveTurbulence.Foundations.Spine.CoherentProfileInputBounds
public import WaveTurbulence.Foundations.Spine.CoherentChoiceAbsorption
public import WaveTurbulence.Foundations.Spine.SchwartzUniformNorm
public import WaveTurbulence.Foundations.Spine.PrefixConjunction
public import WaveTurbulence.Foundations.Spine.PrefixMap
/-! FLOWER-REG: `WTPrefix RegularCouplesL0At` from LG-SPINE's two leafwise regular-couple gates.

The parameter prefix is chosen exactly as in LG-SPINE's `IncoherentLegPrefix` / `CoherentLegPrefix`:
the constants `U`, `K`, `Dc` of the leaf-profile costs depend only on `d, γ, η, φ, C₁`, so they are fixed before
`ν, δ, C₂`; only the large-`L` thresholds (`eventually_regular_thresholds`) come last.
Every canonical regular couple of the carrier is bounded termwise (coherent: `coherent_sub_SNorm_absorbed`;
incoherent: `incoherent_sub_SNorm_absorbed`), so the kind restriction `L0` plays no role beyond `1 ≤ N`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerReg
open WaveTurbulence WaveTurbulence.LGSpine Set Finset Filter
open scoped ENNReal

theorem regularCouplesL0_of_leafwise (hC : LeafwiseCoherentApproximationGate)
    (hI : LeafwiseIncoherentDecayGate) : WTPrefix RegularCouplesL0At := by
  have hsource := prefix_with_coherent_small_parameters
    (prefix_and (prefix_and (prefix_map (fun _ h => LeafwiseCoherentApproximationAt.toOrder0 h) (show WTPrefix LeafwiseCoherentApproximationAt from hC))
      (show WTPrefix LeafwiseIncoherentDecayAt from hI)
      leafwiseCoherentApproximation_largeConstantMonotone
      leafwiseIncoherentDecay_largeConstantMonotone)
      lowProfile_prefix
      (leafwiseCoherentApproximation_largeConstantMonotone.and
        leafwiseIncoherentDecay_largeConstantMonotone)
      lowProfile_largeConstantMonotone)
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
  let m : Fin D → ℕ := fun p => P₀.Lambda (p.1 + 1)
  let K : Fin D → NNReal := fun p => ⟨max 1
    (((2 : ℝ) ^ (40 * d) * (d : ℝ) ^ (40 * d)) ^ (4 * m p) *
      ((d : ℝ) ^ (40 * d + 4 * m p) * U)), by positivity⟩
  choose Dc hDc hchoice using fun p : Fin D => exists_coherent_choice_bound d (m p) (4 * m p)
  let Hs : Fin D → ℝ := fun p => Dc p * (K p : ℝ) ^ (4 * m p + 4 * m p) * (2 : ℝ) ^ (9 * p.1)
  let Gs : Fin D → ℝ := fun p => Dc p * C₁ * (K p : ℝ) ^ (4 * m p + 4 * m p) + 1
  have hd0 : (0 : ℝ) < 50 * d := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hthr := eventually_regular_thresholds ha hd0 D Hs Gs
  obtain ⟨Lfinal, hfinal⟩ := Filter.eventually_atTop.mp hthr
  refine ⟨C₂, hC₂, max Lsource Lfinal, hLsource.trans (le_max_left _ _), ?_⟩
  intro L hL
  have hLs : Lsource ≤ L := (le_max_left _ _).trans hL
  have ht := hfinal L ((le_max_right _ _).trans hL)
  let P : WTParams := ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩
  have hs : CoherentSmallParameters P := (hsource L hLs).2
  have haP : 0 < P.gamma1 - Real.sqrt P.η := ha
  change RegularCouplesL0At P
  intro p hp R hR t htI k N hN
  have hL1 : 1 ≤ P.L := by change 1 ≤ L; linarith [ht.1]
  have hL0 : 0 < P.L := by linarith
  have hd1 : 1 ≤ P.d := by change 1 ≤ d; omega
  have hδ0 := hs.delta_pos
  have hRHS : 0 ≤ jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (50 * P.d : ℝ) *
      P.δ ^ (2 * P.ν * N) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (WaveTurbulence.Induct.jbr_pos k).le _) (Real.rpow_nonneg hL0.le _))
      (Real.rpow_nonneg hδ0.le _)
  rw [regularCoupleSum_L0_eq]
  by_cases hV : regFamily P p N t k = ∅
  · rw [hV, Finset.sum_empty, norm_zero]
    exact hRHS
  obtain ⟨LG, hLG⟩ := Finset.nonempty_iff_ne_empty.mpr hV
  obtain ⟨n, hn2⟩ := regFamily_even hLG
  have hN2 : N = 2 * n := by omega
  have hn1 : 1 ≤ n := by have := regFamily_order_pos hLG; omega
  subst hN2
  have hnN : n ≤ P.N (p + 1) ^ 4 := by omega
  let i : Fin D := ⟨p, hp⟩
  have htIcc : t ∈ Icc (p : ℝ) (p + 1) := ⟨htI.1.le, htI.2.le⟩
  have hinputs := all_stage_input_bounds P hd1 hL1 hs.delta_pos.le htime
    (hsource L hLs).1.2 hC₁ (zero_le_one.trans hCφ) hφ hp R hR
  have hphi := coherent_profile_high_bound P hd1 hs.delta_pos.le htime
    (zero_le_one.trans hCφ) hφ hp
  have hFhigh := coherent_input_high_bound P hd1 hL1 hp R hR (zero_le_one.trans hCφ) hphi
  have hmpos : 0 < P.Lambda (p + 1) := by
    have hh := forty_dim_le_Lambda P hd1 (show p + 1 ≤ P.D by omega)
    omega
  have key := regular_family_pointwise P
    (fun L' hL' => (hsource L' (hLs.trans hL')).1.1.1) (hsource L hLs).1.1.2 hs hd1 hL1 hC₁
    hp hnN hn1 (P.Lambda (p + 1)) hmpos (inputsF P R) U (K i) (le_max_left _ _)
    (by change 1 ≤ Cφ + 1; linarith)
    (fun r hr => (hinputs r hr).1) (fun r hr => (hinputs r hr).2.2) (fun r hr => (hinputs r hr).2.1)
    hFhigh (le_max_right _ _) (Dc i) (hDc i) (hchoice i n) (ht.2.2.2 p hp.le) (ht.2.1 i)
    t htIcc k (regFamily P p (2 * n) t k) (fun LG h => regFamily_mem h)
  refine key.trans ?_
  have hG : Dc i * P.C₁ * ((K i : ℝ)) ^ (4 * P.Lambda (p + 1) + 4 * P.Lambda (p + 1)) + 1 ≤
      P.L ^ (50 * P.d : ℝ) := ht.2.2.1 i
  have hδpow : P.δ ^ ((n : ℝ) / 2) ≤ P.δ ^ (2 * P.ν * ((2 * n : ℕ) : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_ge hδ0 hs.delta_le
    have hν := hs.nu_le
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    push_cast
    nlinarith
  have hjb : 0 ≤ jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) := Real.rpow_nonneg (WaveTurbulence.Induct.jbr_pos k).le _
  calc jbr k ^ (-(4 * (P.Lambda (p + 1) : ℝ))) *
        (Dc i * P.C₁ * ((K i : ℝ)) ^ (4 * P.Lambda (p + 1) + 4 * P.Lambda (p + 1)) + 1) *
        P.δ ^ ((n : ℝ) / 2)
      ≤ jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (50 * P.d : ℝ) *
        P.δ ^ (2 * P.ν * ((2 * n : ℕ) : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hG hjb) hδpow (Real.rpow_nonneg hδ0.le _)
          (mul_nonneg hjb (Real.rpow_nonneg hL0.le _))
    _ = _ := rfl

end WaveTurbulence.FlowerReg
