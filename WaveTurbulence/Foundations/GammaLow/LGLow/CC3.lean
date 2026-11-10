/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.LGLow.CC2
public import WaveTurbulence.Foundations.GammaLow.Flower.NamedInputs

/-! # LG-low (packet L07): the flower couple clause for `0 < γ ≤ 1/2`

Main's `FlowerTop.eventually_p7_context`, `P7LateHyp`, `p7_clause_late` and `couple_clause_prefix`
(`FlowerTop/P7{Context,Late,Prefix}.lean`), copied by source: `NonregularHyp` is replaced by `NonregularNumHyp`
and the gates enter through `TypeGateAt` at each large `L` (`typeGateAt_of_gamma`); the prefix uses the low gates
(L5a, L5c, L6), L5c's finalsbest2 over `𝒱_γ` (`fineSplicedGammaInput_of_subObjects`), and main's proved spine providers for ladderl1old and the
two leafwise inputs. `coupleClauseLow` has exactly the type of L8's named input
`GammaLow.Flower.CoupleClauseLowInput`. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.LGLow.CC
open WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.GammaLow.LGLow

section
-- source: FlowerTop/P7Context.lean
open WaveTurbulence.FlowerTop
open LGSpine Filter Set

theorem eventually_p7_context (C₀ : ℕ → ℝ → ℕ) (hC₀ : ∀ d γ, 2 ≤ C₀ d γ) (P : WTParams)
    (hQ : ∀ L : ℝ, P.L ≤ L → NonregularNumHyp C₀ {P with L := L})
    (hTG : ∀ L : ℝ, P.L ≤ L → 1 ≤ Real.log L → TypeGateAt {P with L := L})
    (Cφ : ℝ) (hCφ : 0 ≤ Cφ)
    (hφ : ∀ τ ∈ Set.Icc (0 : ℝ) P.τstar,
      SNormR (P.Lambda 0) (P.Lambda 0) (P.φ τ) ≤ ENNReal.ofReal Cφ) :
    ∀ᶠ L : ℝ in atTop, ∃ G : LGContext (C₀ P.d P.γ) {P with L := L},
      G.Cφ = Cφ ∧ ∀ p, p < P.D →
        GardenNum {P with L := L} Cφ p ∧ CoupleNum {P with L := L} Cφ p := by
  have h0 : NonregularNumHyp C₀ P := hQ P.L le_rfl
  obtain ⟨⟨_, _⟩, hps0, hη8, hd3, _⟩ := h0
  have hd1 : 1 ≤ P.d := by omega
  have hη := hps0.eta_pos
  set X : ℕ := 4 * (40 * P.d) ^ (2 * P.D + 2) with hX
  -- the eventual thresholds
  have E1 : ∀ᶠ L : ℝ in atTop, ∀ p ∈ Finset.range P.D,
      gardenC P Cφ p * (1 + Real.log L) ^ (24 * logExp P * P.Lambda (p + 1)) ≤ L ^ ((1 : ℝ) / 140) := by
    refine (Filter.eventually_all_finset (Finset.range P.D)).2 ?_
    intro p _
    have hg0 : 0 ≤ gardenC P Cφ p := by
      unfold gardenC
      have hC1 := hps0.c1_ge
      have : 0 ≤ max (Cφ + 1) P.C₁ := le_trans (by linarith) (le_max_right _ _)
      have : 0 < P.C₁ := by linarith
      positivity
    have := CountLemmas.eventually_monomial_log_le (a := 0) (b := (1 : ℝ) / 140) (C := gardenC P Cφ p)
      (by norm_num) hg0 (24 * logExp P * P.Lambda (p + 1))
    filter_upwards [this] with L hL
    simpa only [Real.rpow_zero, mul_one] using hL
  have E2 : ∀ᶠ L : ℝ in atTop, ∀ p ∈ Finset.range P.D,
      coupleC P Cφ p * (1 + Real.log L) ^ (16 * logExp P * P.Lambda (p + 1)) ≤
      L ^ (P.η ^ 7 - (3 * P.theta (p + 1) + 2 * P.theta p) / 5) := by
    refine (Filter.eventually_all_finset (Finset.range P.D)).2 ?_
    intro p _
    have hθ : (3 * P.theta (p + 1) + 2 * P.theta p) / 5 < P.η ^ 7 := by
      have h1 := theta_le_two P hη.le (p + 1)
      have h2 := theta_le_two P hη.le p
      have h3 := eta_gap_pos hη hη8
      linarith
    have hg0 : 0 ≤ coupleC P Cφ p := by
      unfold coupleC
      have hC1 := hps0.c1_ge
      have : 0 ≤ max (Cφ + 1) P.C₁ := le_trans (by linarith) (le_max_right _ _)
      have : 0 < P.C₁ := by linarith
      positivity
    have := CountLemmas.eventually_monomial_log_le (a := 0)
      (b := P.η ^ 7 - (3 * P.theta (p + 1) + 2 * P.theta p) / 5)
      (C := coupleC P Cφ p) (by linarith) hg0 (16 * logExp P * P.Lambda (p + 1))
    filter_upwards [this] with L hL
    simpa only [Real.rpow_zero, mul_one] using hL
  have E3 : ∀ᶠ L : ℝ in atTop, 1 ≤ Real.log L := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have E4 : ∀ᶠ L : ℝ in atTop, P.L ≤ L := eventually_ge_atTop _
  filter_upwards [E1, E2, E3, E4] with L hE1 hE2 hlog hLP
  have hQL := hQ L hLP
  obtain ⟨⟨hlowP, hctxL⟩, hs, hη8L, hd3L, habs⟩ := hQL
  obtain ⟨_, htimeL, _, _⟩ := hctxL
  have hL1 : 1 ≤ L := by have := hs.L_ge; change 2 ≤ L at this; linarith
  have hδ0 := hs.delta_pos
  have hδ1 := hs.delta_le
  have hC₀2 : (2 : ℝ) ≤ ((6 * C₀ P.d P.γ : ℕ) : ℝ) := by
    have := hC₀ P.d P.γ
    exact_mod_cast (by omega : 2 ≤ 6 * C₀ P.d P.γ)
  have hδsmall : 2 * P.C₁ * P.δ ^ (6 * P.ν) ≤ 1 := by
    have h1 := habs.1
    have hν0 := hs.nu_pos
    have hC1 := hs.c1_ge
    have e : P.δ ^ (6 * P.ν) = P.δ ^ (2 * P.ν) * P.δ ^ (4 * P.ν) := by
      rw [← Real.rpow_add hδ0]; ring_nf
    have hle : P.δ ^ (4 * P.ν) ≤ 1 := Real.rpow_le_one hδ0.le hδ1 (by positivity)
    have hp0 : 0 ≤ P.δ ^ (2 * P.ν) := Real.rpow_nonneg hδ0.le _
    have hp1 : 0 ≤ P.δ ^ (4 * P.ν) := Real.rpow_nonneg hδ0.le _
    calc 2 * P.C₁ * P.δ ^ (6 * P.ν) = (2 * P.C₁ * P.δ ^ (2 * P.ν)) * P.δ ^ (4 * P.ν) := by rw [e]; ring
      _ ≤ (2 * P.C₁ * P.δ ^ (2 * P.ν)) * 1 := mul_le_mul_of_nonneg_left hle (by positivity)
      _ ≤ (((6 * C₀ P.d P.γ : ℕ) : ℝ) * P.C₁ ^ 6 * P.δ ^ (2 * P.ν)) := by
          rw [mul_one]
          apply mul_le_mul_of_nonneg_right _ hp0
          calc 2 * P.C₁ ≤ 2 * P.C₁ ^ 6 := by
                have h1 := hs.c1_ge
                nlinarith [pow_le_pow_right₀ h1 (by norm_num : 1 ≤ 6)]
            _ ≤ ((6 * C₀ P.d P.γ : ℕ) : ℝ) * P.C₁ ^ 6 :=
              mul_le_mul_of_nonneg_right hC₀2 (by have := hs.c1_ge; positivity)
      _ ≤ 1 := h1
  have hd1 : 1 ≤ P.d := by omega
  refine ⟨⟨hs, hTG L hLP hlog, hlog, hd1,
    hlowP, htimeL, Cφ, hCφ, hφ⟩, rfl, ?_⟩
  intro p hp
  constructor
  · exact gardenNum_of_numerics {P with L := L} Cφ p hd1 hlog hs.c1_ge hCφ hδ0 hη.le hL1 hδsmall
      (hE1 p (Finset.mem_range.mpr hp))
  · exact coupleNum_of_numerics {P with L := L} Cφ p hd1 hlog hs.c1_ge hCφ hδ0 hL1 hδsmall
      (hE2 p (Finset.mem_range.mpr hp))

end

section
-- source: FlowerTop/P7Late.lean
open WaveTurbulence.FlowerTop
open FlowerP7 LGSpine Filter Set

/-- Earlier source gates and parameter bounds carried into the late-L argument. -/
abbrev P7LateHyp (C₀ : ℕ → ℝ → ℕ) (P : WTParams) : Prop :=
  NonregularNumHyp C₀ P ∧
    (LeafwiseCoherentApproximationOrder0At P ∧ LeafwiseIncoherentDecayAt P) ∧
      CoherentSmallParameters P

/-- GardenNum, CoupleNum, hE, regular-family premises and the context are derived here. -/
theorem p7_clause_late (C₀ : ℕ → ℝ → ℕ) (hC₀ : ∀ d γ, 2 ≤ C₀ d γ)
    (P : WTParams) (hγ : P.γ < 1)
    (hQ : ∀ L : ℝ, P.L ≤ L → P7LateHyp C₀ {P with L := L})
    (hTG : ∀ L : ℝ, P.L ≤ L → 1 ≤ Real.log L → TypeGateAt {P with L := L}) :
    ∀ᶠ L : ℝ in atTop, CoupleClauseAt {P with L := L} := by
  have hbase := hQ P.L le_rfl
  have hs₀ : CoherentSmallParameters P := hbase.2.2
  have hd3 : 3 ≤ P.d := hbase.1.2.2.2.1
  have hd1 : 1 ≤ P.d := by omega
  have hC₁ : 1 ≤ P.C₁ := hbase.1.2.1.c1_ge
  obtain ⟨hsol, htime, hD, _⟩ := hbase.1.1.2
  obtain ⟨Cφ, hCφ1, hφ⟩ := exists_uniform_SNormR hsol.1 (P.Lambda 0) (P.Lambda 0)
  have hCφ : 0 ≤ Cφ := zero_le_one.trans hCφ1
  let U : NNReal := ⟨Cφ + 1, by linarith⟩
  let m : Fin P.D → ℕ := fun p => P.Lambda (p.1 + 1)
  let K : Fin P.D → NNReal := fun p => ⟨max 1
    (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m p) *
      ((P.d : ℝ) ^ (40 * P.d + 4 * m p) * U)), by positivity⟩
  choose Dc hDc hchoice using fun p : Fin P.D =>
    exists_coherent_choice_bound P.d (m p) (4 * m p)
  let Hs : Fin P.D → ℝ := fun p => Dc p * (K p : ℝ) ^ (4 * m p + 4 * m p) * (2 : ℝ) ^ (9 * p.1)
  let Cr : Fin P.D → ℝ := fun p => max (Cφ + 1)
    (Dc p * P.C₁ * (K p : ℝ) ^ (4 * m p + 4 * m p) + 1)
  have ha : 0 < P.gamma1 - Real.sqrt P.η :=
    lt_of_le_of_lt (by positivity : 0 ≤ 2 * P.η ^ 20) hs₀.exponent_reserve
  have hdim : (0 : ℝ) < 50 * P.d := by
    have : (1 : ℝ) ≤ P.d := by exact_mod_cast hd1
    linarith
  have hthr := FlowerReg.eventually_regular_thresholds ha hdim P.D Hs Cr
  have hctx := eventually_p7_context C₀ hC₀ P (fun L hL => (hQ L hL).1) hTG Cφ hCφ hφ
  filter_upwards [hthr, hctx, eventually_p7_loss_all P hd1 Cr,
    eventually_ge_atTop P.L] with L ht hg he hLP
  let Q : WTParams := {P with L := L}
  obtain ⟨G, hGC, hnums⟩ := hg
  have hs : CoherentSmallParameters Q := (hQ L hLP).2.2
  have hL1 : 1 ≤ Q.L := by change 1 ≤ L; linarith [ht.1]
  have hlow : LowProfileAt Q := (hQ L hLP).1.1.1
  intro p hp R hR t htt k N hN kind dt hkdt
  let i : Fin P.D := ⟨p,hp⟩
  have hi := all_stage_input_bounds Q hd1 hL1 hs.delta_pos.le htime hlow hC₁ hCφ hφ hp R hR
  have hhigh := coherent_input_high_bound Q hd1 hL1 hp R hR hCφ
    (coherent_profile_high_bound Q hd1 hs.delta_pos.le htime hCφ hφ hp)
  have hm : 0 < Q.Lambda (p + 1) := by
    exact lt_of_lt_of_le (by change 0 < 40 * P.d; omega)
      (forty_dim_le_Lambda Q hd1 (Nat.succ_le_of_lt hp))
  let H : RegPremises Q (inputsF Q R) p := {
    hsC := fun L' hL' => (hQ L' (hLP.trans hL')).2.1.1
    hsI := (hQ L hLP).2.1.2
    hs := hs
    hd := hd1
    hL := hL1
    hC₁ := hC₁
    hp := hp
    hm := hm
    U := U
    Kc := K i
    hKc := le_max_left _ _
    hU := by change 1 ≤ Cφ + 1; linarith
    hcF := fun r hr => (hi r hr).1
    hlowF := fun r hr => (hi r hr).2.2
    hhighF := fun r hr => (hi r hr).2.1
    hhighP := hhigh
    hmod := le_max_right _ _
    D := Dc i
    hD := hDc i
    hchoice := hchoice i
    hr := ht.2.2.2 p hp.le
    hlargeI := ht.2.1 i
    C0 := Cφ + 1
    hC0 := by linarith
    h0 := abs_inputsF_le Q hd1 hL1 hs.delta_pos hp R hR htime hCφ hφ }
  have hnums' := hnums p hp
  rw [← hGC] at hnums'
  exact coupleSum_total_bound (C₀ P.d P.γ) Q G hp R hR
    (p7_one_le_R Q hd1 G.hlog p) hN htt k kind dt hkdt
    (gamma_le_dim Q hd1 hγ) hnums'.1 hnums'.2 H (he i)

end

section
-- source: FlowerTop/P7Prefix.lean
open WaveTurbulence.FlowerTop
open LGSpine Set Filter

/-- The entire couple clause, with hE/GardenNum/CoupleNum and regular premises discharged. -/
theorem couple_clause_prefix_low (hgate : Fama.Stage1ReductionGateLow) (hcoarse : Famc.CoarseSplicedGateLow)
    (hcount : FinalCount.FinalCountGateLow) (hfine : FineSplicedGammaInput) :
    WTPrefix (fun P => P.γ ≤ 1 / 2 → CoupleClauseAt P) := by
  obtain ⟨C₀, hC₀, hst⟩ := hgate
  have hm1 := Fama.stage1ReductionLow_largeConstantMonotone C₀
  have hm2 := Famc.coarseSplicedLow_largeConstantMonotone
  have hm3 := ladderFourierAt_largeConstantMonotone
  have hm4 := FinalCount.finalCountLow_largeConstantMonotone
  have hm5 := lowProfile_largeConstantMonotone
  have hQ45 := prefix_and hcount lowProfile_prefix hm4 hm5
  have hQ345 := prefix_and Spine.ladder_fourier hQ45 hm3 (hm4.and hm5)
  have hQ2345 := prefix_and (show WTPrefix fun P => P.γ ≤ 1 / 2 → Famc.CoarseSplicedGammaAt P from hcoarse) hQ345 hm2 (hm3.and (hm4.and hm5))
  have hQ0 := prefix_and hst hQ2345 hm1 (hm2.and (hm3.and (hm4.and hm5)))
  have hm0 := hm1.and (hm2.and (hm3.and (hm4.and hm5)))
  have hleaf := prefix_and
    (prefix_map (fun _ h => LeafwiseCoherentApproximationAt.toOrder0 h) Spine.leafwise_coherent_approximation)
    Spine.leafwise_incoherent_decay leafwiseCoherentApproximation_largeConstantMonotone
    leafwiseIncoherentDecay_largeConstantMonotone
  have hmleaf := leafwiseCoherentApproximation_largeConstantMonotone.and
    leafwiseIncoherentDecay_largeConstantMonotone
  have hQ1 := prefix_with_wke_context (prefix_and hQ0 hleaf hm0 hmleaf)
  have hQ2 := prefix_with_stage1_small_fn hQ1
    ((hm0.and hmleaf).and wkeContext_largeConstantMonotone)
    (fun d γ => 6 * C₀ d γ) (fun d γ => by have := hC₀ d γ; omega)
  have hQ3 := prefix_with_gamma_upper (prefix_with_coherent_small_parameters hQ2)
  refine prefix_late hQ3 (fun P hP => ?_)
  by_cases hhalf : P.γ ≤ 1 / 2
  · have hlate := p7_clause_late C₀ hC₀ P (hP P.L le_rfl).2 (by
      intro L hL
      obtain ⟨⟨⟨abc, lf⟩, ctx⟩, ps, eta, hd, habs⟩ := (hP L hL).1.1
      obtain ⟨-, -, -, -, e⟩ := abc
      exact ⟨⟨⟨e, ctx⟩, ps, eta, hd, habs⟩, lf, (hP L hL).1.2⟩) (by
      intro L hL hlog
      obtain ⟨⟨⟨⟨a, b, c, d, -⟩, -⟩, -⟩, hs, -, hd3, habs⟩ := (hP L hL).1.1
      exact typeGateAt_of_gamma (C₀ P.d P.γ) _ hs (b hhalf)
        (hfine {P with L := L} hhalf c (d hhalf) (coverSmall_of_pieceSmall hs)) habs hlog (by omega)
        (a hhalf))
    exact hlate.mono (fun _ h _ => h)
  · exact Filter.Eventually.of_forall fun _ h => absurd h hhalf

end

/-- **The flower couple clause for `0 < γ ≤ 1/2`** (TARGET `flowerest1` (2), L2290–L2305, proof L2306–L2338): L8's
named input `CoupleClauseLowInput`, from the three low gates (L5a, L5c, L6) and L5c's finalsbest2 over `𝒱_γ` (with L3's
named input `Famc.SubObjectsInput`), exactly as `layergarden_low`. Conditional helper (distinct name). -/
theorem coupleClauseLow (h5a : Fama.Stage1ReductionGateLow) (h5c : Famc.CoarseSplicedGateLow)
    (h6 : FinalCount.FinalCountGateLow) (hSO : Famc.SubObjectsInput) :
    WaveTurbulence.GammaLow.Flower.CoupleClauseLowInput :=
  couple_clause_prefix_low h5a h5c h6 (fineSplicedGammaInput_of_subObjects hSO)

/-- `coupleClauseLow` with L5c's proved finalsbest1 over `𝒱_γ` (`Famc.coarseSplicedGateLow`) discharged. -/
theorem coupleClauseLow_of_three (h5a : Fama.Stage1ReductionGateLow) (h6 : FinalCount.FinalCountGateLow)
    (hSO : Famc.SubObjectsInput) : WaveTurbulence.GammaLow.Flower.CoupleClauseLowInput :=
  coupleClauseLow h5a Famc.coarseSplicedGateLow h6 hSO

end WaveTurbulence.GammaLow.LGLow.CC
