/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WAssembly
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.Class
public import WaveTurbulence.Foundations.Flower.IncTop.Gate
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD16
public import WaveTurbulenceVineParam.VineParamMain

/-! # STAGE1W-VINE (T6, part 6): the `WTPrefix` of the weighted vine case

* `v5FrontierClassBoundAt_mono`: the staged bound `V5FrontierClassBoundAt` is monotone in the large constants (main's
  `vineEstHalfMK_mono`; only the factor `(C₁ √δ)^{n₂}` depends on them).
* **`vineCaseRepresentsFW_of_frontier (hV : V5FrontierClassBound) : WTPrefix VineCaseRepresentsFW`** — the conditional
  helper with the staged input **`V5FrontierClassBound`** (V5W-B's target, V5W-0's statement); every other input is
  proved: main's two leafwise gates, INC-TOP's `topIncoherentDecayGateR`, COH-TRUNK (inside V5W-0's T5), V5W-0's T4/T5,
  O4′'s slot targets, and main's `vineparam : VINEPARAM` (M9).
* `stage1ReductionGateFW_of_frontier`: the weighted Stage-1 gate, from the same staged input with O4′'s
  `noVineRepresentsFW`.

Adapted from main's `Represents/{RepVC2, RepVD16}.lean` (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence WaveTurbulence.LGSpine Set VineParamContract WaveTurbulence.Represents
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.Eng WaveTurbulence.VineEstS4 WaveTurbulence.RegRed
open scoped ENNReal

/-- The staged bound is monotone in the large constants. -/
theorem v5FrontierClassBoundAt_mono : LargeConstantMonotone V5FrontierClassBoundAt := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  intro p hp h' B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hcl centre wBar lam g cψ
    hc hgp hre S hS hrow
  have hN := vineEstHalfMK_N P c₁ c₂ (p + 1)
  have key := @h p hp h' B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay
    (by rw [← hN]; exact hord) (by have := vineEstHalfMK_N P c₁ c₂ 1; rw [← this]; exact hcl) centre wBar lam g cψ
    hc hgp hre S hS hrow
  refine le_trans key (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_))
  have hL0 : 0 ≤ P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) :=
    Real.rpow_nonneg (by linarith) _
  have hleaf := WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg RD hG R layer hLayer hB₀
  have hs : 0 ≤ Real.sqrt P.δ := Real.sqrt_nonneg _
  have hc0 : 0 ≤ P.C₁ * Real.sqrt P.δ := mul_nonneg (by linarith) hs
  have hcc : P.C₁ * Real.sqrt P.δ ≤ c₁ * Real.sqrt P.δ := mul_le_mul_of_nonneg_right h₁ hs
  have hpow := pow_le_pow_left₀ hc0 hcc (clLocalOrder2 RD hG R)
  have h1 : 0 ≤ (1 + |lam|) ^ (6 * P.η ^ 6) := Real.rpow_nonneg (by positivity) _
  show (1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R * _ * _) ≤
    (1 + |lam|) ^ (6 * P.η ^ 6) * ((c₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R * _ * _)
  gcongr

/-- **The weighted vine case on the prefix**, from the staged `V5FrontierClassBound` (conditional helper). -/
theorem vineCaseRepresentsFW_of_frontier (hV : V5FrontierClassBound) : WTPrefix VineCaseRepresentsFW := by
  have hgates : WTPrefix (fun P => LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) :=
    prefix_and Spine.leafwise_incoherent_decay Spine.leafwise_coherent_approximation
      leafwiseIncoherentDecay_largeConstantMonotone leafwiseCoherentApproximation30_largeConstantMonotone
  have hm1 : LargeConstantMonotone (fun P => LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) :=
    leafwiseIncoherentDecay_largeConstantMonotone.and leafwiseCoherentApproximation30_largeConstantMonotone
  have hthree : WTPrefix (fun P => (LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) ∧
      TopIncoherentDecayAtR P) :=
    prefix_and hgates IncTop.topIncoherentDecayGateR hm1 Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone
  have hall : WTPrefix (fun P => ((LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) ∧
      TopIncoherentDecayAtR P) ∧ V5FrontierClassBoundAt P) :=
    prefix_and hthree hV (hm1.and Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone)
      v5FrontierClassBoundAt_mono
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hη⟩ := hall d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg : 0 < g1 := by
    rw [hg1]
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    nlinarith
  refine ⟨min η₀ (min (1 / 2) ((g1 / 2) ^ 2)), lt_min hη₀ (lt_min (by norm_num) (by positivity)), ?_⟩
  intro η hηm φin hφin τ hτ φ hsol
  have hη0 : η ≤ η₀ := hηm.2.trans (min_le_left _ _)
  have hη2 : η ≤ 1 / 2 := hηm.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη3 : η ≤ (g1 / 2) ^ 2 := hηm.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₁g, hC₁g, ν₀, hν₀, hrest⟩ := hη η ⟨hηm.1, hη0⟩ φin hφin τ hτ φ hsol
  refine ⟨max C₁g (CvineFW d η C₁g), hC₁g.trans (le_max_left _ _), ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨δ₀, hδ₀, hrest2⟩ := hrest ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, hrest3⟩ := hrest2 δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, ?_⟩
  intro L hL
  obtain ⟨⟨⟨hincP, hcohP⟩, htopP⟩, hVP⟩ := hrest3 L hL
  let Pg : WTParams := ⟨d, γ, η, φin, τ, φ, C₁g, ν, δ, D, C₂, L⟩
  have hL2 : 2 ≤ L := hL₀.trans hL
  have E : GateEnv Pg :=
    { hd1 := by show 1 ≤ d; omega
      hL1 := by show 1 ≤ L; linarith
      hη0 := hηm.1.le
      hη := hη2
      hC1 := hC₁g
      hδ0 := hδ.1.le
      hκ := eta_pow_leN g1 η hg hηm.1 hη3 hη2
      hinc := hincP
      hcoh := hcohP }
  have hV' : V5FrontierClassBoundAt (PB Pg (max C₁g (CvineFW d η C₁g))) :=
    v5FrontierClassBoundAt_mono Pg (max C₁g (CvineFW d η C₁g)) C₂ hC₁g hC₂ hδ.1 hL2 (le_max_left _ _) le_rfl hVP
  have htop' : TopIncoherentDecayAtR (PB Pg (max C₁g (CvineFW d η C₁g))) :=
    Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone Pg (max C₁g (CvineFW d η C₁g)) C₂ hC₁g hC₂ hδ.1 hL2
      (le_max_left _ _) le_rfl htopP
  exact vineCaseRepresentsFW_of_gate Pg (max C₁g (CvineFW d η C₁g)) E htopP hηm.1 hδ.1 hL2 hC₂
    WaveTurbulence.Vine.Param.vineparam (le_max_right _ _) hV' htop'

/-- The weighted Stage-1 reduction gate, from the staged `V5FrontierClassBound` (conditional helper). -/
theorem stage1ReductionGateFW_of_frontier (hV : V5FrontierClassBound) : Stage1ReductionGateFW :=
  stage1ReductionGateFW_of_pieces Stage1WNoVine.noVineRepresentsFW (vineCaseRepresentsFW_of_frontier hV)

end WaveTurbulence.Flower.Stage1WVine
