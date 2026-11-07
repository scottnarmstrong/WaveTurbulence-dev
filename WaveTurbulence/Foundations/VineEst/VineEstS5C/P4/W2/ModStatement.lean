/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Statement
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsBase
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.ModClass

/-! # The modulated vine estimate (ruling R58, finding F-LOWCLOCK)

The lower-child slots of a unit read the clock `τ_b` of the unit's lower joint `b` (TARGET (redkg) L1726, integrated inside
`K^U`, L1737-L1738).  S2 expands them in `τ_b` (VINE-D), which produces modulations `e^{πiλτ_b}` inside the unit kernel.
TARGET's `sumint` tolerates such modulations (the parameters `λ_jⁱ` of (sumintI1), loss `max⟨λ⟩^{η⁶}` in (FourierboundI), L1618).

* The modulated class kernel is V5-CONT's `Cont.twistedRecenteredModC … λ` (`Cont/ModClass.lean`, with `Cont.lowModC R λ t τ =
  exp(πiλτ_b)` inside each member's time integral, `b` the region's lower joint; `twistedRecenteredModC_zero`: `λ = 0` is
  `twistedRecentered`).  No second definition is made here (wt-orch, after V5-CONT READY).
* **`VineEstCanonLayerC2M`**, **`VineEstCanonLayerHalfM`**: `VineEstCanonLayerC2` / `Half` for the modulated class kernel, with the loss
  `(1 + |λ|)^{6η⁶}` on the right-hand side; `λ ∈ ℝ`, `kind = true` (R57: the V5-KIND pass generalizes `kind`).
  `vineEstCanonLayerC2_of_M`, `vineEstCanonLayerHalf_of_M`: the unmodulated statements are the case `λ = 0`.
  `vineEstCanonLayerHalfM_of_C2M`: (ii) from (i) as in R54.
* **`memberAbs`** (S2 request, INTERFACE v2): the absolute summability of the internal integrand of one class member,
  `∑_κ ∫ ‖lowModC · clLocalSummand‖ ≤ baseConst`, uniformly in the exterior times and boundary momenta.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  WaveTurbulence.VineEstS4 VineParamContract TTree MeasureTheory
open scoped ENNReal

/-- **TARGET Proposition `vineest` (layer-uniform, `C₂ ^ b` form, R54 (i)) for the modulated class kernel (R58).**
`VineEstCanonLayerC2` with the factor `e^{πiλτ_b}` in the integrand and the loss `(1 + |λ|)^{6η⁶}`. -/
def VineEstCanonLayerC2M (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 ≤ B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (_hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer), (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ),
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => WaveTurbulence.VineEstS5C.Cont.twistedRecenteredModC G a (canonFinset p (startState B RD hG layer hLayer) (chainStart B))
        P.L P.γ P.δ h wBar lam
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀) *
      P.C₂ ^ (Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card))

/-- **TARGET Proposition `vineest` (layer-uniform, halved bad-vine gain, R54 (ii)) for the modulated class kernel (R58).** -/
def VineEstCanonLayerHalfM (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 ≤ B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (_hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer), (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ),
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => WaveTurbulence.VineEstS5C.Cont.twistedRecenteredModC G a (canonFinset p (startState B RD hG layer hLayer) (chainStart B))
        P.L P.γ P.δ h wBar lam
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀)))

/-- The unmodulated `C₂ ^ b` statement is the case `λ = 0` of the modulated one. -/
theorem vineEstCanonLayerC2_of_M (P : WTParams) (H : VineEstCanonLayerC2M P) : VineEstCanonLayerC2 P := by
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer hlay hord hl1 centre wBar hcoh
  have key := H hp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer hlay hord hl1 centre wBar 0 hcoh
  simp only [WaveTurbulence.VineEstS5C.Cont.twistedRecenteredModC_zero, abs_zero, add_zero, Real.one_rpow, one_mul] at key
  exact key

/-- The unmodulated halved-gain statement is the case `λ = 0` of the modulated one. -/
theorem vineEstCanonLayerHalf_of_M (P : WTParams) (H : VineEstCanonLayerHalfM P) : VineEstCanonLayerHalf P := by
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer hlay hord hl1 centre wBar hcoh
  have key := H hp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer hlay hord hl1 centre wBar 0 hcoh
  simp only [WaveTurbulence.VineEstS5C.Cont.twistedRecenteredModC_zero, abs_zero, add_zero, Real.one_rpow, one_mul] at key
  exact key

/-- **R54 (ii) from (i), modulated**: the halved-gain modulated statement follows from the `C₂ ^ b` modulated statement in prefix
form (`L₀` enlarged to `C₂^{2/η²}`). -/
theorem vineEstCanonLayerHalfM_of_C2M (H : WTPrefix VineEstCanonLayerC2M) : WTPrefix VineEstCanonLayerHalfM := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H1⟩ := H d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφin τ hτ φ hsol => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H1 η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD htime => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD htime
  refine ⟨C₂, hC₂, max L₀ (C₂ ^ (2 / η ^ 2)), le_max_of_le_left hL₀, fun L hL => ?_⟩
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans hL
  have hLC : C₂ ^ (2 / η ^ 2) ≤ L := (le_max_right _ _).trans hL
  have hLpos : 0 < L := by linarith
  have key : VineEstCanonLayerC2M ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩ := H4 L hLL₀
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer hlay hord hl1 centre wBar lam hcoh
  refine (key hp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer hlay hord hl1 centre wBar lam hcoh).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hδ0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
  exact half_of_C2_real (pow_nonneg (mul_nonneg (by linarith) hδ0) _)
    (regionLeafSize_const_nonneg RD hG R layer hLayer hB₀) hLpos (C2_pow_le _ hη.1 hC₂ hLC)

/-- **TARGET Proposition `vineest` (layer-uniform, `C₂ ^ b` form, R54 (i)) for the modulated class kernel (R58).**
`VineEstCanonLayerC2K` with the factor `e^{πiλτ_b}` in the integrand and the loss `(1 + |λ|)^{6η⁶}`. -/
def VineEstCanonLayerC2MK (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 ≤ B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (_hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool), CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ),
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => WaveTurbulence.VineEstS5C.Cont.twistedRecenteredModC G a (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B))
        P.L P.γ P.δ h wBar lam
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀) *
      P.C₂ ^ (Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card))

/-- **TARGET Proposition `vineest` (layer-uniform, halved bad-vine gain, R54 (ii)) for the modulated class kernel (R58).** -/
def VineEstCanonLayerHalfMK (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 ≤ B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (_hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool), CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ),
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => WaveTurbulence.VineEstS5C.Cont.twistedRecenteredModC G a (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B))
        P.L P.γ P.δ h wBar lam
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀)))

/-- The unmodulated `C₂ ^ b` statement is the case `λ = 0` of the modulated one. -/
theorem vineEstCanonLayerC2K_of_MK (P : WTParams) (H : VineEstCanonLayerC2MK P) : VineEstCanonLayerC2K P := by
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar hcoh
  have key := H hp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar 0 hcoh
  simp only [WaveTurbulence.VineEstS5C.Cont.twistedRecenteredModC_zero, abs_zero, add_zero, Real.one_rpow, one_mul] at key
  exact key

/-- The unmodulated halved-gain statement is the case `λ = 0` of the modulated one. -/
theorem vineEstCanonLayerHalfK_of_MK (P : WTParams) (H : VineEstCanonLayerHalfMK P) : VineEstCanonLayerHalfK P := by
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar hcoh
  have key := H hp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar 0 hcoh
  simp only [WaveTurbulence.VineEstS5C.Cont.twistedRecenteredModC_zero, abs_zero, add_zero, Real.one_rpow, one_mul] at key
  exact key

/-- **R54 (ii) from (i), modulated**: the halved-gain modulated statement follows from the `C₂ ^ b` modulated statement in prefix
form (`L₀` enlarged to `C₂^{2/η²}`). -/
theorem vineEstCanonLayerHalfMK_of_C2MK (H : WTPrefix VineEstCanonLayerC2MK) : WTPrefix VineEstCanonLayerHalfMK := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H1⟩ := H d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφin τ hτ φ hsol => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H1 η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD htime => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD htime
  refine ⟨C₂, hC₂, max L₀ (C₂ ^ (2 / η ^ 2)), le_max_of_le_left hL₀, fun L hL => ?_⟩
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans hL
  have hLC : C₂ ^ (2 / η ^ 2) ≤ L := (le_max_right _ _).trans hL
  have hLpos : 0 < L := by linarith
  have key : VineEstCanonLayerC2MK ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩ := H4 L hLL₀
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam hcoh
  refine (key hp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam hcoh).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hδ0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
  exact half_of_C2_real (pow_nonneg (mul_nonneg (by linarith) hδ0) _)
    (regionLeafSize_const_nonneg RD hG R layer hLayer hB₀) hLpos (C2_pow_le _ hη.1 hC₂ hLC)

section Abs
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {D : ReconstructionData G} {hG : G.IsPlain} {L γ δ : ℝ} {F : ℕ → Mom d → ℝ}
  {layer : GNode (D.forest hG) → ℕ} {hLayer : IsLayering (D.garden hG) layer} {base : Mom d}

/-- **Absolute summability of the modulated internal integrand of a CL region** (S2 request, R58 INTERFACE v2): every decoration's
integrand is integrable, the `L¹` norms are summable, and their total is at most `baseConst` (independent of the exterior times `t`, of the
boundary momenta and of `λ`).  Hypotheses: the region is a block, the inputs are summable on the base coset (`HF`), `L ≠ 0`. -/
theorem regionAbsM (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hF : HF D hG L F layer base) (hL : L ≠ 0) (lam : ℝ) (boundary : Fin 4 → Mom d) (t : Fin 3 → ℝ) :
    (∀ κ : CLLocalDecoration R L base boundary, Integrable fun τ : CLInternalTime R =>
      WaveTurbulence.VineEstS5C.Cont.lowModC R lam t τ * clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ) ∧
    Summable (fun κ : CLLocalDecoration R L base boundary => ∫ τ : CLInternalTime R,
      ‖WaveTurbulence.VineEstS5C.Cont.lowModC R lam t τ * clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ‖) ∧
    ∑' κ : CLLocalDecoration R L base boundary, ∫ τ : CLInternalTime R,
      ‖WaveTurbulence.VineEstS5C.Cont.lowModC R lam t τ * clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ‖ ≤
      baseConst D hG L γ δ F layer hLayer base R := by
  have hn : ∀ κ : CLLocalDecoration R L base boundary, (fun τ : CLInternalTime R =>
      ‖WaveTurbulence.VineEstS5C.Cont.lowModC R lam t τ * clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ‖) =
      fun τ => ‖clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ‖ := fun κ =>
    funext fun τ => by rw [norm_mul, WaveTurbulence.VineEstS5C.Cont.norm_lowModC, one_mul]
  refine ⟨fun κ => ?_, ?_, ?_⟩
  · have hi := integrable_clLocalSummand (γ := γ) (δ := δ) (hLayer := hLayer) R hF boundary t κ
    refine Integrable.mono' hi.norm ?_ (Filter.Eventually.of_forall fun τ => ?_)
    · refine AEStronglyMeasurable.mul ?_ hi.aestronglyMeasurable
      unfold WaveTurbulence.VineEstS5C.Cont.lowModC
      exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_const.mul
        continuous_id)).mul continuous_const)).comp_aestronglyMeasurable
        (measurable_clock_fixed R t b).aestronglyMeasurable
    · rw [norm_mul, WaveTurbulence.VineEstS5C.Cont.norm_lowModC, one_mul]
  · simp_rw [hn]
    exact summable_integral_norm_clLocalSummand hU R hF hL boundary t
  · simp_rw [hn]
    exact tsum_integral_norm_clLocalSummand_le hU R hF hL boundary t

/-- **Per class member** (state `Bs`, chain `c`): the absolute summability of `twistedLocalKernelM`'s internal integrand, from the coset
summability of every input. -/
theorem memberAbs {ι : Type*} (Bs : FamilyReconstruction w ι) (c : ChainAt Bs.skeleton Bs.family) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (base : Mom d) (hL : L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |F k (base + latticePoint L n)|) (lam : ℝ)
    (boundary : Fin 4 → Mom d) (t : Fin 3 → ℝ) :
    (∀ κ : CLLocalDecoration (clRegionData Bs.skeleton c.block c.cl) L base boundary, Integrable fun τ =>
      WaveTurbulence.VineEstS5C.Cont.lowModC (clRegionData Bs.skeleton c.block c.cl) lam t τ *
        clLocalSummand Bs.data Bs.plain (clRegionData Bs.skeleton c.block c.cl) L γ δ F (stateLayer Bs)
          (stateLayer_isLayering Bs) base boundary t κ τ) ∧
    Summable (fun κ : CLLocalDecoration (clRegionData Bs.skeleton c.block c.cl) L base boundary => ∫ τ,
      ‖WaveTurbulence.VineEstS5C.Cont.lowModC (clRegionData Bs.skeleton c.block c.cl) lam t τ *
        clLocalSummand Bs.data Bs.plain (clRegionData Bs.skeleton c.block c.cl) L γ δ F (stateLayer Bs)
          (stateLayer_isLayering Bs) base boundary t κ τ‖) ∧
    ∑' κ : CLLocalDecoration (clRegionData Bs.skeleton c.block c.cl) L base boundary, ∫ τ,
      ‖WaveTurbulence.VineEstS5C.Cont.lowModC (clRegionData Bs.skeleton c.block c.cl) lam t τ *
        clLocalSummand Bs.data Bs.plain (clRegionData Bs.skeleton c.block c.cl) L γ δ F (stateLayer Bs)
          (stateLayer_isLayering Bs) base boundary t κ τ‖ ≤
      baseConst Bs.data Bs.plain L γ δ F (stateLayer Bs) (stateLayer_isLayering Bs) base
        (clRegionData Bs.skeleton c.block c.cl) :=
  regionAbsM c.block _ (HF_of_all _ _ _ _ _ _ hF) hL lam boundary t

end Abs

end WaveTurbulence.VineEstS5C
