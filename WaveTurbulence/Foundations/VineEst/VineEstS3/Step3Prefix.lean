/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Final
public import WaveTurbulence.Foundations.VineEst.VineEstS3.StepMono
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3AtLeaf
public import WaveTurbulence.Foundations.VineEst.VineEstS3.CohmolBound
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClause

/-! # TARGET vineest Step 3 (L1826-L1870), no-twist case, in prefix form

`Step3Statement P` is the bound (vineest2) for the single-garden recentered kernel `K̃^U_{(G)}` of a (CL) vine chain
(V4's `clRecenteredLocalKernel`, the expression of (vineest1) without the LF-twist sum), in the `sumint` coordinates
(boundary vector permuted by `sumintBoundary`), over the `sumint` output box/set, with `ε` kept.  `vineestStep3` proves it
as a `WTPrefix` statement from the three prefix statements `SumintMixSignedDoubled` (proved unconditionally by DEGEN-VINE's
`SumintMixFinal`), `CoherentApproximationGate30d` (proved by PL23-30D from the B2.1 gates) and `IncoherentDecayGate`
(B2.2, sealed on main).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine WaveTurbulence.LGSpine
  VineParamContract TTree Reg Reg.Skeleton RegRed
open scoped ENNReal
open Set

/-- **TARGET vineest Step 3, no-twist case.** -/
def Step3Statement (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ {Rin : ℕ → Mom P.d → ℝ}, (∀ r ≤ p, InputRemainder P (Rin r) r) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer), (∀ x, layer x ≤ p) →
    RowSizes hM9 B RD hG (P.N (p + 1) ^ 4) → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    CoreVinesNoTwist B RD hG layer hLayer →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d),
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ (inputsF P Rin) p →
    XNorm00Restr (2 * P.η ^ 8) (outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => clRecenteredLocalKernel RD hG R P.L P.γ P.δ (inputsF P Rin) layer hLayer wBar
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7))

/-- The cost `traceConst(2η⁸, χ₀)²` of the two time traces for leaf lower children (a constant of `η` only). -/
noncomputable def traceR (η : ℝ) : ℝ := ((Regref.traceConst (r := 3) (2 * η ^ 8) chiUnit) ^ 2).toReal

theorem one_le_traceR {η : ℝ} (hη : 0 ≤ η) : 1 ≤ traceR η := by
  unfold traceR
  have h1 : (1 : ℝ≥0∞) ≤ Regref.traceConst (r := 3) (2 * η ^ 8) chiUnit ^ 2 :=
    one_le_pow₀ (one_le_traceConst' (by positivity))
  have h2 : Regref.traceConst (r := 3) (2 * η ^ 8) chiUnit ^ 2 ≠ ⊤ := ENNReal.pow_ne_top (traceConst_ne_top _)
  have := ENNReal.toReal_mono h2 h1
  simpa using this

/-- The final constant as a function of the base constant `c₀`. -/
noncomputable def finalCstar (d : ℕ) (η c₀ : ℝ) : ℝ :=
  traceR η * numCstar (ccη η + 1).toReal (finalC0 η) (finalC1 η) (max (CfsOf d η).toReal 1)
    (1 + PL2330.cLeib d (30 * d)) c₀

theorem trace_absorb (T N s Lp : ℝ) (n : ℕ) (hT : 1 ≤ T) (hn : 1 ≤ n) (hN : 0 ≤ N) (hs : 0 ≤ s) (hLp : 0 ≤ Lp) :
    T * ((N * s) ^ n * Lp) ≤ ((T * N) * s) ^ n * Lp := by
  calc T * ((N * s) ^ n * Lp) ≤ T ^ n * ((N * s) ^ n * Lp) :=
        mul_le_mul_of_nonneg_right (le_self_pow₀ hT (by omega)) (mul_nonneg (pow_nonneg (mul_nonneg hN hs) _) hLp)
    _ = ((T * N) * s) ^ n * Lp := by rw [mul_assoc T N s, mul_pow]; ring

/-- The step from the three statements at `P' = {P with C₁ := c₀}` to the literal bound at `P`, `P.C₁ = C*(c₀)`. -/
theorem step3_of_at {A : ℝ} (P : WTParams) (c₀ : ℝ)
    (hdb : SumintMixDoubledAt A {P with C₁ := c₀}) (hA : 6561 ≤ A)
    (hgate : CoherentGateAt {P with C₁ := c₀}) (hinc : IncoherentGateAt {P with C₁ := c₀})
    (hd : 1 ≤ P.d) (hη0 : 0 < P.η) (hη2 : P.η ≤ 1 / 2) (hc : 1 ≤ c₀) (hδ : 0 < P.δ) (hL : 1 ≤ P.L)
    (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) (hCfin : P.C₁ = finalCstar P.d P.η c₀) : Step3Statement P := by
  have hη6 : 6 * P.η ^ 6 ≤ P.η := by
    have h5 : P.η ^ 5 ≤ (1 / 2 : ℝ) ^ 5 := pow_le_pow_left₀ hη0.le hη2 5
    calc 6 * P.η ^ 6 = 6 * P.η ^ 5 * P.η := by ring
      _ ≤ 6 * (1 / 2) ^ 5 * P.η := by gcongr
      _ ≤ P.η := by nlinarith
  intro p hp Rin hR w G U a b R n hM9 B RD hG layer hLayer hlay hsz hM hno centre wBar hcoh
  have hbk := canonBadKind_cases hM9 B RD hG layer
  have hbad := badClause_canon hM9 B RD hG layer hLayer hno (qOutOf RD hG layer a b R) centre wBar
  generalize canonBadKind hM9 B RD hG layer = badKind at hbk hbad hcoh ⊢
  have hqOut : ∀ c, qOutOf RD hG layer a b R c ≤ p := by
    intro c; fin_cases c <;> simp only [qOutOf] <;> exact hlay _
  have hel := fun v => eligible_of hM9 B RD hG layer hLayer
    (step3W hM9 B RD hG layer hLayer badKind (qOutOf RD hG layer a b R) centre wBar) rfl rfl P.L P.γ P.δ
    (inputsF P Rin) (P.N (p + 1) ^ 4) p hlay hsz hcoh v
  have h := step3AtLeaf (P := {P with C₁ := c₀}) hdb hA hgate hinc hd hη0 hη6 hη2 hc hδ hL hw hp hR hM9 B RD hG layer hLayer
    hlay (qOutOf RD hG layer a b R) centre wBar badKind hqOut hbk hbad
    (fun v => by rw [show ({P with C₁ := c₀} : WTParams).N (p + 1) ^ 4 = P.N (p + 1) ^ 4 by rw [N_largeConstants]]; exact hel v)
    (by simpa using hM) (qOutOf_one_le hM9 B RD hG layer hLayer (assemblyShape_I_pos hM9 B))
    (qOutOf_two_le hM9 B RD hG layer hLayer (assemblyShape_I_pos hM9 B))
  have hsb := step3Bound_le {P with C₁ := c₀} (Cfs := CfsOf P.d P.η) (CfsOf_ne_top _ _) hM9 B RD hG layer hLayer badKind
    (qOutOf RD hG layer a b R) centre wBar hη0 (by linarith) hc hδ hL
  have hn2 : 1 ≤ clLocalOrder2 RD hG R := by
    rw [order2_eq hM9 B RD hG]
    exact (M_pos hM9 B).trans (Nat.le_add_right _ _)
  refine h.trans ?_
  have hT : Regref.traceConst (r := 3) (2 * P.η ^ 8) chiUnit ^ 2 = ENNReal.ofReal (traceR P.η) := by
    unfold traceR
    rw [ENNReal.ofReal_toReal (ENNReal.pow_ne_top (traceConst_ne_top _))]
  have hTr := one_le_traceR hη0.le
  have hcb : (1 : ℝ) ≤ 1 + PL2330.cLeib P.d (30 * P.d) := by
    have := PL2330.cLeib_nonneg P.d (30 * P.d); linarith
  have hN1 := one_le_numCstar hc (one_le_ccη_toReal P.η) (one_le_finalC0 hη0.le) (one_le_finalC1 hη0.le)
    (le_max_right (CfsOf P.d P.η).toReal 1) hcb
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  refine (mul_le_mul' le_rfl hsb).trans ?_
  rw [hT, ← ENNReal.ofReal_mul (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hCfin]
  have hcoh : cohmolIndex B RD hG layer ≤
      (step3D hM9 B RD hG layer hLayer badKind (qOutOf RD hG layer a b R) centre wBar).M₀ :=
    cohmolIndex_le_M0 hM9 B RD hG layer (step3W hM9 B RD hG layer hLayer badKind (qOutOf RD hG layer a b R) centre wBar)
      rfl
  have hm : P.η ^ 8 * (cohmolIndex B RD hG layer : ℝ) ≤ P.η ^ 8 *
      ((step3D hM9 B RD hG layer hLayer badKind (qOutOf RD hG layer a b R) centre wBar).M₀ : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcoh) (by positivity)
  refine (trace_absorb (traceR P.η) (numCstar (ccη P.η + 1).toReal (finalC0 P.η) (finalC1 P.η)
    (max (CfsOf P.d P.η).toReal 1) (1 + PL2330.cLeib P.d (30 * P.d)) c₀) (Real.sqrt P.δ) _ (clLocalOrder2 RD hG R) hTr hn2
    (by linarith [hN1]) (Real.sqrt_nonneg _) (Real.rpow_nonneg hL0 _)).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_) (by positivity)
  push_cast
  linarith [hm]

/-- **TARGET vineest Step 3 (no twist), as a prefix statement.**  The three hypotheses are the prefix statements
`SumintMixSignedDoubled` (DEGEN-VINE `sumintMixSignedDoubled`, unconditional), `CoherentApproximationGate30d`
(PL23-30D) and `IncoherentDecayGate` (B2.2, sealed). -/
theorem vineestStep3 (hS : SumintMixSignedDoubled) (hG : CoherentApproximationGate30d)
    (hI : IncoherentDecayGate) : WTPrefix Step3Statement := by
  intro d hd γ hγ
  obtain ⟨ηS, hηS, hSa⟩ := hS d hd γ hγ
  obtain ⟨ηG, hηG, hGa⟩ := hG d hd γ hγ
  obtain ⟨ηI, hηI, hIa⟩ := hI d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1d
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 + 1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hg1 : 0 < g1 := by
    have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    nlinarith
  refine ⟨min (min ηS (min ηG ηI)) (min (1 / 2) (g1 ^ 2)), by
    refine lt_min (lt_min hηS (lt_min hηG hηI)) (lt_min (by norm_num) (by positivity)), ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  have hη0 : 0 < η := hη.1
  have hm : η ≤ min ηS (min ηG ηI) := hη.2.trans (min_le_left _ _)
  have hηS' : η ∈ Ioc 0 ηS := ⟨hη.1, hm.trans (min_le_left _ _)⟩
  have hηG' : η ∈ Ioc 0 ηG := ⟨hη.1, hm.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hηI' : η ∈ Ioc 0 ηI := ⟨hη.1, hm.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hη12 : η ≤ 1 / 2 := hη.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηg : η ≤ g1 ^ 2 := hη.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨CS, hCS, νS, hνS, hSb⟩ := hSa η hηS' 6561 (by norm_num) φin hφin τ hτ φ hsol
  obtain ⟨CG, hCG, νG, hνG, hGb⟩ := hGa η hηG' φin hφin τ hτ φ hsol
  obtain ⟨CI, hCI, νI, hνI, hIb⟩ := hIa η hηI' φin hφin τ hτ φ hsol
  set c₀ : ℝ := max (max CS CG) CI with hc₀d
  have hc₀ : 1 ≤ c₀ := hCS.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hCSc : CS ≤ c₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hCGc : CG ≤ c₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hCIc : CI ≤ c₀ := le_max_right _ _
  have hcb : (1 : ℝ) ≤ 1 + PL2330.cLeib d (30 * d) := by
    have := PL2330.cLeib_nonneg d (30 * d); linarith
  have hfin : 1 ≤ finalCstar d η c₀ := by
    unfold finalCstar
    exact one_le_mul_of_one_le_of_one_le (one_le_traceR hη0.le)
      (one_le_numCstar hc₀ (one_le_ccη_toReal η) (one_le_finalC0 hη0.le) (one_le_finalC1 hη0.le) (le_max_right _ _) hcb)
  refine ⟨finalCstar d η c₀, hfin, min νS (min νG νI), lt_min hνS (lt_min hνG hνI), ?_⟩
  intro ν hν
  have hνS' : ν ∈ Ioc 0 νS := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hνG' : ν ∈ Ioc 0 νG := ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hνI' : ν ∈ Ioc 0 νI := ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨δS, hδS, hSc⟩ := hSb ν hνS'
  obtain ⟨δG, hδG, hGc⟩ := hGb ν hνG'
  obtain ⟨δI, hδI, hIc⟩ := hIb ν hνI'
  refine ⟨min δS (min δG δI), lt_min hδS (lt_min hδG hδI), ?_⟩
  intro δ hδ D hD htime
  have hδS' : δ ∈ Ioc 0 δS := ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩
  have hδG' : δ ∈ Ioc 0 δG := ⟨hδ.1, hδ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hδI' : δ ∈ Ioc 0 δI := ⟨hδ.1, hδ.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨C₂S, hC₂S, LS, hLS, hSd⟩ := hSc δ hδS' D hD htime
  obtain ⟨C₂G, hC₂G, LG, hLG, hGd⟩ := hGc δ hδG' D hD htime
  obtain ⟨C₂I, hC₂I, LI, hLI, hId⟩ := hIc δ hδI' D hD htime
  refine ⟨max C₂S (max C₂G C₂I), hC₂S.trans (le_max_left _ _), max LS (max LG LI),
    hLS.trans (le_max_left _ _), ?_⟩
  intro L hL
  have hLS' : LS ≤ L := (le_max_left _ _).trans hL
  have hLG' : LG ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hLI' : LI ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  have hL2 : 2 ≤ L := hLS.trans hLS'
  set C₂ : ℝ := max C₂S (max C₂G C₂I) with hC₂d
  have hC₂S' : C₂S ≤ C₂ := le_max_left _ _
  have hC₂G' : C₂G ≤ C₂ := le_max_of_le_right (le_max_left _ _)
  have hC₂I' : C₂I ≤ C₂ := le_max_of_le_right (le_max_right _ _)
  let PS : WTParams := ⟨d, γ, η, φin, τ, φ, CS, ν, δ, D, C₂S, L⟩
  let PG : WTParams := ⟨d, γ, η, φin, τ, φ, CG, ν, δ, D, C₂G, L⟩
  let PI : WTParams := ⟨d, γ, η, φin, τ, φ, CI, ν, δ, D, C₂I, L⟩
  let PF : WTParams := ⟨d, γ, η, φin, τ, φ, finalCstar d η c₀, ν, δ, D, C₂, L⟩
  have h1 : SumintMixDoubledAt 6561 {PF with C₁ := c₀} :=
    sumintMix_mono 6561 PS c₀ C₂ hCS hC₂S hδ.1 hL2 hCSc hC₂S' (hSd L hLS')
  have h2 : CoherentGateAt {PF with C₁ := c₀} :=
    coherentGate_mono PG c₀ C₂ hCG hC₂G hδ.1 (hLG.trans hLG') hCGc hC₂G' (hGd L hLG')
  have h3 : IncoherentGateAt {PF with C₁ := c₀} :=
    incoherentGate_mono PI c₀ C₂ hCI hC₂I hδ.1 (hLI.trans hLI') hCIc hC₂I' (hId L hLI')
  have hw : 0 ≤ PF.gamma1 - Real.sqrt PF.η := by
    have : Real.sqrt η ≤ g1 := Real.sqrt_le_iff.2 ⟨hg1.le, hηg⟩
    show 0 ≤ g1 - Real.sqrt η
    linarith
  have key : Step3Statement PF :=
    step3_of_at PF c₀ h1 (le_refl _) h2 h3 (by show 1 ≤ d; omega) hη0 hη12 hc₀ hδ.1 (by show 1 ≤ L; linarith) hw rfl
  exact @key

end WaveTurbulence.VineEstS3
