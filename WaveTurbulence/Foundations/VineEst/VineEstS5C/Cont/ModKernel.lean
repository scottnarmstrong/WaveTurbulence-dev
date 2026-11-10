/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.Core

/-! # V5-CONT (R58), the modulated kernel in `sumint` form

`lowModC R lam t τ = e^{πiλ τ_b}` (τ_b the clock of the lower joint `b`), `clLocalKernelModC` / `clRecenteredLocalKernelModC`:
`clLocalKernel` / `clRecenteredLocalKernel` with `lowModC` inserted in the time integrand.  These are the definitions of R58
(same formulas as the W13 definitions `lowMod`, `clLocalKernelMod`; `λ` is a real number here, the case `λ : ℤ` is a cast).

* `clRecenteredLocalKernelModC_congr`: the modulated kernel does not depend on the time of a leaf lower child.
* `kernelMod_eq_clockedExprEpsM`: at points of the output set, the modulated recentered kernel is
  `coupling^{n₁} ζ · clockedExprEpsM` where `clockedExprEpsM` is the clocked expression with the factor
  `m τ = e^{πiλ τ_slot0}` in the time integrand (`τ_slot0` is the clock of the first slot, i.e. of the lower joint).
* `continuousOn_clockedExprEpsM`: continuity of `clockedExprEpsM` for a bounded jointly continuous factor.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.Cont
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine
  WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory Filter Topology
open scoped ENNReal

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- The modulation `e^{πiλτ_b}` at the lower joint `b` of the region. -/
noncomputable def lowModC (R : CLRegionData G U a b) (lam : ℝ) (t : Fin 3 → ℝ) (τ : CLInternalTime R) : ℂ :=
  Complex.exp (((Real.pi * lam * clLocalClock R t τ b : ℝ) : ℂ) * Complex.I)

theorem norm_lowModC (R : CLRegionData G U a b) (lam : ℝ) (t : Fin 3 → ℝ) (τ : CLInternalTime R) :
    ‖lowModC R lam t τ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- `K^U` with the modulation `e^{πiλτ_b}` in the time integrand. -/
noncomputable def clLocalKernelModC (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (lam : ℝ)
    (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) : ℂ :=
  (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
    ∑' κ : CLLocalDecoration R L base ![e, f, g, h],
      ∫ τ : CLInternalTime R,
        lowModC R lam ![tUpper, tPositive, tNegative] τ *
          clLocalSummand D hG R L γ δ F layer hLayer base ![e, f, g, h] ![tUpper, tPositive, tNegative] κ τ

/-- The recentered modulated kernel `e^{-πiδL^{2γ}t₀Γ} K^U_λ` (the member term of `twistedRecenteredMod`). -/
noncomputable def clRecenteredLocalKernelModC (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (lam : ℝ)
    (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) : ℂ :=
  Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * tUpper * boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ) *
    Complex.I) * clLocalKernelModC D hG R L γ δ F layer hLayer base lam tUpper tPositive tNegative e f g h

/-- The modulation does not see the time of a leaf lower child. -/
theorem lowModC_congr (R : CLRegionData G U a b) (lam : ℝ) (t t' : Fin 3 → ℝ) (h0 : t 0 = t' 0)
    (hp : (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching ∨ t 1 = t' 1)
    (hn : (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching ∨ t 2 = t' 2)
    (τ : CLInternalTime R) : lowModC R lam t τ = lowModC R lam t' τ := by
  unfold lowModC
  rw [clLocalClock_congr R t t' h0 hp hn τ]

theorem clRecenteredLocalKernelModC_congr (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (lam : ℝ) (tU tP tN tP' tN' : ℝ) (e f g h : Mom d)
    (hp : (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching ∨ tP = tP')
    (hn : (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching ∨ tN = tN') :
    clRecenteredLocalKernelModC D hG R L γ δ F layer hLayer base lam tU tP tN e f g h =
      clRecenteredLocalKernelModC D hG R L γ δ F layer hLayer base lam tU tP' tN' e f g h := by
  unfold clRecenteredLocalKernelModC clLocalKernelModC
  congr 2
  refine tsum_congr fun κ => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  have h0 : ![tU, tP, tN] 0 = ![tU, tP', tN'] 0 := rfl
  have e1 := lowModC_congr R lam ![tU, tP, tN] ![tU, tP', tN'] h0 hp hn τ
  have e2 := clLocalSummand_congr D hG R L γ δ F layer hLayer base ![e, f, g, h] ![tU, tP, tN] ![tU, tP', tN'] rfl hp hn κ τ
  simp only [e1, e2]

variable {R : CLRegionData G U a b} {n : ℕ}

/-- Recentering inside the modulated integral. -/
theorem clLocalKernelModC_recentered (hU : G.molecule.IsBlock U a b) (D : ReconstructionData G) (hG : G.IsPlain)
    (R : CLRegionData G U a b) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (lam : ℝ)
    (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) :
    clRecenteredLocalKernelModC D hG R L γ δ F layer hLayer base lam tUpper tPositive tNegative e f g h =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        ∑' κ : CLLocalDecoration R L base ![e, f, g, h], ∫ τ : CLInternalTime R,
          lowModC R lam ![tUpper, tPositive, tNegative] τ *
            clLocalRecenteredSummand D hG R L γ δ F layer hLayer base ![e, f, g, h]
              ![tUpper, tPositive, tNegative] κ τ := by
  let C := (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R
  let E := Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * tUpper *
    boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ) * Complex.I)
  unfold clRecenteredLocalKernelModC clLocalKernelModC
  rw [mul_left_comm E C]
  apply congrArg (fun z => C * z)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro κ
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun τ => ?_))
  have := clLocalSummand_recenter hU D hG R L γ δ F layer hLayer base ![e, f, g, h]
    ![tUpper, tPositive, tNegative] κ τ
  have this' : Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * tUpper *
      boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ) * Complex.I) *
      clLocalSummand D hG R L γ δ F layer hLayer base ![e, f, g, h] ![tUpper, tPositive, tNegative] κ τ =
      clLocalRecenteredSummand D hG R L γ δ F layer hLayer base ![e, f, g, h] ![tUpper, tPositive, tNegative] κ τ := by
    simpa using this
  beta_reduce
  rw [← this']
  ring

/-- **The modulated recentered kernel in `sumint` form** (`vineChain_eq_sumintForm'` with the factor `e^{πiλτ_b}`). -/
theorem vineChainMod_eq_sumintForm' (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (D : ReconstructionData G)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer)
    (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (D.coreBranch hG v).toNode))
    (hok : ConstraintsOK hM9 B W) (base : Mom d) (lam : ℝ) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (t : Fin 3 → ℝ)
    (hp : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      t 1 ≤ assemblyTimeQ hM9 B (fun v => layer (D.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩))
    (hn : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      t 2 ≤ assemblyTimeQ hM9 B (fun v => layer (D.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩)) :
    clRecenteredLocalKernelModC D hG R L γ δ F layer hLayer base lam (t 0) (t 1) (t 2)
      (base + latticePoint L (β 0)) (base + latticePoint L (β 1))
      (base + latticePoint L (β 2)) (base + latticePoint L (β 3)) =
    (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
      ∑' x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ),
        (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ) *
        ∫ τ in (sourceSumintDatum hM9 B hG W).timeDom (assemblyShape_I_pos hM9 B) (t 0) (t 1) (t 2),
          Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩) : ℝ) : ℂ) * Complex.I) *
          (signedPhase (sourceSumintDatum hM9 B hG W)
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2 * δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (t 0) τ *
            ∏ v, (assemblyWK hM9 B D hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
                ((sourceSumintDatum hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              assemblyWL hM9 B D hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
                ((sourceSumintDatum hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v))) := by
  let H := clLocalRecenteredSummand D hG R L γ δ F layer hLayer base
    (fun j => base + latticePoint L (β j)) t
  have hb : ![base + latticePoint L (β 0), base + latticePoint L (β 1),
      base + latticePoint L (β 2), base + latticePoint L (β 3)] = fun j => base + latticePoint L (β j) := by
    funext j
    fin_cases j <;> rfl
  have ht : ![t 0, t 1, t 2] = t := by funext j; fin_cases j <;> rfl
  have hsrc := clLocalKernelModC_recentered B.isBlock D hG R L γ δ F layer hLayer base lam
    (t 0) (t 1) (t 2) (base + latticePoint L (β 0)) (base + latticePoint L (β 1))
      (base + latticePoint L (β 2)) (base + latticePoint L (β 3))
  generalize hbb : ![base + latticePoint L (β 0), base + latticePoint L (β 1),
      base + latticePoint L (β 2), base + latticePoint L (β 3)] = bb at hsrc
  obtain rfl : bb = fun j => base + latticePoint L (β j) := hbb.symm.trans hb
  simp only [ht] at hsrc
  rw [hsrc]
  set Hm : CLLocalDecoration R L base (fun j => base + latticePoint L (β j)) → CLInternalTime R → ℂ :=
    fun κ τ => lowModC R lam t τ * H κ τ with hHm
  have hs : (∑' κ, ∫ τ, Hm κ τ) =
      ∑' x, ∫ τ, Hm ((clNormalizedChainEquiv hL B base β hβ hM9).symm x) τ :=
    ((clNormalizedChainEquiv hL B base β hβ hM9).symm.tsum_eq (fun κ => ∫ τ, Hm κ τ)).symm
  refine congrArg (fun z : ℂ => (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R * z) (hs.trans ?_)
  refine tsum_congr fun x => ?_
  rw [assemblyClock_integral hM9 B (Hm ((clNormalizedChainEquiv hL B base β hβ hM9).symm x))]
  have hpt : ∀ τ : (assemblyShape hM9 B).TVar → ℝ,
      Hm ((clNormalizedChainEquiv hL B base β hβ hM9).symm x) (assemblyClockEquiv hM9 B τ) =
        (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ) *
        ((assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t).indicator
          (fun τ => Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩) : ℝ) : ℂ) *
              Complex.I) *
            (signedPhase (sourceSumintDatum hM9 B hG W)
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2 * δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (t 0) τ *
            ∏ v, (assemblyWK hM9 B D hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
                ((sourceSumintDatum hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              assemblyWL hM9 B D hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
                ((sourceSumintDatum hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v)))) τ) := by
    intro τ
    have hs := clLocalRecenteredSummand_sumint hM9 B D hG W hpar hbad hL γ δ η F layer hLayer base β hβ x t τ
    have hbclock : clLocalClock R t (assemblyClockEquiv hM9 B τ) b =
        τ (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩) := by
      have := clLocalClock_slot hM9 B t τ (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩)
      rwa [assemblyClockAtom_first hM9 B (assemblyShape_I_pos hM9 B)] at this
    simp only [hHm]
    change lowModC R lam t (assemblyClockEquiv hM9 B τ) *
        clLocalRecenteredSummand D hG R L γ δ F layer hLayer base (fun j => base + latticePoint L (β j)) t _
          (assemblyClockEquiv hM9 B τ) = _
    rw [hs]
    unfold lowModC
    rw [hbclock]
    by_cases hmem : τ ∈ assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t
    · simp only [Set.indicator_of_mem hmem]
      ring
    · simp only [Set.indicator_of_notMem hmem]
      ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
  congr 1
  rw [integral_clockDomain_eq' hM9 B (assemblyShape_I_pos hM9 B) _ t hp hn,
    ← setIntegral_timeDom_eq_assembly hM9 B hG W _ hq hok]
  rfl

end WaveTurbulence.VineEstS5C.Cont
