/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.Core
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.ModKernel
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Step3AtH
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LeafChild
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LeafWire
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.ModKernel` (sha256 79849973c2fa52c6…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

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
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.Cont
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.Cont
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3
  WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory Filter Topology
open scoped ENNReal

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

variable {R : CLRegionData G U a b} {n : ℕ}

/-- **The modulated recentered kernel in `sumint` form** (`vineChain_eq_sumintForm'` with the factor `e^{πiλτ_b}`). -/
theorem vineChainMod_eq_sumintForm'Γ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (D : ReconstructionData G)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer)
    (hq : W.q = assemblyTimeQΓ hM9 B (fun v => layer (D.coreBranch hG v).toNode))
    (hok : ConstraintsOKΓ hM9 B W) (base : Mom d) (lam : ℝ) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (t : Fin 3 → ℝ)
    (hp : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      t 1 ≤ assemblyTimeQΓ hM9 B (fun v => layer (D.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩))
    (hn : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      t 2 ≤ assemblyTimeQΓ hM9 B (fun v => layer (D.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩)) :
    clRecenteredLocalKernelModC D hG R L γ δ F layer hLayer base lam (t 0) (t 1) (t 2)
      (base + latticePoint L (β 0)) (base + latticePoint L (β 1))
      (base + latticePoint L (β 2)) (base + latticePoint L (β 3)) =
    (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
      ∑' x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ),
        (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1) : ℂ) *
        ∫ τ in (sourceSumintDatumΓ hM9 B hG W).timeDom (assemblyShape_I_posΓ hM9 B) (t 0) (t 1) (t 2),
          Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩) : ℝ) : ℂ) * Complex.I) *
          (signedPhase (sourceSumintDatumΓ hM9 B hG W)
              (assemblyCoreFirstSignΓ hM9 B) (assemblyCoreSignΓ hM9 B) L γ (2 * δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (t 0) τ *
            ∏ v, (assemblyWKΓ hM9 B D hG L γ δ F layer hLayer t (assemblyClockEquivΓ hM9 B τ) v
                ((sourceSumintDatumΓ hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              assemblyWLΓ hM9 B D hG L γ δ F layer hLayer t (assemblyClockEquivΓ hM9 B τ) v
                ((sourceSumintDatumΓ hM9 B hG W).ℓVec L x
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
      ∑' x, ∫ τ, Hm ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x) τ :=
    ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm.tsum_eq (fun κ => ∫ τ, Hm κ τ)).symm
  refine congrArg (fun z : ℂ => (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R * z) (hs.trans ?_)
  refine tsum_congr fun x => ?_
  rw [assemblyClock_integralΓ hM9 B (Hm ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x))]
  have hpt : ∀ τ : (assemblyShapeΓ hM9 B).TVar → ℝ,
      Hm ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x) (assemblyClockEquivΓ hM9 B τ) =
        (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1) : ℂ) *
        ((assemblyClockEquivΓ hM9 B ⁻¹' clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t).indicator
          (fun τ => Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩) : ℝ) : ℂ) *
              Complex.I) *
            (signedPhase (sourceSumintDatumΓ hM9 B hG W)
              (assemblyCoreFirstSignΓ hM9 B) (assemblyCoreSignΓ hM9 B) L γ (2 * δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (t 0) τ *
            ∏ v, (assemblyWKΓ hM9 B D hG L γ δ F layer hLayer t (assemblyClockEquivΓ hM9 B τ) v
                ((sourceSumintDatumΓ hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              assemblyWLΓ hM9 B D hG L γ δ F layer hLayer t (assemblyClockEquivΓ hM9 B τ) v
                ((sourceSumintDatumΓ hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v)))) τ) := by
    intro τ
    have hs := clLocalRecenteredSummand_sumintΓ hM9 B D hG W hpar hbad hL γ δ η F layer hLayer base β hβ x t τ
    have hbclock : clLocalClock R t (assemblyClockEquivΓ hM9 B τ) b =
        τ (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩) := by
      have := clLocalClock_slotΓ hM9 B t τ (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩)
      rwa [assemblyClockAtom_firstΓ hM9 B (assemblyShape_I_posΓ hM9 B)] at this
    simp only [hHm]
    change lowModC R lam t (assemblyClockEquivΓ hM9 B τ) *
        clLocalRecenteredSummand D hG R L γ δ F layer hLayer base (fun j => base + latticePoint L (β j)) t _
          (assemblyClockEquivΓ hM9 B τ) = _
    rw [hs]
    unfold lowModC
    rw [hbclock]
    by_cases hmem : τ ∈ assemblyClockEquivΓ hM9 B ⁻¹' clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t
    · simp only [Set.indicator_of_mem hmem]
      ring
    · simp only [Set.indicator_of_notMem hmem]
      ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
  congr 1
  rw [integral_clockDomain_eq'Γ hM9 B (assemblyShape_I_posΓ hM9 B) _ t hp hn,
    ← setIntegral_timeDom_eq_assemblyΓ hM9 B hG W _ hq hok]
  rfl

end WaveTurbulence.GammaLow.Famb.VineEstS5C.Cont
