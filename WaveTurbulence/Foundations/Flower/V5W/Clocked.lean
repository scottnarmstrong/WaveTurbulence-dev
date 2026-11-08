/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W.Analytic

/-! # V5W-0, row 0c (part 1): the weighted member kernel in `sumint` form, with selected rows

Copies of main's `VineEstS2.assemblyWK/WL`, `clLocalStarProduct_eq_weights`, `VineEstS3.assemblyClocked`,
`clockedIntegrand_assembly`, `RegRed.clLocalRecenteredSummand`, `clLocalSummand_recenter`,
`VineEstS2.clLocalRecenteredSummand_sumint` and `Cont.clLocalKernelModC_recentered`,
`Cont.vineChainMod_eq_sumintForm'`, for the pinned kernel:

* `coupleRowFW`, `treeRowFW`: the selected row of a source pair / interior branch (coherent: main's `KQstar`/`KTstar`;
  incoherent: `coupleLeavesTop`/`treeLeavesTop` at the layer profiles), as functions of the two clocks and the momentum;
* `assemblyClockedFW`: the `ClockedRows` with these rows and main's slots;
* `vineChainFW_eq_sumintForm'`: the recentered weighted member kernel, with the multiplier `m` inside the lattice sum and
  the lower-joint modulation `modW λ` (R58), in `sumint` input form.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.DegenVine WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory Filter
  Topology
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineC WaveTurbulence.Flower.Stage1W
open scoped ENNReal

section Rows
variable {w d : ℕ} {G : Garden w}

/-- The selected row of a source pair (the pair factor of `clLocalStarProductFW`). -/
def coupleRowFW (pw : ℕ) (g : Mom d → ℂ) (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
    (pr : SourcePair G) (t s : ℝ) (k : Mom d) : ℂ :=
  if coupleIncoh D hG layer hLayer pr = 0 then
    KQstar L γ δ F (nativeCoupleLayered D hG layer hLayer pr) t s k
  else
    coupleLeavesTop L γ δ pw g (coupleRootParents pw D hG layer hLayer pr 0)
      (coupleRootParents pw D hG layer hLayer pr 1) (nativeCoupleLayered D hG layer hLayer pr)
      (layerProfiles (nativeCoupleLayered D hG layer hLayer pr) F) t s k

/-- The selected row of an interior branch (the branch factor of `clLocalStarProductFW`). -/
def treeRowFW (pw : ℕ) (g : Mom d → ℂ) (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
    (v : GBranch G.tree) (t s : ℝ) (k : Mom d) : ℂ :=
  if treeIncoh D hG layer hLayer v = 0 then
    KTstar L γ δ F (nativeChainLayered D hG layer hLayer v) t s k
  else
    treeLeavesTop L γ δ pw g (treeRootParent pw D hG layer hLayer v) (nativeChainLayered D hG layer hLayer v)
      (layerProfiles (nativeChainLayered D hG layer hLayer v) F) t s k

end Rows

section Assembly
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The selected pair factor of the `v`-th `sumint` row, as a function of its momentum. -/
def assemblyWKFW (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (pw : ℕ) (g : Mom d → ℂ) (D : ReconstructionData G)
    (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (t : Fin 3 → ℝ) (τ : CLInternalTime R)
    (v : (assemblyShape hM9 B).VIdx) (k : Mom d) : ℂ :=
  coupleRowFW pw g D hG L γ δ F layer hLayer (assemblyPairOf hM9 B hG v).1
    (parentClock (t 0) (clLocalClock R t τ) ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode)
    (parentClock (t 0) (clLocalClock R t τ) ((assemblyPairOf hM9 B hG v).1.secondLeaf hG).toNode) k

/-- The selected branch factor of the `v`-th `sumint` row, as a function of its momentum. -/
def assemblyWLFW (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (pw : ℕ) (g : Mom d → ℂ) (D : ReconstructionData G)
    (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (t : Fin 3 → ℝ) (τ : CLInternalTime R)
    (v : (assemblyShape hM9 B).VIdx) (k : Mom d) : ℂ :=
  treeRowFW pw g D hG L γ δ F layer hLayer (assemblyBranchOf hM9 B v).1
    (parentClock (t 0) (clLocalClock R t τ) (assemblyBranchOf hM9 B v).1.toNode)
    (clLocalClock R t τ (assemblyBranchOf hM9 B v).1) k

theorem clLocalStarProductFW_eq_weights (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (pw : ℕ) (g : Mom d → ℂ)
    (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (κ : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (τ : CLInternalTime R) :
    clLocalStarProductFW pw g D hG R L γ δ F layer hLayer base κ t τ =
      ∏ v : (assemblyShape hM9 B).VIdx,
        (assemblyWKFW hM9 B pw g D hG L γ δ F layer hLayer t τ v
            (cosetDecoration G L base κ ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode) *
          assemblyWLFW hM9 B pw g D hG L γ δ F layer hLayer t τ v
            (cosetDecoration G L base κ (assemblyBranchOf hM9 B v).1.toNode)) := by
  rw [Finset.prod_mul_distrib]
  simp only [clLocalStarProductFW]
  refine congrArg₂ (· * ·) ?_ ?_
  · rw [← Finset.prod_coe_sort]
    exact (Equiv.prod_comp ((assemblyRowEquiv hM9 B).symm.trans (assemblyPairOrder hG B hM9).symm)
      (fun p : ↥(clRegionalPairs hG U) => coupleRowFW pw g D hG L γ δ F layer hLayer p.1
        (parentClock (t 0) (clLocalClock R t τ) (p.1.firstLeaf hG).toNode)
        (parentClock (t 0) (clLocalClock R t τ) (p.1.secondLeaf hG).toNode)
        (cosetDecoration G L base κ (p.1.firstLeaf hG).toNode))).symm
  · rw [← Finset.prod_coe_sort]
    exact (Equiv.prod_comp ((assemblyRowEquiv hM9 B).symm.trans (assemblyIntOrder hM9 B).e.symm)
      (fun z : ↥(clInteriorBranches R) => treeRowFW pw g D hG L γ δ F layer hLayer z.1
        (parentClock (t 0) (clLocalClock R t τ) z.1.toNode) (clLocalClock R t τ z.1)
        (cosetDecoration G L base κ z.1.toNode))).symm

/-- **The selected clock-dependent rows of the assembly** (main's slots). -/
def assemblyClockedFW (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShape hM9 B) d) (pw : ℕ) (g : Mom d → ℂ) (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) :
    ClockedRows (sourceSumintDatum hM9 B hG W) where
  W := fun ρ c k => match ρ with
    | Sum.inl v => coupleRowFW pw g RD hG L γ δ F layer hLayer (assemblyPairOf hM9 B hG v).1 (c 0) (c 1) k
    | Sum.inr v => treeRowFW pw g RD hG L γ δ F layer hLayer (assemblyBranchOf hM9 B v).1 (c 0) (c 1) k
  slot := (assemblyClocked hM9 B RD hG W L γ δ F layer hLayer).slot

/-- The integrand of `clockedExpr` for `assemblyClockedFW` is the integrand of the weighted endpoint. -/
theorem clockedIntegrand_assemblyFW (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShape hM9 B) d) (pw : ℕ) (g : Mom d → ℂ) (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (cfs cs : Fin (assemblyShape hM9 B).I → ℤˣ) (γ' δ' η : ℝ) (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ))
    (E : Fin 4 → Mom d) (t : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ) :
    clockedIntegrand (assemblyClockedFW hM9 B RD hG W pw g L γ δ F layer hLayer) cfs cs L γ' δ' η x E t τ =
      signedPhase (sourceSumintDatum hM9 B hG W) cfs cs L γ' δ' η x (E 0 - E 1) (t 0) τ *
        ∏ v, (assemblyWKFW hM9 B pw g RD hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
            ((sourceSumintDatum hM9 B hG W).kVec L x E v) *
          assemblyWLFW hM9 B pw g RD hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
            ((sourceSumintDatum hM9 B hG W).ℓVec L x E v)) := by
  unfold clockedIntegrand
  congr 1
  rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hp := pairLeaf_ne (a := a) hG (assemblyPairOf hM9 B hG v)
  have h1 := nodeSlot_spec hM9 B _ (clRegionalPair_realization hG _ (assemblyPairOf hM9 B hG v).2).1 hp.1 t τ
  have h2 := nodeSlot_spec hM9 B _ (clRegionalPair_realization hG _ (assemblyPairOf hM9 B hG v).2).2 hp.2 t τ
  have hbr := (branch_mem_clRealizationNodes (assemblyBranchOf hM9 B v).1).mpr
    (Finset.mem_erase.mp (assemblyBranchOf hM9 B v).2).2
  have h3 := nodeSlot_spec hM9 B _ hbr (interior_ne (assemblyBranchOf hM9 B v)) t τ
  have h4 := branchSlot_spec hM9 B (assemblyBranchOf hM9 B v) t τ
  simp only [ClockedRows.clock, assemblyClockedFW, assemblyClocked, rowMom, Sum.elim_inl, Sum.elim_inr, slotVal]
  unfold assemblyWKFW assemblyWLFW
  simp only [h1, h2, h3, h4, if_true, Fin.isValue]
  rfl

end Assembly

section Recenter
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- The recentered local summand with selected rows (copy of `RegRed.clLocalRecenteredSummand`). -/
def clLocalRecenteredSummandFW (pw : ℕ) (g : Mom d → ℂ) (D : ReconstructionData G) (hG : G.IsPlain)
    (R : CLRegionData G U a b) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (boundary : Fin 4 → Mom d)
    (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base boundary) (τ : CLInternalTime R) : ℂ :=
  (clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ) *
    (clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t).indicator
      (fun τ => clRegionalPhase G U L γ δ (cosetDecoration G L base (clExtendIndices R κ.1))
          (fun v => clLocalClock R t τ v - t 0) *
        clLocalStarProductFW pw g D hG R L γ δ F layer hLayer base (clExtendIndices R κ.1) t τ) τ

theorem clLocalSummandFW_recenter (hU : G.molecule.IsBlock U a b) (pw : ℕ) (g : Mom d → ℂ)
    (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (boundary : Fin 4 → Mom d)
    (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base boundary) (τ : CLInternalTime R) :
    Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * t 0 *
      boundaryEnergyFromMomenta (G.sign a.toNode) (boundary 0) (boundary 1) (boundary 2) (boundary 3) : ℝ) : ℂ) *
        Complex.I) * clLocalSummandFW pw g D hG R L γ δ F layer hLayer base boundary t κ τ =
      clLocalRecenteredSummandFW pw g D hG R L γ δ F layer hLayer base boundary t κ τ := by
  let A := clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t
  by_cases hτ : τ ∈ A
  · have hp := clLocalDecoration_phase_recenter hU R L γ δ base boundary κ (clLocalClock R t τ) (t 0)
    unfold clLocalSummandFW clLocalRecenteredSummandFW
    rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hτ]
    apply Eq.trans (b := (clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ) *
      ((Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * t 0 *
        boundaryEnergyFromMomenta (G.sign a.toNode) (boundary 0) (boundary 1) (boundary 2) (boundary 3) : ℝ) : ℂ) *
          Complex.I) *
          clRegionalPhase G U L γ δ (cosetDecoration G L base (clExtendIndices R κ.1)) (clLocalClock R t τ)) *
        clLocalStarProductFW pw g D hG R L γ δ F layer hLayer base (clExtendIndices R κ.1) t τ))
    · ring
    · exact congrArg (fun z => (clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ) *
        (z * clLocalStarProductFW pw g D hG R L γ δ F layer hLayer base (clExtendIndices R κ.1) t τ)) hp
  · unfold clLocalSummandFW clLocalRecenteredSummandFW
    rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem hτ]
    simp only [mul_zero]

/-- Recentering inside the weighted kernel (copy of `Cont.clLocalKernelModC_recentered`). -/
theorem clLocalKernelFW_recentered (hU : G.molecule.IsBlock U a b) (pw : ℕ) (g : Mom d → ℂ)
    (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (m : (GNode G.tree → Fin d → ℤ) → ℂ) (W : ℝ → ℂ) (tUpper tPositive tNegative : ℝ) (e f g' h : Mom d) :
    recPhase (G.sign a.toNode) L γ δ tUpper e f g' h *
        clLocalKernelFW pw g D hG R L γ δ F layer hLayer base m W tUpper tPositive tNegative e f g' h =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        ∑' κ : CLLocalDecoration R L base ![e, f, g', h], ∫ τ : CLInternalTime R,
          m (clExtendIndices R κ.1) * (W (clLocalClock R ![tUpper, tPositive, tNegative] τ b) *
            clLocalRecenteredSummandFW pw g D hG R L γ δ F layer hLayer base ![e, f, g', h]
              ![tUpper, tPositive, tNegative] κ τ) := by
  let C := (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R
  let E := Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * tUpper *
    boundaryEnergyFromMomenta (G.sign a.toNode) e f g' h : ℝ) : ℂ) * Complex.I)
  unfold recPhase clLocalKernelFW
  rw [mul_left_comm E C]
  apply congrArg (fun z => C * z)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro κ
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun τ => ?_))
  have := clLocalSummandFW_recenter hU pw g D hG R L γ δ F layer hLayer base ![e, f, g', h]
    ![tUpper, tPositive, tNegative] κ τ
  have this' : Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * tUpper *
      boundaryEnergyFromMomenta (G.sign a.toNode) e f g' h : ℝ) : ℂ) * Complex.I) *
      clLocalSummandFW pw g D hG R L γ δ F layer hLayer base ![e, f, g', h] ![tUpper, tPositive, tNegative] κ τ =
      clLocalRecenteredSummandFW pw g D hG R L γ δ F layer hLayer base ![e, f, g', h]
        ![tUpper, tPositive, tNegative] κ τ := by
    simpa using this
  beta_reduce
  rw [← this']
  ring

end Recenter

section Sumint
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- One summand of the recentered weighted kernel in `sumint` form (copy of `clLocalRecenteredSummand_sumint`). -/
theorem clLocalRecenteredSummandFW_sumint (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (pw : ℕ) (g : Mom d → ℂ)
    (D : ReconstructionData G) (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    (τ : (assemblyShape hM9 B).TVar → ℝ) :
    clLocalRecenteredSummandFW pw g D hG R L γ δ F layer hLayer base (fun j => base + latticePoint L (β j)) t
        ((clNormalizedChainEquiv hL B base β hβ hM9).symm x) (assemblyClockEquiv hM9 B τ) =
      (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ) *
        ((assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R
            (fun v => layer (D.coreBranch hG v).toNode) t).indicator
          (fun τ => signedPhase (sourceSumintDatum hM9 B hG W)
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2 * δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (t 0) τ *
            ∏ v, (assemblyWKFW hM9 B pw g D hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
                ((sourceSumintDatum hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              assemblyWLFW hM9 B pw g D hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
                ((sourceSumintDatum hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v))) τ) := by
  unfold clLocalRecenteredSummandFW
  congr 1
  by_cases h : assemblyClockEquiv hM9 B τ ∈ clLocalTimeDomain R
      (fun v => layer (D.coreBranch hG v).toNode) t
  · have h' : τ ∈ assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R
        (fun v => layer (D.coreBranch hG v).toNode) t := h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    rw [sumintBoundary_gap_physical (L := L) (G.sign a.toNode) base β hβ,
      ← assembly_regionalPhase_eq_signedPhase hM9 B hG W hpar hbad hL base β hβ γ δ η x t τ,
      clLocalStarProductFW_eq_weights hM9 B pw g D hG L γ δ F layer hLayer base]
    refine congrArg (HMul.hMul _) (Finset.prod_congr rfl (fun v _ => ?_))
    rw [← assembly_pair_momentum hM9 B hG W hL base β hβ x v,
      ← assembly_branch_momentum hM9 B hG W hL base β hβ x v]
  · have h' : τ ∉ assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R
        (fun v => layer (D.coreBranch hG v).toNode) t := h
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

/-- **The recentered weighted member kernel in `sumint` form** (copy of `Cont.vineChainMod_eq_sumintForm'` with the
multiplier `m` inside the lattice sum; the modulation is `modW λ` at the lower joint). -/
theorem vineChainFW_eq_sumintForm' (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (pw : ℕ) (g : Mom d → ℂ)
    (D : ReconstructionData G) (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer)
    (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (D.coreBranch hG v).toNode))
    (hok : ConstraintsOK hM9 B W) (base : Mom d) (m : (GNode G.tree → Fin d → ℤ) → ℂ) (lam : ℝ)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (t : Fin 3 → ℝ)
    (hp : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      t 1 ≤ assemblyTimeQ hM9 B (fun v => layer (D.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩))
    (hn : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      t 2 ≤ assemblyTimeQ hM9 B (fun v => layer (D.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩)) :
    recPhase (G.sign a.toNode) L γ δ (t 0) (base + latticePoint L (β 0)) (base + latticePoint L (β 1))
        (base + latticePoint L (β 2)) (base + latticePoint L (β 3)) *
      clLocalKernelFW pw g D hG R L γ δ F layer hLayer base m (modW lam) (t 0) (t 1) (t 2)
        (base + latticePoint L (β 0)) (base + latticePoint L (β 1))
        (base + latticePoint L (β 2)) (base + latticePoint L (β 3)) =
    (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
      ∑' x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ),
        (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ) *
        m (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) *
        ∫ τ in (sourceSumintDatum hM9 B hG W).timeDom (assemblyShape_I_pos hM9 B) (t 0) (t 1) (t 2),
          Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩) : ℝ) : ℂ) * Complex.I) *
          (signedPhase (sourceSumintDatum hM9 B hG W)
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2 * δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (t 0) τ *
            ∏ v, (assemblyWKFW hM9 B pw g D hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
                ((sourceSumintDatum hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              assemblyWLFW hM9 B pw g D hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
                ((sourceSumintDatum hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v))) := by
  let H := clLocalRecenteredSummandFW pw g D hG R L γ δ F layer hLayer base
    (fun j => base + latticePoint L (β j)) t
  have hb : ![base + latticePoint L (β 0), base + latticePoint L (β 1),
      base + latticePoint L (β 2), base + latticePoint L (β 3)] = fun j => base + latticePoint L (β j) := by
    funext j
    fin_cases j <;> rfl
  have ht : ![t 0, t 1, t 2] = t := by funext j; fin_cases j <;> rfl
  have hsrc := clLocalKernelFW_recentered B.isBlock pw g D hG R L γ δ F layer hLayer base m (modW lam)
    (t 0) (t 1) (t 2) (base + latticePoint L (β 0)) (base + latticePoint L (β 1))
      (base + latticePoint L (β 2)) (base + latticePoint L (β 3))
  generalize hbb : ![base + latticePoint L (β 0), base + latticePoint L (β 1),
      base + latticePoint L (β 2), base + latticePoint L (β 3)] = bb at hsrc
  obtain rfl : bb = fun j => base + latticePoint L (β j) := hbb.symm.trans hb
  simp only [ht] at hsrc
  rw [hsrc]
  set Hm : CLLocalDecoration R L base (fun j => base + latticePoint L (β j)) → CLInternalTime R → ℂ :=
    fun κ τ => m (clExtendIndices R κ.1) * (modW lam (clLocalClock R t τ b) * H κ τ) with hHm
  have hs : (∑' κ, ∫ τ, Hm κ τ) =
      ∑' x, ∫ τ, Hm ((clNormalizedChainEquiv hL B base β hβ hM9).symm x) τ :=
    ((clNormalizedChainEquiv hL B base β hβ hM9).symm.tsum_eq (fun κ => ∫ τ, Hm κ τ)).symm
  refine congrArg (fun z : ℂ => (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R * z) (hs.trans ?_)
  refine tsum_congr fun x => ?_
  rw [assemblyClock_integral hM9 B (Hm ((clNormalizedChainEquiv hL B base β hβ hM9).symm x))]
  have hpt : ∀ τ : (assemblyShape hM9 B).TVar → ℝ,
      Hm ((clNormalizedChainEquiv hL B base β hβ hM9).symm x) (assemblyClockEquiv hM9 B τ) =
        ((clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ) *
          m (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)) *
        ((assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t).indicator
          (fun τ => Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩) : ℝ) : ℂ) *
              Complex.I) *
            (signedPhase (sourceSumintDatum hM9 B hG W)
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2 * δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (t 0) τ *
            ∏ v, (assemblyWKFW hM9 B pw g D hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
                ((sourceSumintDatum hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              assemblyWLFW hM9 B pw g D hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
                ((sourceSumintDatum hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v)))) τ) := by
    intro τ
    have hs := clLocalRecenteredSummandFW_sumint hM9 B pw g D hG W hpar hbad hL γ δ η F layer hLayer base β hβ x t τ
    have hbclock : clLocalClock R t (assemblyClockEquiv hM9 B τ) b =
        τ (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩) := by
      have := clLocalClock_slot hM9 B t τ (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩)
      rwa [assemblyClockAtom_first hM9 B (assemblyShape_I_pos hM9 B)] at this
    simp only [hHm]
    change m (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) *
        (modW lam (clLocalClock R t (assemblyClockEquiv hM9 B τ) b) *
          clLocalRecenteredSummandFW pw g D hG R L γ δ F layer hLayer base (fun j => base + latticePoint L (β j)) t _
            (assemblyClockEquiv hM9 B τ)) = _
    rw [hs]
    unfold modW
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

end Sumint

end WaveTurbulence.Flower.V5W
