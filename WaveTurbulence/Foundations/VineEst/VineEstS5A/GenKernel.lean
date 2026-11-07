/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLKernelReindex

/-! # The recentered regional kernel with an abstract regular-object factor (V5 Step 4d-A, item 3)

`clLocalStarProduct` (the product of the native starred kernels of the regional pairs and interior branches) is the
only place where the regular objects enter the CL-local expression.  The `Gen` versions of the recentering
(`clLocalSummand_recenter`, `clLocalKernel_recentered_formula`) and of the lattice/clock change
(`clLocalKernel_reindexed`) take an ARBITRARY factor `Φ κ t τ` in its place; with `Φ = clLocalStarProduct` they are
the existing declarations (`clRecenteredLocalKernelGen_star`).  Proofs are those of the originals.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5A
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- The local summand with an abstract factor `Φ` in place of `clLocalStarProduct`. -/
noncomputable def clLocalSummandGen (R : CLRegionData G U a b)
    (Φ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → CLInternalTime R → ℂ)
    (layer0 : GBranch G.tree → ℕ)
    (L γ δ : ℝ) (base : Mom d) (boundary : Fin 4 → Mom d)
    (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base boundary) (τ : CLInternalTime R) : ℂ :=
  (clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ) *
    (clLocalTimeDomain R layer0 t).indicator
      (fun τ => clRegionalPhase G U L γ δ (cosetDecoration G L base (clExtendIndices R κ.1))
          (clLocalClock R t τ) * Φ (clExtendIndices R κ.1) t τ) τ

/-- The recentered local summand with an abstract factor. -/
noncomputable def clLocalRecenteredSummandGen (R : CLRegionData G U a b)
    (Φ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → CLInternalTime R → ℂ)
    (layer0 : GBranch G.tree → ℕ)
    (L γ δ : ℝ) (base : Mom d) (boundary : Fin 4 → Mom d)
    (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base boundary) (τ : CLInternalTime R) : ℂ :=
  (clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ) *
    (clLocalTimeDomain R layer0 t).indicator
      (fun τ => clRegionalPhase G U L γ δ (cosetDecoration G L base (clExtendIndices R κ.1))
          (fun v => clLocalClock R t τ v - t 0) * Φ (clExtendIndices R κ.1) t τ) τ

/-- The seven-argument local kernel with an abstract factor. -/
noncomputable def clLocalKernelGen (R : CLRegionData G U a b)
    (Φ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → CLInternalTime R → ℂ)
    (layer0 : GBranch G.tree → ℕ) (L γ δ : ℝ) (base : Mom d)
    (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) : ℂ :=
  (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R *
    ∑' κ : CLLocalDecoration R L base ![e,f,g,h],
      ∫ τ : CLInternalTime R,
        clLocalSummandGen R Φ layer0 L γ δ base ![e,f,g,h] ![tUpper,tPositive,tNegative] κ τ

/-- The recentered kernel with an abstract factor. -/
noncomputable def clRecenteredLocalKernelGen (R : CLRegionData G U a b)
    (Φ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → CLInternalTime R → ℂ)
    (layer0 : GBranch G.tree → ℕ) (L γ δ : ℝ) (base : Mom d)
    (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) : ℂ :=
  Complex.exp (((-(Real.pi*δ*L^(2*γ))*tUpper*boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ)*Complex.I) *
    clLocalKernelGen R Φ layer0 L γ δ base tUpper tPositive tNegative e f g h

/-- With the native factor the generic kernel is the actual one. -/
theorem clRecenteredLocalKernelGen_star (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) :
    clRecenteredLocalKernelGen R (fun κ t τ => clLocalStarProduct D hG R L γ δ F layer hLayer base κ t τ)
      (fun v => layer (D.coreBranch hG v).toNode) L γ δ base tUpper tPositive tNegative e f g h =
    clRecenteredLocalKernel D hG R L γ δ F layer hLayer base tUpper tPositive tNegative e f g h := rfl

theorem clLocalSummandGen_recenter (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (Φ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → CLInternalTime R → ℂ)
    (layer0 : GBranch G.tree → ℕ) (L γ δ : ℝ) (base : Mom d) (boundary : Fin 4 → Mom d)
    (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base boundary) (τ : CLInternalTime R) :
    Complex.exp (((-(Real.pi*δ*L^(2*γ))*t 0*
      boundaryEnergyFromMomenta (G.sign a.toNode) (boundary 0) (boundary 1) (boundary 2) (boundary 3) : ℝ) : ℂ)*Complex.I) *
        clLocalSummandGen R Φ layer0 L γ δ base boundary t κ τ =
      clLocalRecenteredSummandGen R Φ layer0 L γ δ base boundary t κ τ := by
  let A := clLocalTimeDomain R layer0 t
  by_cases hτ : τ ∈ A
  · have hp := clLocalDecoration_phase_recenter hU R L γ δ base boundary κ (clLocalClock R t τ) (t 0)
    unfold clLocalSummandGen clLocalRecenteredSummandGen
    rw [Set.indicator_of_mem hτ,Set.indicator_of_mem hτ]
    apply Eq.trans (b := (clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ) *
      ((Complex.exp (((-(Real.pi*δ*L^(2*γ))*t 0*
        boundaryEnergyFromMomenta (G.sign a.toNode) (boundary 0) (boundary 1) (boundary 2) (boundary 3) : ℝ) : ℂ)*Complex.I) *
          clRegionalPhase G U L γ δ (cosetDecoration G L base (clExtendIndices R κ.1)) (clLocalClock R t τ)) *
        Φ (clExtendIndices R κ.1) t τ))
    · ring
    · exact congrArg (fun z => (clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ) *
        (z * Φ (clExtendIndices R κ.1) t τ)) hp
  · unfold clLocalSummandGen clLocalRecenteredSummandGen
    rw [Set.indicator_of_notMem hτ,Set.indicator_of_notMem hτ]
    simp only [mul_zero]

theorem clLocalKernelGen_recentered_formula (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (Φ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → CLInternalTime R → ℂ)
    (layer0 : GBranch G.tree → ℕ) (L γ δ : ℝ) (base : Mom d)
    (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) :
    clRecenteredLocalKernelGen R Φ layer0 L γ δ base tUpper tPositive tNegative e f g h =
      (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R *
        ∑' κ : CLLocalDecoration R L base ![e,f,g,h], ∫ τ : CLInternalTime R,
          clLocalRecenteredSummandGen R Φ layer0 L γ δ base ![e,f,g,h]
            ![tUpper,tPositive,tNegative] κ τ := by
  let C := (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R
  let E := Complex.exp (((-(Real.pi*δ*L^(2*γ))*tUpper*
    boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ)*Complex.I)
  unfold clRecenteredLocalKernelGen clLocalKernelGen
  rw [mul_left_comm E C]
  apply congrArg (fun z => C*z)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro κ
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun τ =>
    clLocalSummandGen_recenter hU R Φ layer0 L γ δ base ![e,f,g,h]
      ![tUpper,tPositive,tNegative] κ τ))

variable {R : CLRegionData G U a b} {n : ℕ}

theorem clLocalKernelGen_reindexed {L : ℝ} (hL : L ≠ 0)
    (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (Φ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → CLInternalTime R → ℂ)
    (layer0 : GBranch G.tree → ℕ)
    (γ δ : ℝ) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (t : Fin 3 → ℝ) :
    clRecenteredLocalKernelGen R Φ layer0 L γ δ base (t 0) (t 1) (t 2)
      (base+latticePoint L (β 0)) (base+latticePoint L (β 1))
      (base+latticePoint L (β 2)) (base+latticePoint L (β 3)) =
    (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R *
      ∑' x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ), ∫ τ : (assemblyShape hM9 B).TVar → ℝ,
        clLocalRecenteredSummandGen R Φ layer0 L γ δ base
          (fun j => base+latticePoint L (β j)) t
          ((clNormalizedChainEquiv hL B base β hβ hM9).symm x) (assemblyClockEquiv hM9 B τ) := by
  let H := clLocalRecenteredSummandGen R Φ layer0 L γ δ base
    (fun j => base+latticePoint L (β j)) t
  have hb : ![base+latticePoint L (β 0),base+latticePoint L (β 1),
      base+latticePoint L (β 2),base+latticePoint L (β 3)] = fun j => base+latticePoint L (β j) := by
    funext j
    fin_cases j <;> rfl
  have ht : ![t 0,t 1,t 2] = t := by funext j; fin_cases j <;> rfl
  have hsrc := clLocalKernelGen_recentered_formula B.isBlock R Φ layer0 L γ δ base
    (t 0) (t 1) (t 2) (base+latticePoint L (β 0)) (base+latticePoint L (β 1))
      (base+latticePoint L (β 2)) (base+latticePoint L (β 3))
  generalize hbb : ![base+latticePoint L (β 0),base+latticePoint L (β 1),
      base+latticePoint L (β 2),base+latticePoint L (β 3)] = b at hsrc
  obtain rfl : b = fun j => base+latticePoint L (β j) := hbb.symm.trans hb
  simp only [ht] at hsrc
  have hs : (∑' κ, ∫ τ, H κ τ) =
      ∑' x, ∫ τ, H ((clNormalizedChainEquiv hL B base β hβ hM9).symm x) τ :=
    ((clNormalizedChainEquiv hL B base β hβ hM9).symm.tsum_eq (fun κ => ∫ τ, H κ τ)).symm
  calc
    _ = (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R * (∑' κ, ∫ τ, H κ τ) := hsrc
    _ = _ := congrArg (fun z : ℂ => (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R*z) hs
    _ = _ := by
      apply congrArg (fun z : ℂ => (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R*z)
      apply tsum_congr
      intro x
      exact assemblyClock_integral hM9 B (H ((clNormalizedChainEquiv hL B base β hβ hM9).symm x))

end WaveTurbulence.VineEstS5A
