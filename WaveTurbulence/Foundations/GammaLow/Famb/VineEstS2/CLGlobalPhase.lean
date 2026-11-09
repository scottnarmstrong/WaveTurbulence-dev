/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLGlobalPhaseExponent
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLKernelReindex
public import WaveTurbulence.Foundations.VineEst.VineEstS2.BlockPhaseAlgebra
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLGlobalPhase
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLGlobalPhaseExponent
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLGlobalPhase` (sha256 4a53a128c8d13788…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # TARGET Step 2: the regional phase is the frozen signed sumint phase

For every lattice point `x` of the frozen sumint vector lattice and every sumint clock
`τ`, the literal regional source phase of the corresponding regional decoration and the
reindexed clocks equals `signedPhase` of the source sumint datum, at `δ' = 2δ`, with the
common gap `-(β₂-β₃)` and vanishing weight parameters. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem assembly_phase_exponentΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d)
    {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (γ δ : ℝ) (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    (τ : (sourceSumintDatumΓ hM9 B hG W).S.TVar → ℝ) :
    (∑ z : Σ i : Fin n, Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n,
      Real.pi * δ * L ^ (2*γ) *
        ((((G.sign ((assemblyChartAtΓ hM9 B z.1).indexing.atom z.2).1.toNode : ℤ) : ℝ)) *
          omegaNode G (clChainMomentumΓ hL B base β hβ hM9 (jointFlip _ x))
            ((assemblyChartAtΓ hM9 B z.1).indexing.atom z.2).1) *
        (asmFCΓ hM9 B τ z - t 0)) =
    Real.pi * signedPhaseExponent (sourceSumintDatumΓ hM9 B hG W)
      (assemblyCoreFirstSignΓ hM9 B) (assemblyCoreSignΓ hM9 B) L γ (2*δ) x
      (-(latticePoint L (β 2-β 3))) (t 0) τ := by
  obtain ⟨gA, hgA⟩ := assembly_slot_resonanceΓ hL B base β hβ hM9 (jointFlip _ x)
  rw [Finset.sum_congr rfl (fun z _ => by rw [hgA z])]
  refine assembly_slots_exponentΓ hM9 B hG W γ δ x t τ (latticePoint L (β 2-β 3))
    (fun i j => nodeResonance (assemblyChartAtΓ hM9 B i).indexing
      (((assemblyChartAtΓ hM9 B i).chart (gA i) (latticePoint L (β 2-β 3))).symm
        (fun j => latticePoint L (jointFlip _ x (assemblyVectorEquivΓ hM9 B
          ((assemblyInputEquivΓ hM9 B).symm ⟨i,j⟩))))).1 (gA i) (latticePoint L (β 2-β 3)) j)
    (fun i j => latticePoint L (jointFlip _ x (assemblyVectorEquivΓ hM9 B
          ((assemblyInputEquivΓ hM9 B).symm ⟨i,j⟩)))) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    show latticePoint L (jointFlip _ x (assemblyVectorEquivΓ hM9 B ((assemblyInputEquivΓ hM9 B).symm
      ⟨i,(assemblyChartAtΓ hM9 B i).indexing.shape.x0⟩))) = _
    rw [assemblyVector_inputΓ, familySlotEquiv_x0]
    exact (congrArg (latticePoint L) (jointFlip_x0 (assemblyShapeΓ hM9 B) x i)).trans
      (latticePoint_neg' L _)
  · intro i j
    show latticePoint L (jointFlip _ x (assemblyVectorEquivΓ hM9 B ((assemblyInputEquivΓ hM9 B).symm
      ⟨i,(assemblyChartAtΓ hM9 B i).indexing.shape.xSlot j⟩))) = _
    rw [assemblyVector_inputΓ, familySlotEquiv_x]
    exact congrArg (latticePoint L) (jointFlip_x (assemblyShapeΓ hM9 B) x i j)
  · intro i j
    show latticePoint L (jointFlip _ x (assemblyVectorEquivΓ hM9 B ((assemblyInputEquivΓ hM9 B).symm
      ⟨i,(assemblyChartAtΓ hM9 B i).indexing.shape.ySlot j⟩))) = _
    rw [assemblyVector_inputΓ, familySlotEquiv_y]
    exact congrArg (latticePoint L) (jointFlip_y (assemblyShapeΓ hM9 B) x i j)
  · intro k c
    have h1 := assemblyVector_inputΓ hM9 B k.1
      ((assemblyChartAtΓ hM9 B k.1).indexing.shape.uSlot ((shapeFamily_normal_iff _ _ k.1).mp k.2) c)
    have h2 := familySlotEquiv_u (fun i => (assemblyPieceAtΓ B i).label)
      (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape) k.1
      ((shapeFamily_normal_iff _ _ k.1).mp k.2) k.2 c
    exact (congrArg (fun v => latticePoint L (jointFlip _ x v)) h1).trans
      ((congrArg (fun q => latticePoint L (jointFlip _ x ⟨k.1, q⟩)) h2).trans
        (congrArg (latticePoint L) (jointFlip_u (assemblyShapeΓ hM9 B) x k.1 k.2 c)))
  · intro i
    have e : asmFCΓ hM9 B τ ⟨i, (assemblyChartAtΓ hM9 B i).indexing.shape.x0⟩ = τ (.inl ⟨i,0⟩) :=
      familyClock_x0 (fun i => (assemblyPieceAtΓ B i).label)
        (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape) τ i
    refine (block_joint_exponent (assemblyChartAtΓ hM9 B i) (gA i) (latticePoint L (β 2-β 3))
      (fun j => latticePoint L (jointFlip _ x (assemblyVectorEquivΓ hM9 B
          ((assemblyInputEquivΓ hM9 B).symm ⟨i,j⟩)))) (Real.pi * δ * L ^ (2*γ))
      (asmFCΓ hM9 B τ ⟨i, (assemblyChartAtΓ hM9 B i).indexing.shape.x0⟩) (t 0)).trans ?_
    rw [e]
  · intro i j
    have ex : asmFCΓ hM9 B τ ⟨i, (assemblyChartAtΓ hM9 B i).indexing.shape.xSlot j⟩ =
        τ (.inl ⟨i,j.succ⟩) :=
      familyClock_x (fun i => (assemblyPieceAtΓ B i).label)
        (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape) τ i j
    have ey : asmFCΓ hM9 B τ ⟨i, (assemblyChartAtΓ hM9 B i).indexing.shape.ySlot j⟩ =
        τ (.inr (.inl ⟨i,j⟩)) :=
      familyClock_y (fun i => (assemblyPieceAtΓ B i).label)
        (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape) τ i j
    refine (block_rung_exponent (assemblyChartAtΓ hM9 B i) (gA i) (latticePoint L (β 2-β 3))
      (fun j => latticePoint L (jointFlip _ x (assemblyVectorEquivΓ hM9 B
          ((assemblyInputEquivΓ hM9 B).symm ⟨i,j⟩)))) j (Real.pi * δ * L ^ (2*γ))
      (asmFCΓ hM9 B τ ⟨i, (assemblyChartAtΓ hM9 B i).indexing.shape.xSlot j⟩)
      (asmFCΓ hM9 B τ ⟨i, (assemblyChartAtΓ hM9 B i).indexing.shape.ySlot j⟩) (t 0)).trans ?_
    rw [ex, ey]
  · intro k
    have eu : ∀ c : Fin 3, asmFCΓ hM9 B τ ⟨k.1, (assemblyChartAtΓ hM9 B k.1).indexing.shape.uSlot
        ((shapeFamily_normal_iff _ _ k.1).mp k.2) c⟩ = τ (.inr (.inr ⟨k,c⟩)) :=
      fun c => familyClock_u (fun i => (assemblyPieceAtΓ B i).label)
        (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape) τ k c
    refine (block_core_exponent (assemblyChartAtΓ hM9 B k.1) ((shapeFamily_normal_iff _ _ k.1).mp k.2)
      (gA k.1) (latticePoint L (β 2-β 3))
      (fun j => latticePoint L (jointFlip _ x (assemblyVectorEquivΓ hM9 B
          ((assemblyInputEquivΓ hM9 B).symm ⟨k.1,j⟩))))
      (fun c => asmFCΓ hM9 B τ ⟨k.1, (assemblyChartAtΓ hM9 B k.1).indexing.shape.uSlot
        ((shapeFamily_normal_iff _ _ k.1).mp k.2) c⟩) (Real.pi * δ * L ^ (2*γ)) (t 0)).trans ?_
    simp only [eu]
    rfl

/-- TARGET vineest Step 2, phase part: the literal recentered regional source phase on the
reindexed chain coordinates is `signedPhase` of the source sumint datum (the weight parameters
vanish, no bad factor), at `δ' = 2δ` and the frozen gap `-(β₂-β₃)`. -/
theorem assembly_regionalPhase_eq_signedPhaseΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (γ δ η : ℝ) (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) :
    clRegionalPhase G U L γ δ
        (cosetDecoration G L base
          (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1))
        (fun v => clLocalClock R t (assemblyClockEquivΓ hM9 B τ) v - t 0) =
      signedPhase (sourceSumintDatumΓ hM9 B hG W) (assemblyCoreFirstSignΓ hM9 B)
        (assemblyCoreSignΓ hM9 B) L γ (2*δ) η x (-(latticePoint L (β 2-β 3))) (t 0) τ := by
  have hK : cosetDecoration G L base
      (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1) =
      clChainMomentumΓ hL B base β hβ hM9 (jointFlip _ x) := rfl
  rw [hK, clRegionalPhase_eq_exp_slotsΓ hM9 B L γ δ _ t τ,
    signedPhase_eq_exp (sourceSumintDatumΓ hM9 B hG W) (assemblyCoreFirstSignΓ hM9 B)
      (assemblyCoreSignΓ hM9 B) L γ (2*δ) η x _ (t 0) τ hpar hbad]
  exact congrArg (fun y : ℝ => Complex.exp ((y : ℂ) * Complex.I))
    (assembly_phase_exponentΓ hM9 B hG W hL base β hβ γ δ x t τ)

end WaveTurbulence.GammaLow.Famb.VineEstS2
