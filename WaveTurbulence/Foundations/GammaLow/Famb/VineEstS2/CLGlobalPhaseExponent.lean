/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblySlotResonance
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLinearSumintDatum
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintAlgebraicHypotheses
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SignedPhaseExp
public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9WeightedPhases
public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9SlotSums
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SumintJointFlip
public import WaveTurbulence.Foundations.VineEst.VineEstS2.GapPhaseNormalization
public import WaveTurbulence.Foundations.VineEst.VineEstS2.BlockPhaseAlgebra
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLGlobalPhaseExponent
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblySlotResonance
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintAlgebraicHypotheses
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLGlobalPhaseExponent` (sha256 71a1f07072b39a6b…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The summed source phase exponent equals the frozen signed phase exponent -/

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
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)

/-- The source clock pulled back to the M9 atom slots of the assembly. -/
noncomputable abbrev asmFCΓ (τ : (assemblyShapeΓ hM9 B).TVar → ℝ)
    (z : Σ i : Fin n, Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n) : ℝ :=
  familyClock (fun i => (assemblyPieceAtΓ B i).label)
    (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape) τ z

theorem assemblyVector_inputΓ
    (i : Fin n) (j : Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n) :
    assemblyVectorEquivΓ hM9 B ((assemblyInputEquivΓ hM9 B).symm ⟨i,j⟩) =
      ⟨i, familySlotEquiv (fun i => (assemblyPieceAtΓ B i).label)
        (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape) i j⟩ := by
  exact congrArg (Equiv.sigmaCongrRight (familySlotEquiv (fun i => (assemblyPieceAtΓ B i).label)
    (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape))) ((assemblyInputEquivΓ hM9 B).apply_symm_apply ⟨i,j⟩)

/-- Algebraic core of the global phase identity: if the slot resonances `N` satisfy the
weighted ingredient identities in the unflipped chart coordinates `xx`, then the slot sum is
the frozen signed phase exponent at `δ' = 2δ` and gap `-rc`. -/
theorem assembly_slots_exponentΓ (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) {L : ℝ} (γ δ : ℝ)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    (τ : (sourceSumintDatumΓ hM9 B hG W).S.TVar → ℝ) (rc : Mom d)
    (N : ∀ i : Fin n, Fin ((assemblyChartAtΓ hM9 B) i).indexing.shape.n → ℝ)
    (xx : ∀ i : Fin n, Fin ((assemblyChartAtΓ hM9 B) i).indexing.shape.n → Mom d)
    (hx0 : ∀ i, xx i ((assemblyChartAtΓ hM9 B) i).indexing.shape.x0 = -latticePoint L (x ((sourceSumintDatumΓ hM9 B hG W).S.x0Slot i)))
    (hxj : ∀ i (j : Fin ((assemblyChartAtΓ hM9 B) i).indexing.shape.m),
      xx i (((assemblyChartAtΓ hM9 B) i).indexing.shape.xSlot j) = latticePoint L (x ((sourceSumintDatumΓ hM9 B hG W).S.xSlot i j)))
    (hyj : ∀ i (j : Fin ((assemblyChartAtΓ hM9 B) i).indexing.shape.m),
      xx i (((assemblyChartAtΓ hM9 B) i).indexing.shape.ySlot j) = latticePoint L (x ((sourceSumintDatumΓ hM9 B hG W).S.ySlot i j)))
    (hxu : ∀ (k : {i : Fin (sourceSumintDatumΓ hM9 B hG W).S.I // (sourceSumintDatumΓ hM9 B hG W).S.nor i = true}) (c : Fin 3),
      xx k.1 (((assemblyChartAtΓ hM9 B) k.1).indexing.shape.uSlot ((shapeFamily_normal_iff _ _ k.1).mp k.2) c) =
        latticePoint L (x ((sourceSumintDatumΓ hM9 B hG W).S.uSlot k.1 k.2 c)))
    (hJ : ∀ i, (Real.pi * δ * L ^ (2*γ)) * N i ((assemblyChartAtΓ hM9 B) i).indexing.shape.x0 * (asmFCΓ hM9 B τ ⟨i, ((assemblyChartAtΓ hM9 B) i).indexing.shape.x0⟩ - t 0) =
          (Real.pi * δ * L ^ (2*γ)) * (2 * ((τ (.inl ⟨i,0⟩) - t 0) * inner ℝ rc (xx i ((assemblyChartAtΓ hM9 B) i).indexing.shape.x0))))
    (hR : ∀ i (j : Fin ((assemblyChartAtΓ hM9 B) i).indexing.shape.m),
      (Real.pi * δ * L ^ (2*γ)) * N i (((assemblyChartAtΓ hM9 B) i).indexing.shape.xSlot j) * (asmFCΓ hM9 B τ ⟨i, ((assemblyChartAtΓ hM9 B) i).indexing.shape.xSlot j⟩ - t 0) +
        (Real.pi * δ * L ^ (2*γ)) * N i (((assemblyChartAtΓ hM9 B) i).indexing.shape.ySlot j) * (asmFCΓ hM9 B τ ⟨i, ((assemblyChartAtΓ hM9 B) i).indexing.shape.ySlot j⟩ - t 0) =
      (Real.pi * δ * L ^ (2*γ)) * (2 * ((τ (.inl ⟨i,j.succ⟩) - τ (.inr (.inl ⟨i,j⟩))) *
          inner ℝ (xx i (((assemblyChartAtΓ hM9 B) i).indexing.shape.xSlot j)) (xx i (((assemblyChartAtΓ hM9 B) i).indexing.shape.ySlot j)) +
        (τ (.inl ⟨i,j.succ⟩) - t 0) * inner ℝ rc
          ((((assemblyChartAtΓ hM9 B) i).ζc j 0 : ℝ) • xx i (((assemblyChartAtΓ hM9 B) i).indexing.shape.xSlot j) +
            (((assemblyChartAtΓ hM9 B) i).ζc j 1 : ℝ) • xx i (((assemblyChartAtΓ hM9 B) i).indexing.shape.ySlot j) +
            (((assemblyChartAtΓ hM9 B) i).ζc j 2 : ℝ) • rc))))
    (hC : ∀ k : {i : Fin (sourceSumintDatumΓ hM9 B hG W).S.I // (sourceSumintDatumΓ hM9 B hG W).S.nor i = true},
      (∑ c' : Fin 3, (Real.pi * δ * L ^ (2*γ)) *
        N k.1 (((assemblyChartAtΓ hM9 B) k.1).indexing.shape.uSlot ((shapeFamily_normal_iff _ _ k.1).mp k.2) c') *
          (asmFCΓ hM9 B τ ⟨k.1, ((assemblyChartAtΓ hM9 B) k.1).indexing.shape.uSlot ((shapeFamily_normal_iff _ _ k.1).mp k.2) c'⟩ - t 0)) =
      (Real.pi * δ * L ^ (2*γ)) * (2 *
        ((τ (.inr (.inr ⟨k,0⟩)) - τ (.inr (.inr ⟨k,2⟩))) * (((assemblyCoreFirstSignΓ hM9 B k.1 : ℤ) : ℝ) *
            inner ℝ (xx k.1 (((assemblyChartAtΓ hM9 B) k.1).indexing.shape.uSlot ((shapeFamily_normal_iff _ _ k.1).mp k.2) 0))
              (xx k.1 (((assemblyChartAtΓ hM9 B) k.1).indexing.shape.uSlot ((shapeFamily_normal_iff _ _ k.1).mp k.2) 1))) +
          (τ (.inr (.inr ⟨k,1⟩)) - τ (.inr (.inr ⟨k,2⟩))) * (((assemblyCoreFirstSignΓ hM9 B k.1 : ℤ) : ℝ) *
            (if ((assemblyChartAtΓ hM9 B) k.1).coreLinear then
              inner ℝ (xx k.1 (((assemblyChartAtΓ hM9 B) k.1).indexing.shape.uSlot ((shapeFamily_normal_iff _ _ k.1).mp k.2) 0))
                (xx k.1 (((assemblyChartAtΓ hM9 B) k.1).indexing.shape.uSlot ((shapeFamily_normal_iff _ _ k.1).mp k.2) 2))
            else ((assemblyCoreSignΓ hM9 B k.1 : ℤ) : ℝ) *
              inner ℝ (xx k.1 (((assemblyChartAtΓ hM9 B) k.1).indexing.shape.uSlot ((shapeFamily_normal_iff _ _ k.1).mp k.2) 2))
                (xx k.1 (((assemblyChartAtΓ hM9 B) k.1).indexing.shape.uSlot ((shapeFamily_normal_iff _ _ k.1).mp k.2) 0) +
                  xx k.1 (((assemblyChartAtΓ hM9 B) k.1).indexing.shape.uSlot ((shapeFamily_normal_iff _ _ k.1).mp k.2) 1) -
                  xx k.1 (((assemblyChartAtΓ hM9 B) k.1).indexing.shape.uSlot ((shapeFamily_normal_iff _ _ k.1).mp k.2) 2)))) +
          (τ (.inr (.inr ⟨k,2⟩)) - t 0) * inner ℝ rc
            (((((assemblyChartAtΓ hM9 B) k.1).ξc 0 : ℤ) : ℝ) •
                xx k.1 (((assemblyChartAtΓ hM9 B) k.1).indexing.shape.uSlot ((shapeFamily_normal_iff _ _ k.1).mp k.2) 0) +
              ((((assemblyChartAtΓ hM9 B) k.1).ξc 1 : ℤ) : ℝ) •
                xx k.1 (((assemblyChartAtΓ hM9 B) k.1).indexing.shape.uSlot ((shapeFamily_normal_iff _ _ k.1).mp k.2) 1) +
              ((((assemblyChartAtΓ hM9 B) k.1).ξc 2 : ℤ) : ℝ) •
                xx k.1 (((assemblyChartAtΓ hM9 B) k.1).indexing.shape.uSlot ((shapeFamily_normal_iff _ _ k.1).mp k.2) 2) +
              ((((assemblyChartAtΓ hM9 B) k.1).ξc 3 : ℤ) : ℝ) • rc)))) :
    (∑ z : Σ i : Fin n, Fin ((assemblyChartAtΓ hM9 B) i).indexing.shape.n, (Real.pi * δ * L ^ (2*γ)) * N z.1 z.2 * (asmFCΓ hM9 B τ z - t 0)) =
    Real.pi * signedPhaseExponent (sourceSumintDatumΓ hM9 B hG W)
      (assemblyCoreFirstSignΓ hM9 B) (assemblyCoreSignΓ hM9 B) L γ (2*δ) x (-rc) (t 0) τ := by
  rw [sum_familySlots (fun i => (assemblyPieceAtΓ B i).label)
    (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape)]
  unfold signedPhaseExponent
  rw [mul_add]
  congr 1
  · refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) (Finset.mul_sum Finset.univ _ Real.pi).symm
    dsimp only
    refine (congrArg₂ (· + ·) (hJ i) (Finset.sum_congr rfl (fun j _ => hR i j))).trans ?_
    have hA : inner ℝ rc (xx i (assemblyChartAtΓ hM9 B i).indexing.shape.x0) =
        inner ℝ (-rc) (latticePoint L (x ((sourceSumintDatumΓ hM9 B hG W).S.x0Slot i))) := by
      rw [hx0 i]
      simp only [inner_neg_left, inner_neg_right]
    have hZ : ∀ j : Fin (assemblyChartAtΓ hM9 B i).indexing.shape.m,
        inner ℝ rc ((((assemblyChartAtΓ hM9 B i).ζc j 0 : ℤ) : ℝ) •
            latticePoint L (x ((sourceSumintDatumΓ hM9 B hG W).S.xSlot i j)) +
          (((assemblyChartAtΓ hM9 B i).ζc j 1 : ℤ) : ℝ) •
            latticePoint L (x ((sourceSumintDatumΓ hM9 B hG W).S.ySlot i j)) +
          (((assemblyChartAtΓ hM9 B i).ζc j 2 : ℤ) : ℝ) • rc) =
        inner ℝ (-rc) ((((sourceSumintDatumΓ hM9 B hG W).ζc i j 0 : ℤ) : ℝ) •
            latticePoint L (x ((sourceSumintDatumΓ hM9 B hG W).S.xSlot i j)) +
          (((sourceSumintDatumΓ hM9 B hG W).ζc i j 1 : ℤ) : ℝ) •
            latticePoint L (x ((sourceSumintDatumΓ hM9 B hG W).S.ySlot i j)) +
          (((sourceSumintDatumΓ hM9 B hG W).ζc i j 2 : ℤ) : ℝ) • (-rc)) := by
      intro j
      have h0 : (sourceSumintDatumΓ hM9 B hG W).ζc i j 0 = -((assemblyChartAtΓ hM9 B i).ζc j 0) := by
        simp [sourceSumintDatumΓ, assemblyZetaΓ]
      have h1 : (sourceSumintDatumΓ hM9 B hG W).ζc i j 1 = -((assemblyChartAtΓ hM9 B i).ζc j 1) := by
        simp [sourceSumintDatumΓ, assemblyZetaΓ]
      have h2 : (sourceSumintDatumΓ hM9 B hG W).ζc i j 2 = ((assemblyChartAtΓ hM9 B i).ζc j 2) := by
        simp [sourceSumintDatumΓ, assemblyZetaΓ]
      rw [h0, h1, h2, inner_flip_two]
    simp only [hxj, hyj, hA, hZ]
    rw [mul_add Real.pi, mul_add Real.pi, Finset.mul_sum Finset.univ _ Real.pi,
      Finset.mul_sum Finset.univ _ Real.pi, add_right_comm _ (Real.pi * _), ← Finset.sum_add_distrib,
      add_comm]
    congr 1
    · exact Finset.sum_congr rfl (fun j _ => by ring!)
    · ring
  · rw [Finset.mul_sum]
    refine sum_univ_congr_inst (α := {i : Fin (sourceSumintDatumΓ hM9 B hG W).S.I //
      (sourceSumintDatumΓ hM9 B hG W).S.nor i = true}) _ _ _ _ (fun k => ?_)
    refine (hC k).trans ?_
    dsimp only
    have hX : inner ℝ rc ((((assemblyChartAtΓ hM9 B k.1).ξc 0 : ℤ) : ℝ) •
          latticePoint L (x ((sourceSumintDatumΓ hM9 B hG W).S.uSlot k.1 k.2 0)) +
        (((assemblyChartAtΓ hM9 B k.1).ξc 1 : ℤ) : ℝ) •
          latticePoint L (x ((sourceSumintDatumΓ hM9 B hG W).S.uSlot k.1 k.2 1)) +
        (((assemblyChartAtΓ hM9 B k.1).ξc 2 : ℤ) : ℝ) •
          latticePoint L (x ((sourceSumintDatumΓ hM9 B hG W).S.uSlot k.1 k.2 2)) +
        (((assemblyChartAtΓ hM9 B k.1).ξc 3 : ℤ) : ℝ) • rc) =
      inner ℝ (-rc) ((((sourceSumintDatumΓ hM9 B hG W).ξc k.1 0 : ℤ) : ℝ) •
          latticePoint L (x ((sourceSumintDatumΓ hM9 B hG W).S.uSlot k.1 k.2 0)) +
        (((sourceSumintDatumΓ hM9 B hG W).ξc k.1 1 : ℤ) : ℝ) •
          latticePoint L (x ((sourceSumintDatumΓ hM9 B hG W).S.uSlot k.1 k.2 1)) +
        (((sourceSumintDatumΓ hM9 B hG W).ξc k.1 2 : ℤ) : ℝ) •
          latticePoint L (x ((sourceSumintDatumΓ hM9 B hG W).S.uSlot k.1 k.2 2)) +
        (((sourceSumintDatumΓ hM9 B hG W).ξc k.1 3 : ℤ) : ℝ) • (-rc)) := by
      have h0 : (sourceSumintDatumΓ hM9 B hG W).ξc k.1 0 = -((assemblyChartAtΓ hM9 B k.1).ξc 0) := by
        simp [sourceSumintDatumΓ, assemblyXiΓ] <;> rfl
      have h1 : (sourceSumintDatumΓ hM9 B hG W).ξc k.1 1 = -((assemblyChartAtΓ hM9 B k.1).ξc 1) := by
        simp [sourceSumintDatumΓ, assemblyXiΓ] <;> rfl
      have h2 : (sourceSumintDatumΓ hM9 B hG W).ξc k.1 2 = -((assemblyChartAtΓ hM9 B k.1).ξc 2) := by
        simp [sourceSumintDatumΓ, assemblyXiΓ] <;> rfl
      have h3 : (sourceSumintDatumΓ hM9 B hG W).ξc k.1 3 = ((assemblyChartAtΓ hM9 B k.1).ξc 3) := by
        simp [sourceSumintDatumΓ, assemblyXiΓ] <;> rfl
      rw [h0, h1, h2, h3, inner_flip_three]
    simp only [hxu, hX]
    ring!

end WaveTurbulence.GammaLow.Famb.VineEstS2
