/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyAtomSlots
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyShape
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLClockReindex
public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9ClockSlots
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalFactors
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLRegionalPhaseSlots
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyAtomSlots
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLClockReindex
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLRegionalPhaseSlots` (sha256 d175e7bcf87d3619…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The regional phase as one exponential indexed by the M9 atom slots -/

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

/-- The M9 slot of an interior atom: block, then slot in the ingredient chart. -/
noncomputable def assemblySlotAtomEquivΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) :
    (Σ i : Fin n, Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n) ≃ ↥(U.erase a) :=
  (assemblyInputEquivΓ hM9 B).symm.trans (assemblyAtomEquivΓ hM9 B)

theorem assemblySlotAtom_valΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (z : Σ i : Fin n, Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n) :
    (assemblySlotAtomEquivΓ hM9 B z).1 = ((assemblyChartAtΓ hM9 B z.1).indexing.atom z.2).1 :=
  assemblyAtomEquiv_inputΓ hM9 B z.1 z.2

theorem assemblyTime_symm_inputΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (z : Σ i : Fin n, Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n) :
    (assemblyTimeEquivΓ hM9 B).symm ((assemblyInputEquivΓ hM9 B).symm z) =
      (familyTimeEquiv (fun i => (assemblyPieceAtΓ B i).label)
        (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape)).symm z := by
  exact congrArg (Sumint.timeVectorEquiv _).symm
    (congrArg (Equiv.sigmaCongrRight (familySlotEquiv (fun i => (assemblyPieceAtΓ B i).label)
      (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape))) ((assemblyInputEquivΓ hM9 B).apply_symm_apply z))

theorem assemblyClock_slotΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (z : Σ i : Fin n, Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n) :
    (assemblyClockAtomEquivΓ hM9 B).symm (assemblySlotAtomEquivΓ hM9 B z) =
      (familyTimeEquiv (fun i => (assemblyPieceAtΓ B i).label)
        (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape)).symm z := by
  show (assemblyTimeEquivΓ hM9 B).symm ((assemblyAtomEquivΓ hM9 B).symm
    (assemblyAtomEquivΓ hM9 B ((assemblyInputEquivΓ hM9 B).symm z))) = _
  rw [Equiv.symm_apply_apply]
  exact assemblyTime_symm_inputΓ hM9 B z

theorem clRegionalPhase_eq_exp_slotsΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (L γ δ : ℝ) (K : GNode G.tree → Mom d) (t : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) :
    clRegionalPhase G U L γ δ K
        (fun v => clLocalClock R t (assemblyClockEquivΓ hM9 B τ) v - t 0) =
      Complex.exp ((∑ z : Σ i : Fin n, Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n,
        Real.pi * δ * L ^ (2*γ) *
          ((((G.sign ((assemblyChartAtΓ hM9 B z.1).indexing.atom z.2).1.toNode : ℤ) : ℝ)) *
            omegaNode G K ((assemblyChartAtΓ hM9 B z.1).indexing.atom z.2).1) *
          (familyClock (fun i => (assemblyPieceAtΓ B i).label)
            (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape) τ z - t 0) : ℝ) * Complex.I) := by
  classical
  have ha : a ∈ U := (B.isBlock).2.1
  unfold clRegionalPhase
  rw [← Finset.mul_prod_erase U _ ha]
  have h1 : phaseAtom L γ δ (G.sign a.toNode) (omegaNode G K a)
      (clLocalClock R t (assemblyClockEquivΓ hM9 B τ) a - t 0) = 1 := by
    rw [clLocalClock_upper, sub_self]
    unfold phaseAtom
    simp
  rw [h1, one_mul, ← Finset.prod_coe_sort, ← Equiv.prod_comp (assemblySlotAtomEquivΓ hM9 B)]
  rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro z _
  rw [phaseAtom_eq_exp, assemblySlotAtom_valΓ]
  congr 2
  have hc := assemblyClock_internalΓ hM9 B t τ (assemblySlotAtomEquivΓ hM9 B z)
  rw [assemblySlotAtom_valΓ] at hc
  beta_reduce
  rw [hc, assemblyClock_slotΓ]
  rfl

end WaveTurbulence.GammaLow.Famb.VineEstS2
