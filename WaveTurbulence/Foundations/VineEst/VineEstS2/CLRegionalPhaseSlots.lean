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

/-! # The regional phase as one exponential indexed by the M9 atom slots -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The M9 slot of an interior atom: block, then slot in the ingredient chart. -/
noncomputable def assemblySlotAtomEquiv (hM9 : VINEPARAM) (B : CLChainAssembly G R n) :
    (Σ i : Fin n, Fin (assemblyChartAt hM9 B i).indexing.shape.n) ≃ ↥(U.erase a) :=
  (assemblyInputEquiv hM9 B).symm.trans (assemblyAtomEquiv hM9 B)

theorem assemblySlotAtom_val (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (z : Σ i : Fin n, Fin (assemblyChartAt hM9 B i).indexing.shape.n) :
    (assemblySlotAtomEquiv hM9 B z).1 = ((assemblyChartAt hM9 B z.1).indexing.atom z.2).1 :=
  assemblyAtomEquiv_input hM9 B z.1 z.2

theorem assemblyTime_symm_input (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (z : Σ i : Fin n, Fin (assemblyChartAt hM9 B i).indexing.shape.n) :
    (assemblyTimeEquiv hM9 B).symm ((assemblyInputEquiv hM9 B).symm z) =
      (familyTimeEquiv (fun i => (assemblyPieceAt B i).vineType)
        (fun i => (assemblyChartAt hM9 B i).indexing.shape)).symm z := by
  exact congrArg (Sumint.timeVectorEquiv _).symm
    (congrArg (Equiv.sigmaCongrRight (familySlotEquiv (fun i => (assemblyPieceAt B i).vineType)
      (fun i => (assemblyChartAt hM9 B i).indexing.shape))) ((assemblyInputEquiv hM9 B).apply_symm_apply z))

theorem assemblyClock_slot (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (z : Σ i : Fin n, Fin (assemblyChartAt hM9 B i).indexing.shape.n) :
    (assemblyClockAtomEquiv hM9 B).symm (assemblySlotAtomEquiv hM9 B z) =
      (familyTimeEquiv (fun i => (assemblyPieceAt B i).vineType)
        (fun i => (assemblyChartAt hM9 B i).indexing.shape)).symm z := by
  show (assemblyTimeEquiv hM9 B).symm ((assemblyAtomEquiv hM9 B).symm
    (assemblyAtomEquiv hM9 B ((assemblyInputEquiv hM9 B).symm z))) = _
  rw [Equiv.symm_apply_apply]
  exact assemblyTime_symm_input hM9 B z

theorem phaseAtom_eq_exp (L γ δ : ℝ) (ζ : ℤˣ) (Ω t : ℝ) :
    phaseAtom L γ δ ζ Ω t =
      Complex.exp ((Real.pi * δ * L ^ (2*γ) * (((ζ : ℤ) : ℝ) * Ω) * t : ℝ) * Complex.I) := by
  have h : Real.pi * ((ζ : ℤ) : ℝ) * δ * L ^ (2*γ) * Ω * t =
      Real.pi * δ * L ^ (2*γ) * (((ζ : ℤ) : ℝ) * Ω) * t := by ring
  unfold phaseAtom
  rw [h]

theorem clRegionalPhase_eq_exp_slots (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (L γ δ : ℝ) (K : GNode G.tree → Mom d) (t : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ) :
    clRegionalPhase G U L γ δ K
        (fun v => clLocalClock R t (assemblyClockEquiv hM9 B τ) v - t 0) =
      Complex.exp ((∑ z : Σ i : Fin n, Fin (assemblyChartAt hM9 B i).indexing.shape.n,
        Real.pi * δ * L ^ (2*γ) *
          ((((G.sign ((assemblyChartAt hM9 B z.1).indexing.atom z.2).1.toNode : ℤ) : ℝ)) *
            omegaNode G K ((assemblyChartAt hM9 B z.1).indexing.atom z.2).1) *
          (familyClock (fun i => (assemblyPieceAt B i).vineType)
            (fun i => (assemblyChartAt hM9 B i).indexing.shape) τ z - t 0) : ℝ) * Complex.I) := by
  classical
  have ha : a ∈ U := (B.isBlock).2.1
  unfold clRegionalPhase
  rw [← Finset.mul_prod_erase U _ ha]
  have h1 : phaseAtom L γ δ (G.sign a.toNode) (omegaNode G K a)
      (clLocalClock R t (assemblyClockEquiv hM9 B τ) a - t 0) = 1 := by
    rw [clLocalClock_upper, sub_self]
    unfold phaseAtom
    simp
  rw [h1, one_mul, ← Finset.prod_coe_sort, ← Equiv.prod_comp (assemblySlotAtomEquiv hM9 B)]
  rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro z _
  rw [phaseAtom_eq_exp, assemblySlotAtom_val]
  congr 2
  have hc := assemblyClock_internal hM9 B t τ (assemblySlotAtomEquiv hM9 B z)
  rw [assemblySlotAtom_val] at hc
  beta_reduce
  rw [hc, assemblyClock_slot]
  rfl


end WaveTurbulence.VineEstS2
