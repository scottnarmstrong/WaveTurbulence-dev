/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyAtoms
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalKernelRecentering
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLClockReindex
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyAtoms
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLClockReindex` (sha256 a4781e9443d04596…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Measure-preserving clock change from actual source branches to sumint slots -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed MeasureTheory
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def assemblyClockEquivΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) :
    ((assemblyShapeΓ hM9 B).TVar → ℝ) ≃ᵐ CLInternalTime R :=
  MeasurableEquiv.piCongrLeft (fun _ : ↥(clInteriorBranches R) => ℝ) (assemblyClockAtomEquivΓ hM9 B)

theorem assemblyClock_measurePreservingΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) :
    MeasurePreserving (assemblyClockEquivΓ hM9 B) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : ↥(clInteriorBranches R) => ℝ) (assemblyClockAtomEquivΓ hM9 B)

/-- A finite coordinate permutation changes no Lebesgue measure. This
identity holds for every Bochner integrand, with no Fubini premise. -/
theorem assemblyClock_integralΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (F : CLInternalTime R → ℂ) :
    (∫ τ, F τ) = ∫ τ, F (assemblyClockEquivΓ hM9 B τ) :=
  ((assemblyClock_measurePreservingΓ hM9 B).integral_comp' F).symm

theorem assemblyClock_internalΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (t : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) (v : ↥(clInteriorBranches R)) :
    clLocalClock R t (assemblyClockEquivΓ hM9 B τ) v.1 = τ ((assemblyClockAtomEquivΓ hM9 B).symm v) :=
  (clLocalClock_internal R t (assemblyClockEquivΓ hM9 B τ) v).trans
    (by
      have he := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ↥(clInteriorBranches R) => ℝ) (assemblyClockAtomEquivΓ hM9 B) τ
        ((assemblyClockAtomEquivΓ hM9 B).symm v)
      exact (congrArg (fun z : ↥(clInteriorBranches R) => assemblyClockEquivΓ hM9 B τ z)
        ((assemblyClockAtomEquivΓ hM9 B).apply_symm_apply v)).symm.trans he)

end WaveTurbulence.GammaLow.Famb.VineEstS2
