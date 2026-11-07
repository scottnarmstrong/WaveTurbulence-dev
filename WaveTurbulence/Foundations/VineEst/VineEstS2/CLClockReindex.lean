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

/-! # Measure-preserving clock change from actual source branches to sumint slots -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed MeasureTheory
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def assemblyClockEquiv (hM9 : VINEPARAM) (B : CLChainAssembly G R n) :
    ((assemblyShape hM9 B).TVar → ℝ) ≃ᵐ CLInternalTime R :=
  MeasurableEquiv.piCongrLeft (fun _ : ↥(clInteriorBranches R) => ℝ) (assemblyClockAtomEquiv hM9 B)

theorem assemblyClock_measurePreserving (hM9 : VINEPARAM) (B : CLChainAssembly G R n) :
    MeasurePreserving (assemblyClockEquiv hM9 B) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : ↥(clInteriorBranches R) => ℝ) (assemblyClockAtomEquiv hM9 B)

/-- A finite coordinate permutation changes no Lebesgue measure. This
identity holds for every Bochner integrand, with no Fubini premise. -/
theorem assemblyClock_integral (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (F : CLInternalTime R → ℂ) :
    (∫ τ, F τ) = ∫ τ, F (assemblyClockEquiv hM9 B τ) :=
  ((assemblyClock_measurePreserving hM9 B).integral_comp' F).symm

theorem assemblyClock_internal (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (t : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ) (v : ↥(clInteriorBranches R)) :
    clLocalClock R t (assemblyClockEquiv hM9 B τ) v.1 = τ ((assemblyClockAtomEquiv hM9 B).symm v) :=
  (clLocalClock_internal R t (assemblyClockEquiv hM9 B τ) v).trans
    (by
      have he := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ↥(clInteriorBranches R) => ℝ) (assemblyClockAtomEquiv hM9 B) τ
        ((assemblyClockAtomEquiv hM9 B).symm v)
      exact (congrArg (fun z : ↥(clInteriorBranches R) => assemblyClockEquiv hM9 B τ z)
        ((assemblyClockAtomEquiv hM9 B).apply_symm_apply v)).symm.trans he)

end WaveTurbulence.VineEstS2
