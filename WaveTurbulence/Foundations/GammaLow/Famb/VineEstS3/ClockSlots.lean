/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Time
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockSlots
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Time
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.ClockSlots` (sha256 4755673b71d8a4d8…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # B4: parent clocks of realization nodes are slots (V5)

For a node `x` of the realization with `x ≠ a.toNode`, the parent clock
`parentClock (t 0) (clLocalClock R t (assemblyClockEquiv τ)) x` is either the top time `t 0` or the value
`τ s` of an internal time variable `s`; likewise the clock of an interior branch is `τ s`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 VineParamContract TTree Reg Reg.Skeleton RegRed WaveTurbulence.GammaLow.Famb.VineEstS2
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem node_parent_slotΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) :
    (∀ t τ, parentClock (t 0) (clLocalClock R t (assemblyClockEquivΓ hM9 B τ)) x = t 0) ∨
    ∃ s : (assemblyShapeΓ hM9 B).TVar, ∀ t τ,
      parentClock (t 0) (clLocalClock R t (assemblyClockEquivΓ hM9 B τ)) x = τ s := by
  classical
  obtain ⟨hn, hp⟩ := cl_realization_parent B.isBlock R x hx hne
  by_cases hpa : x.parent hn = a
  · left
    intro t τ
    rw [parentClock_nonroot _ _ x hn, hpa]
    exact clLocalClock_upper R t _
  · right
    have hmem : x.parent hn ∈ clInteriorBranches R := Finset.mem_erase.mpr ⟨hpa, hp⟩
    refine ⟨(assemblyClockAtomEquivΓ hM9 B).symm ⟨x.parent hn, hmem⟩, fun t τ => ?_⟩
    rw [parentClock_nonroot _ _ x hn]
    have := clLocalClock_slotΓ hM9 B t τ ((assemblyClockAtomEquivΓ hM9 B).symm ⟨x.parent hn, hmem⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this

theorem branch_clock_slotΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (v : ↥(clInteriorBranches R)) :
    ∃ s : (assemblyShapeΓ hM9 B).TVar, ∀ t τ,
      clLocalClock R t (assemblyClockEquivΓ hM9 B τ) v.1 = τ s := by
  refine ⟨(assemblyClockAtomEquivΓ hM9 B).symm v, fun t τ => ?_⟩
  have := clLocalClock_slotΓ hM9 B t τ ((assemblyClockAtomEquivΓ hM9 B).symm v)
  have h := congrArg Subtype.val (Equiv.apply_symm_apply (assemblyClockAtomEquivΓ hM9 B) v)
  rw [h] at this
  exact this

end WaveTurbulence.GammaLow.Famb.VineEstS3
