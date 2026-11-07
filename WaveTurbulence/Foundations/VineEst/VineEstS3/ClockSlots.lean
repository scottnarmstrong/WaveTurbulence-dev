/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Time

/-! # B4: parent clocks of realization nodes are slots (V5)

For a node `x` of the realization with `x ≠ a.toNode`, the parent clock
`parentClock (t 0) (clLocalClock R t (assemblyClockEquiv τ)) x` is either the top time `t 0` or the value
`τ s` of an internal time variable `s`; likewise the clock of an interior branch is `τ s`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 VineParamContract TTree Reg Reg.Skeleton RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem node_parent_slot (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) :
    (∀ t τ, parentClock (t 0) (clLocalClock R t (assemblyClockEquiv hM9 B τ)) x = t 0) ∨
    ∃ s : (assemblyShape hM9 B).TVar, ∀ t τ,
      parentClock (t 0) (clLocalClock R t (assemblyClockEquiv hM9 B τ)) x = τ s := by
  classical
  obtain ⟨hn, hp⟩ := cl_realization_parent B.isBlock R x hx hne
  by_cases hpa : x.parent hn = a
  · left
    intro t τ
    rw [parentClock_nonroot _ _ x hn, hpa]
    exact clLocalClock_upper R t _
  · right
    have hmem : x.parent hn ∈ clInteriorBranches R := Finset.mem_erase.mpr ⟨hpa, hp⟩
    refine ⟨(assemblyClockAtomEquiv hM9 B).symm ⟨x.parent hn, hmem⟩, fun t τ => ?_⟩
    rw [parentClock_nonroot _ _ x hn]
    have := clLocalClock_slot hM9 B t τ ((assemblyClockAtomEquiv hM9 B).symm ⟨x.parent hn, hmem⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this

theorem branch_clock_slot (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (v : ↥(clInteriorBranches R)) :
    ∃ s : (assemblyShape hM9 B).TVar, ∀ t τ,
      clLocalClock R t (assemblyClockEquiv hM9 B τ) v.1 = τ s := by
  refine ⟨(assemblyClockAtomEquiv hM9 B).symm v, fun t τ => ?_⟩
  have := clLocalClock_slot hM9 B t τ ((assemblyClockAtomEquiv hM9 B).symm v)
  have h := congrArg Subtype.val (Equiv.apply_symm_apply (assemblyClockAtomEquiv hM9 B) v)
  rw [h] at this
  exact this

end WaveTurbulence.VineEstS3
