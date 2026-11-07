/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.AssemblyClocked
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ConstraintsOK

/-! # Step 3: the clocks of a tree row are ordered (`child < parent`) on the `sumint` time domain, and `ζ` is unimodular -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng VineParamContract TTree Reg Reg.Skeleton RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- On the `sumint` time domain with the source windows/constraints, the clock of an interior branch lies below
its parent clock. -/
theorem clock_lt_parentClock (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) (hok : ConstraintsOK hM9 B W)
    (tt : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ)
    (hτ : τ ∈ (sourceSumintDatum hM9 B hG W).timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2))
    (z : ↥(clInteriorBranches R)) :
    clLocalClock R tt (assemblyClockEquiv hM9 B τ) z.1 <
      parentClock (tt 0) (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) z.1.toNode := by
  set s0 := (assemblyClockAtomEquiv hM9 B).symm z with hs0
  have hz : (assemblyClockAtomEquiv hM9 B s0).1 = z.1 :=
    congrArg Subtype.val (Equiv.apply_symm_apply (assemblyClockAtomEquiv hM9 B) z)
  have hclock : clLocalClock R tt (assemblyClockEquiv hM9 B τ) z.1 = τ s0 := by
    rw [← hz]; exact clLocalClock_slot hM9 B tt τ s0
  obtain ⟨hτ1, _, hτ3⟩ := hτ
  have hlt0 := (hτ1 s0).2.2
  rw [hclock]
  have hsp := slot_parent_clock hM9 B tt τ s0
  rw [hz] at hsp
  rcases hsp with ⟨h1, _⟩ | ⟨s', hs', h2⟩
  · rw [h1]; exact hlt0
  · rw [h2]
    have := hτ3 (s0, s') (show (s0, s') ∈ W.constraints from hok.1 hs')
    exact this

/-- `‖ζ‖ = 1` for the local sign factor. -/
theorem norm_clLocalZeta (R : CLRegionData G U a b) : ‖clLocalZeta R‖ = 1 := by
  unfold clLocalZeta
  rw [norm_prod]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [norm_mul, Complex.norm_I, one_mul]
  rcases Int.units_eq_one_or (G.sign v.toNode) with h | h <;> simp [h]

end WaveTurbulence.VineEstS3
