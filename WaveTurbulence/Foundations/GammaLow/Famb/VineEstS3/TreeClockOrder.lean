/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.AssemblyClocked
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ConstraintsOK
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.TreeClockOrder
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.AssemblyClocked
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.AssemblyClockedS1
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.ConstraintsOK
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.TreeClockOrder` (sha256 72d50b43e4b4ad9b…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Step 3: the clocks of a tree row are ordered (`child < parent`) on the `sumint` time domain, and `ζ` is unimodular -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng VineParamContract TTree Reg Reg.Skeleton RegRed WaveTurbulence.GammaLow.Famb.VineEstS2
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- On the `sumint` time domain with the source windows/constraints, the clock of an interior branch lies below
its parent clock. -/
theorem clock_lt_parentClockΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (hok : ConstraintsOKΓ hM9 B W)
    (tt : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ)
    (hτ : τ ∈ (sourceSumintDatumΓ hM9 B hG W).timeDom (assemblyShape_I_posΓ hM9 B) (tt 0) (tt 1) (tt 2))
    (z : ↥(clInteriorBranches R)) :
    clLocalClock R tt (assemblyClockEquivΓ hM9 B τ) z.1 <
      parentClock (tt 0) (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ)) z.1.toNode := by
  set s0 := (assemblyClockAtomEquivΓ hM9 B).symm z with hs0
  have hz : (assemblyClockAtomEquivΓ hM9 B s0).1 = z.1 :=
    congrArg Subtype.val (Equiv.apply_symm_apply (assemblyClockAtomEquivΓ hM9 B) z)
  have hclock : clLocalClock R tt (assemblyClockEquivΓ hM9 B τ) z.1 = τ s0 := by
    rw [← hz]; exact clLocalClock_slotΓ hM9 B tt τ s0
  obtain ⟨hτ1, _, hτ3⟩ := hτ
  have hlt0 := (hτ1 s0).2.2
  rw [hclock]
  have hsp := slot_parent_clockΓ hM9 B tt τ s0
  rw [hz] at hsp
  rcases hsp with ⟨h1, _⟩ | ⟨s', hs', h2⟩
  · rw [h1]; exact hlt0
  · rw [h2]
    have := hτ3 (s0, s') (show (s0, s') ∈ W.constraints from hok.1 hs')
    exact this

end WaveTurbulence.GammaLow.Famb.VineEstS3
