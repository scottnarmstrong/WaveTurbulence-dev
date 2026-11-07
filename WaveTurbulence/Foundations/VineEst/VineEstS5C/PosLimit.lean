/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Step3FinalH

/-! # From positive to nonnegative leaf sizes (R45)

The engine needs `0 < Bh r` (strict inequality of the row bounds); `VineEstCanonLayer` allows `0 ≤ Bh r`.  Since the
left-hand side does not depend on `Bh` and `regionLeafSize (Bh + ε)` is a finite product of terms `Bh ℓ + ε`, the bound
at `Bh + ε` for every `ε > 0` gives the bound at `Bh`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton Filter Topology
open scoped ENNReal
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem continuous_regionLeafSize_shift {R : CLRegionData G U a b} (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (Bh : ℕ → ℝ) :
    Continuous fun ε : ℝ => regionLeafSize RD hG R layer hLayer (fun r => Bh r + ε) := by
  unfold regionLeafSize
  fun_prop

/-- The bound at every `Bh + ε` (`ε > 0`) gives the bound at `Bh`. -/
theorem le_regionLeafSize_of_forall_pos {R : CLRegionData G U a b} (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (Bh : ℕ → ℝ) {X : ℝ≥0∞}
    (c : ℝ) (H : ∀ ε : ℝ, 0 < ε → X ≤ ENNReal.ofReal (c * regionLeafSize RD hG R layer hLayer (fun r => Bh r + ε))) :
    X ≤ ENNReal.ofReal (c * regionLeafSize RD hG R layer hLayer Bh) := by
  have hc : Continuous fun ε : ℝ => c * regionLeafSize RD hG R layer hLayer (fun r => Bh r + ε) :=
    continuous_const.mul (continuous_regionLeafSize_shift RD hG layer hLayer Bh)
  have h0 : Tendsto (fun ε : ℝ => ENNReal.ofReal (c * regionLeafSize RD hG R layer hLayer (fun r => Bh r + ε)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (c * regionLeafSize RD hG R layer hLayer (fun r => Bh r + 0)))) :=
    ((ENNReal.continuous_ofReal.comp hc).tendsto 0).mono_left nhdsWithin_le_nhds
  have e : (fun r => Bh r + 0) = Bh := by funext r; simp
  rw [e] at h0
  exact ge_of_tendsto h0 (eventually_nhdsWithin_of_forall fun ε hε => H ε hε)

end WaveTurbulence.VineEstS5C
