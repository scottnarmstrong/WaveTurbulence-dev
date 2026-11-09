/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowStep
public import WaveTurbulence.Foundations.VineEst.VineEstS4.AssemblyReach
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Kernel
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowReach
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowSum
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.AssemblyReach
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowCoh
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS4.RowReach` (sha256 5a6ab350a871edf7…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Rows of a reached state (V5 Step 4b, step 1)

Along any `Reach`:
* `Reach.localInc_le`: `M₁` (the sum of the incoherency counts of the regional couples and interior trees) of the reached
  state is at least that of the start (ordinary rows are LF-invariant, the two exceptional objects of every operation are
  coherent in the source).  Hence `L^{-η⁸(cohmol + M₁)}` is no larger at the reached garden than at the start.
* `Reach.rowsCoh`: the chart-free row coherence `RowsCoh` of the start is carried to the reached state: either no operation
  was applied (the state is the start) or the state is canonical (the output of an LF operation), where every
  coherent row is coherent by `rowsCoh_of_canonical`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS4
open WaveTurbulence.VineEstS4
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3
  WaveTurbulence.Links WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton VineParamContract TTree
variable {w : ℕ} {ι : Type*}

section Assemblies
variable {p : ℕ} {kind : Bool} {M : List ι} {A B : FamilyReconstruction w ι}
  {c : ChainAt A.skeleton A.family} {c' : ChainAt B.skeleton B.family} {n : ℕ}
  (hM9 : NormalChartSupply γF) (h : Reach p kind M A c B c')
  (B0 : CLChainAssemblyΓ γF A.skeleton (clRegionData A.skeleton c.block c.cl) n)
  (B1 : CLChainAssemblyΓ γF B.skeleton (clRegionData B.skeleton c'.block c'.cl) n)
include h

/-- **`RowCoherent` of the reached garden** (any assembly of the reached region) follows from `RowCoherent` of the
start (any assembly of the start region). -/
theorem Reach.rowCoherentΓ {d : ℕ} (bk0 : Fin (assemblyShapeΓ hM9 B0).I → Fin 4) (q0 : Fin 3 → ℕ)
    (bk1 : Fin (assemblyShapeΓ hM9 B1).I → Fin 4) (q1 : Fin 3 → ℕ) (centre : Fin 4 → Mom d) (wBar : Mom d)
    (hq0 : q0 0 = stateLayer A (A.data.coreBranch A.plain c.a).toNode)
    (hq1 : q1 0 = stateLayer B (B.data.coreBranch B.plain c'.a).toNode)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (H : RowCoherentΓ hM9 B0 A.data A.plain (stateLayer A) (stateLayer_isLayering A)
      (step3WΓ hM9 B0 A.data A.plain (stateLayer A) (stateLayer_isLayering A) bk0 q0 centre wBar) L γ δ F p) :
    RowCoherentΓ hM9 B1 B.data B.plain (stateLayer B) (stateLayer_isLayering B)
      (step3WΓ hM9 B1 B.data B.plain (stateLayer B) (stateLayer_isLayering B) bk1 q1 centre wBar) L γ δ F p := by
  rw [rowCoherent_iffΓ hM9 B1 B.data B.plain (stateLayer B) (stateLayer_isLayering B) _ rfl hq1]
  rw [rowCoherent_iffΓ hM9 B0 A.data A.plain (stateLayer A) (stateLayer_isLayering A) _ rfl hq0] at H
  exact h.rowsCoh H

end Assemblies

end WaveTurbulence.GammaLow.Famb.VineEstS4
