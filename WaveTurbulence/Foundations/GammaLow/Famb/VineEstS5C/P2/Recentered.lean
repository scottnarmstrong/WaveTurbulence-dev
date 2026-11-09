/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P3.Bound
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Recentered
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P3.Bound
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Recentered` (sha256 97ffc75024496db2…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P2: the recentered form of `unrolled_bound` (finding F-RECENTER)

P3's `termFn`/`clsFn` are the NON-recentered kernels (`twistedLocalKernel`), whereas the engine (`clockedExprMul3`, the `sumint` form of V4)
and `VineEstCanonLayer` (`twistedRecentered`) carry the unimodular factor `recFac = exp(-πiδL^{2γ} t₀ Γ(E))`, which depends on the exterior
clock `t₀` and on the boundary momenta, so `XNorm00Restr` is NOT invariant under it.  Here: `termFnR = recFac · termFn`, and
`unrolled_bound_recentered`: the recentered class sum is the sum of the recentered terms, so the abstract per-term bound `TermBoundR` (of
`termFnR`) gives the same finite-Minkowski bound as `P3.unrolled_bound`. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C
variable {γF : ℝ}
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton
  WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3
open scoped ENNReal

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}

/-- The recentered observable of a summand. -/
noncomputable def termFnRΓ (σ : ℤˣ) (κ0 : KPar d) (lv : LvlΓ B) (ψ : PsiT G d) (s : ℤˣ) : (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ :=
  fun tt E => recFac σ s κ0.L κ0.γ κ0.δ tt E * termFnΓ B κ0 lv ψ s tt E

variable (BE : BundleExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P2
