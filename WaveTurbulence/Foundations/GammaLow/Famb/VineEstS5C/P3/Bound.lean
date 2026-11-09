/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P3.Count
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P3.Bound
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P3.Unroll
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P3.Bound` (sha256 731cd3b47adaa3a0…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P3 EXPORT: `unrolled_bound` (V5 Step 4d part C)

The observable `termFn lv ψ s tt E = c ζ lkRaw ψ tt (sumintBoundary s E)` of a summand `ψ`; `clsFn lv s` the class sum with the boundary
parameters `sumintBoundary s E`.  `clsFn_eq_sum_terms`: on the window, `clsFn` is the sum of `termFn ψ` over the unrolled terms.
**`unrolled_bound`**: the abstract per-term bound `TermBound` (to be delivered by the engine, one clocked expression per term) gives
`XNorm00Restr θ B K (clsFn) ≤ (cc θ q + 1) * (#terms * β)`; `unrolled_bound_pow`: `#terms ≤ N ^ #members`; `unrolled_bound_gain`: the
gain `L^{-η² b}` of a term bound `C L^{-η² b}` combines with `N ^ #members`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P3
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3
variable {γF : ℝ}
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.GammaLow.Famb.VineEstS4
open WaveTurbulence.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C
open scoped ENNReal

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}

/-- The constant `c ζ` of a level. -/
noncomputable def LvlΓ.cstΓ (κ0 : KPar d) (lv : LvlΓ B) : ℂ :=
  (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region

/-- The observable of a summand: `c ζ lkRaw ψ` at the exterior clocks `tt` and the boundary `sumintBoundary s E`. -/
noncomputable def termFnΓ (κ0 : KPar d) (lv : LvlΓ B) (ψ : PsiT G d) (s : ℤˣ) : (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ :=
  fun tt E => LvlΓ.cstΓ B κ0 lv * lkRaw lv.region κ0.L κ0.base ψ tt (sumintBoundary s E)

variable (BE : BundleExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P3
