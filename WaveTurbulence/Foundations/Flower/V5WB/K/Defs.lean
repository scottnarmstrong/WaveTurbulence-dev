/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VineEst.VineSpaceK.Statements
public import WaveTurbulence.Foundations.Flower.Stage1W.Defs

/-! # V5W-B-WORLD: the V5-SPACE kernels and flat statements for every row selector

Copied by source from main 416902c8 (`VineEst/VineSpaceK/StatementDefs.lean`: `memberMX`, `twistedRecenteredModCX`,
`flatFnRMX`; `VineEst/VineSpaceK/Statements.lean`: `VineFlatC2MX`, `VineFlatHalfMX`; see `COPIED-SHA256SUMS`).  On main
these sit outside the V5 tower and read the plain rows; here they carry the row selector (`variable [RowSel]`), so
that the weighted selector `selW` reads its rows.  Bodies are verbatim; the namespace is `WaveTurbulence.Flower.V5WB`.
The selector-free names (`ClassMember`, `EnginePullback`, `nodeWeight`, `spatialMul`) are main's.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul)

section KernelDefs
open MeasureTheory VineEstS5C VineEstS5C.Cont VineEstS4 LFTwist RegRed Reg.Skeleton
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
/-- Spatial multiplication precedes both the lattice sum and time integration. -/
def memberMX (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (lam : ℝ)
    (m : (GNode G.tree → Fin d → ℤ) → ℂ)
    (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) : ℂ :=
  (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
    ∑' κ : CLLocalDecoration R L base ![e, f, g, h],
      ∫ τ : CLInternalTime R, m (clExtendIndices R κ.1) *
        (lowModC R lam ![tUpper, tPositive, tNegative] τ *
          clLocalSummand D hG R L γ δ F layer hLayer base ![e, f, g, h] ![tUpper, tPositive, tNegative] κ τ)

/-- A literal weighted class. The multiplier family is still indexed by each member;
its covariance must be certified before any common-data factorization is used. -/
def twistedRecenteredModCX {ι : Type*} (G : Garden w) (a : GBranch G.tree)
    (Z : Finset (ClassMember w ι))
    (m : (z : ClassMember w ι) → (GNode z.1.skeleton.tree → Fin d → ℤ) → ℂ)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (lam t0 t1 t2 : ℝ) (e f g h : Mom d) : ℂ :=
  Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * t0 * boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ) * Complex.I) *
    ∑ z ∈ Z, memberMX z.1.data z.1.plain (clRegionData z.1.skeleton z.2.block z.2.cl)
      L γ δ F (stateLayer z.1) (stateLayer_isLayering z.1) base lam (m z) t0 t1 t2 e f g h

end KernelDefs

section FlatDefs
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
variable {kind : Bool}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
/-- The weighted flat observable of the top level: `recFac · c ζ · lkRaw (modPsi b λ psiFuel)`. -/
noncomputable def flatFnRMX (m : (GNode G.tree → Fin d → ℤ) → ℂ) (lam : ℝ) (σ : ℤˣ) (κ0 : KPar d) (hprime : IsPrimeGarden G) (s : ℤˣ) :
    (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ :=
  fun tt E => recFac σ s κ0.L κ0.γ κ0.δ tt E * (Lvl.cst B κ0 (Lvl.top B) *
    lkRaw (Lvl.top B).region κ0.L κ0.base
      (spatialMul m (modPsi b lam (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B))))
      tt (sumintBoundary s E))


end FlatDefs

section Statements
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine

end Statements

end WaveTurbulence.Flower.V5WB
