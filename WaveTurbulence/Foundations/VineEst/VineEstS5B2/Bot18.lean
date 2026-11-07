/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot17

/-! # V5 Step 4d-B2: the bottom vine, part 18 (the statement for the induction over the core vines)

`classSum_bottom`: `tildeJ2_bundle_bottom` with the static parameters `κ0` and the dynamic parameters `(t₀, t₁, t₂, e, f, g, h)` explicit, in
the shape of the flat form of TARGET Step 4 of part C: the class sum is `c ζ ∑'_κ ∫_τ Ψ(κ, (t₀,t₁,t₂), clock τ)` with the clock-based summand
`Ψ = psiBot p kind κ0 A c0 pstar`, which depends only on the static fields of `κ0` (`L γ δ F base`) (`psiBot_static`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} [Fintype ι] [DecidableEq ι]

theorem psiBot_static (κ0 : KPar d) (t0 t1 t2 : ℝ) (e f g h : Mom d) (A : FamilyReconstruction w ι)
    (c0 : ChainAt A.skeleton A.family) (pstar : ι) :
    psiBot p kind { κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h } A c0 pstar =
      psiBot p kind κ0 A c0 pstar := rfl

/-- **The bottom case of the induction over the core vines**: the class sum of a chain region whose bottom joint is the lower joint of the
operative member `pstar` (no other member operative) is `c ζ` times the local sum-integral of the A-chart bundle `psiBot`. -/
theorem classSum_bottom (κ0 : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hA : IsPrimeGarden A.skeleton) (hb0 : c0.b = (A.family.placement pstar).lower)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j)) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    ∑ z ∈ canonFinsetK p kind A c0, twistedLocalKernel z.1 z.2 κ0.L κ0.γ κ0.δ κ0.F κ0.base t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (botR A c0) * clLocalZeta (botR A c0) *
        ∑' κd : CLLocalDecoration (botR A c0) κ0.L κ0.base ![e, f, g, h], ∫ τ : CLInternalTime (botR A c0),
          psiBot p kind κ0 A c0 pstar (clExtendIndices (botR A c0) κd.1) ![t0, t1, t2]
            (clLocalClock (botR A c0) ![t0, t1, t2] τ) :=
  tildeJ2_bundle_bottom (p := p) { κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h } A c0 hA hb0 hup
    hL hF

end WaveTurbulence.VineEstS5B2
