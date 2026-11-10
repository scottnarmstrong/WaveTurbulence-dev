/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot15

/-! # V5 Step 4d-B2: the S-side twist identity at an operative BOTTOM vine

**`tildeJ2_bundle_bottom`** (TARGET Step 4, L1850-L1935, for `p* = ` the bottom piece, `U^{<p}` empty): for a state `A` with prime skeleton, a
chain region `c0` of `A` whose bottom joint is the lower joint of the member `pstar`, and no operation at any other member, the class sum
`∑_{y ∈ canonFinsetK p kind A c0} K^U_y` equals `c ζ ∑'_κ ∫_τ psiBot κ A c0 pstar (κ) t (clock τ)`, where
`psiBot x t u = ∑_{G} ε_G · frame_A · rowVal_G · bFac_A` is the A-chart bundle at the bottom vine: the exceptional pair rows `rowQ`, `rowT`
of every state `G` of the class, with the twisted clock slots and labels exchanged (`tw`), sign `ν_G`, and sign `ε_G = -1` for twisted
states; there is no lower factor (`K̃^{U<p}` is trivial: its only content, the conservation at `b` and the time conditions at the boundary
children, is the factor `bFac_A` and the boundary-decoration constraint of `CLLocalDecoration`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} [Fintype ι] [DecidableEq ι]

/-- The A-chart bundle at the bottom vine: the signed sum over the class of the integrands `stBot`. -/
@[expose] noncomputable def psiBot (p : ℕ) (kind : Bool) (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (pstar : ι) (x : GNode A.skeleton.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch A.skeleton.tree → ℝ) : ℂ :=
  ∑ z ∈ canonFinsetK p kind A c0, stBot κ A c0 pstar z.1 x t u

end WaveTurbulence.VineEstS5B2
