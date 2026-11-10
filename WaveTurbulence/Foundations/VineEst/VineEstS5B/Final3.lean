/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Final2

/-! # V5 Step 4d-B: the twisted factor identity at `U^p` (TARGET (tildeJ2), L1877-L1925)

`zp_state`: for every `G ∈ Zp(A)`, `sSumAt G (K̃^G)` is `± c ∑' ∫ bundleInt ...` in the chart of `A`, with `BOK`.
`tildeJ2_bundle`: the sum over `Zp(A)` is `c ∑'_x ∫_σ ∑_G ε_G bundleInt_G`: all states share the frame and the lower factor
`K̃_A(t_b, E, F_r)`; only the exceptional factor `rowVal` (rows `rowQ`, `rowT`, sign `nuOf`, clock/label pattern `tw`) differs.
The rows enter only as abstract functions `rowQ κ G p*`, `rowT κ G p*` (starred kernels of the native objects of `G`), so
the statement is independent of the input profile `κ.F` beyond the summability premise `hF`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]

open Classical in
/-- The sign `ε_G = -1` for a twisted state, `+1` otherwise. -/
@[expose] noncomputable def epsOf (A : FamilyReconstruction w ι) (pstar : ι) (G : FamilyReconstruction w ι) : ℂ :=
  if twAt A G pstar then -1 else 1

theorem tw_false (A : FamilyReconstruction w ι) {kind : Bool} (hcan : CanonicalObject p kind A.layered)
    (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
      (A.family.atoms pstar) (A.family.upper pstar))
    (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
    (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))
    (con : LFConstruction (A.source pstar hcan hel htc hcc) false) :
    ¬ twAt A (opOut A pstar hcan hel htc hcc con) pstar := by
  intro hh
  apply hh
  rw [sigStar_false A hcan hel htc hcc con]
  rfl

theorem tw_true (A : FamilyReconstruction w ι) {kind : Bool} (hcan : CanonicalObject p kind A.layered)
    (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
      (A.family.atoms pstar) (A.family.upper pstar))
    (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
    (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))
    (con : LFConstruction (A.source pstar hcan hel htc hcc) true) :
    twAt A (opOut A pstar hcan hel htc hcc con) pstar := by
  intro e
  have h1 : (sigStar (opOut A pstar hcan hel htc hcc con) pstar).1 = -(sigStar A pstar).1 := by
    rw [sigStar_output]
    exact (sign_out_true A pstar hcan hel htc hcc con).trans (congrArg (fun z => -z) (by rw [sigStar_self]))
  exact units_ne_neg (sigStar A pstar).1 (by rw [← h1]; exact e.symm)

end WaveTurbulence.VineEstS5B
