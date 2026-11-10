/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot10

/-! # V5 Step 4d-B2: the bottom vine, part 11 (the A-chart integrand of a state of the class; the skipped state)

For the chain region `c0` of the state `A` whose bottom joint is the lower joint of the member `pstar`, `botKernel` is the integrand of the chart
of `A` with the exceptional rows of a state `G` (`rowVal`, sign `ν`, clock/label pattern `tw`) and the `b`-factor of `A`; there is no
lower factor.  `stBot G` is the signed integrand of the state `G` (`ε_G = -1` iff `G` is twisted at `pstar`).
`botState_skip`: the skipped state `A` itself.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} [Fintype ι] [DecidableEq ι]

/-- The region data of the chain region of `A`. -/
@[expose, reducible] noncomputable def botR (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family) :
    CLRegionData A.skeleton c0.U c0.a c0.b := clRegionData A.skeleton c0.block c0.cl

/-- The A-chart integrand of a state with exceptional rows `(rq, rt)`, sign `ν`, clock/label pattern `tw`, without a lower factor. -/
@[expose] noncomputable def botKernel (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (pstar : ι) (tw : Bool) (ν : ℤˣ) (rq rt : ℝ → ℝ → Mom d → ℂ) (x : GNode A.skeleton.tree → (Fin d → ℤ))
    (t : Fin 3 → ℝ) (u : GBranch A.skeleton.tree → ℝ) : ℂ :=
  spartFrame A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base c0.U c0.a c0.b
      (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) x u *
    (rowVal ν rq rt (u c0.b)
        (if tw then u (qrOf (A.family.placement pstar)) else u (qbOf (A.family.placement pstar)))
        (if tw then u (qbOf (A.family.placement pstar)) else u (qrOf (A.family.placement pstar)))
        (if tw then κ.base + latticePoint κ.L (x (A.family.placement pstar).lower.toNode)
          else κ.base + latticePoint κ.L (x (A.family.placement pstar).retained.toNode))
        (if tw then κ.base + latticePoint κ.L (x (A.family.placement pstar).retained.toNode)
          else κ.base + latticePoint κ.L (x (A.family.placement pstar).lower.toNode)) *
      bFac (botR A c0) κ.L κ.γ κ.δ κ.base x t u)

open Classical in
/-- The signed A-chart integrand of the state `G` (sign `-1` iff `G` is twisted at `pstar`). -/
@[expose] noncomputable def stBot (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (pstar : ι) (G : FamilyReconstruction w ι) (x : GNode A.skeleton.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    (u : GBranch A.skeleton.tree → ℝ) : ℂ :=
  epsOf A pstar G * botKernel κ A c0 pstar (decide (twAt A G pstar)) (nuOf G pstar) (rowQ κ G pstar) (rowT κ G pstar) x t u

variable {pstar : ι}

/-- Same-chart states (skip, FALSE choice): `sameIntB` is `botKernel` with the pattern `tw = false`. -/
theorem sameIntB_eq_botKernel (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hb0 : c0.b = (A.family.placement pstar).lower) (G : FamilyReconstruction w ι)
    (D2 : ReconstructionData A.skeleton) (layer2 : GNode (D2.forest A.plain) → ℕ)
    (hLayer2 : IsLayering (D2.garden A.plain) layer2)
    (hσ : sigStar G pstar = (A.skeleton.sign (A.family.placement pstar).lower.toNode,
      nativeCoupleLayered D2 A.plain layer2 hLayer2 (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained),
      nativeChainLayered D2 A.plain layer2 hLayer2 (A.family.placement pstar).lower))
    (hQ : rowQ κ G pstar = VineEst.selCoupleRow κ.L κ.γ κ.δ κ.F D2 A.plain layer2 hLayer2
      (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained))
    (hT : rowT κ G pstar = VineEst.selTreeRow κ.L κ.γ κ.δ κ.F D2 A.plain layer2 hLayer2 (A.family.placement pstar).lower)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (hpx : PairedAt (A.family.placement pstar) x) (t : Fin 3 → ℝ)
    (u : GBranch A.skeleton.tree → ℝ) :
    sameIntB A.plain A.data D2 κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) layer2 hLayer2 κ.base
        (botR A c0) (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) t x u =
      botKernel κ A c0 pstar false (nuOf G pstar) (rowQ κ G pstar) (rowT κ G pstar) x t u := by
  have hex := exc_same (A.family.placement pstar) A.plain D2 κ.L κ.γ κ.δ κ.F layer2 hLayer2 κ.base
    (S := c0.U) (a := c0.a) hb0 x hpx u
  unfold sameIntB botKernel
  rw [hex, hQ, hT]
  unfold nuOf
  rw [hσ]
  simp only [Bool.false_eq_true, if_false]
  have e1 : A.skeleton.sign c0.b.toNode = A.skeleton.sign (A.family.placement pstar).lower.toNode := by rw [hb0]
  have e2 : VineEst.selTreeRow κ.L κ.γ κ.δ κ.F D2 A.plain layer2 hLayer2 c0.b =
      VineEst.selTreeRow κ.L κ.γ κ.δ κ.F D2 A.plain layer2 hLayer2 (A.family.placement pstar).lower := by rw [hb0]
  have e3 : x c0.b.toNode = x (A.family.placement pstar).lower.toNode := by rw [hb0]
  rw [e1, e2, e3]

section Ops
variable {p : ℕ} {kind : Bool} (κ : KPar d) (A : FamilyReconstruction w ι)
  (hcan : CanonicalObject p kind A.layered)
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

/-- The selected exceptional couple row of a FALSE-choice output is the selected row of the output data at the source
pair (ruling F2). -/
theorem rowQ_false_eq (con : LFConstruction (A.source pstar hcan hel htc hcc) false) :
    rowQ κ (opOut A pstar hcan hel htc hcc con) pstar =
      VineEst.selCoupleRow κ.L κ.γ κ.δ κ.F con.data A.plain (stateLayer (opOut A pstar hcan hel htc hcc con))
        (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) := by
  unfold rowQ
  rw [sigStar_false A hcan hel htc hcc con]
  rfl

/-- The selected exceptional tree row of a FALSE-choice output is the selected row of the output data at the lower
joint (ruling F2). -/
theorem rowT_false_eq (con : LFConstruction (A.source pstar hcan hel htc hcc) false) :
    rowT κ (opOut A pstar hcan hel htc hcc con) pstar =
      VineEst.selTreeRow κ.L κ.γ κ.δ κ.F con.data A.plain (stateLayer (opOut A pstar hcan hel htc hcc con))
        (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) (A.family.placement pstar).lower := by
  unfold rowT
  rw [sigStar_false A hcan hel htc hcc con]
  rfl

end Ops

end WaveTurbulence.VineEstS5B2
