/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B.StateInt1

/-! # V5 Step 4d-B: the S-side of the states of `Zp(A)` in the chart of `A` (part 2: untwisted states)

`rowQ κ G i`, `rowT κ G i`: the exceptional starred couple and tree rows of the state `G` at the member `i` (the native
objects `sigStar G i`; chart free), `nuOf G i`: the sign of the lower joint.
`bundleInt`: the integrand of the chart of `A` (frame of `A`, exceptional factor `rowVal` of the state, lower factor `Ψ`).
`sSumAt_skip`, `sSumAt_false`: the S-side of the skipped state `A` and of a FALSE-choice output in this form.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} {d : ℕ}

/-- The exceptional starred couple row of the state `G` at the member `i`, read through the row selector (ruling F2):
the selection data are those of the native couple `(sigStar G i).2.1` at the pair of the retained leaf. -/
@[expose] noncomputable def rowQ (κ : KPar d) (G : FamilyReconstruction w ι) (i : ι) : ℝ → ℝ → Mom d → ℂ :=
  VineEst.KQsel
    (Flower.V5W.coupleIncoh G.data G.plain (stateLayer G) (stateLayer_isLayering G)
      (pairOfLeaf G.skeleton G.plain (G.family.placement i).retained))
    (Flower.V5W.coupleRootParents rowSel.p G.data G.plain (stateLayer G) (stateLayer_isLayering G)
      (pairOfLeaf G.skeleton G.plain (G.family.placement i).retained) 0)
    (Flower.V5W.coupleRootParents rowSel.p G.data G.plain (stateLayer G) (stateLayer_isLayering G)
      (pairOfLeaf G.skeleton G.plain (G.family.placement i).retained) 1)
    κ.L κ.γ κ.δ κ.F (sigStar G i).2.1

/-- The exceptional starred tree row of the state `G` at the member `i`, read through the row selector (ruling F2):
the selection data are those of the native tree `(sigStar G i).2.2` at the lower joint. -/
@[expose] noncomputable def rowT (κ : KPar d) (G : FamilyReconstruction w ι) (i : ι) : ℝ → ℝ → Mom d → ℂ :=
  VineEst.KTsel
    (Flower.V5W.treeIncoh G.data G.plain (stateLayer G) (stateLayer_isLayering G) (G.family.placement i).lower)
    (Flower.V5W.treeRootParent rowSel.p G.data G.plain (stateLayer G) (stateLayer_isLayering G)
      (G.family.placement i).lower)
    κ.L κ.γ κ.δ κ.F (sigStar G i).2.2

/-- The sign of the lower joint of the member `i` of the state `G`. -/
@[expose] noncomputable def nuOf (G : FamilyReconstruction w ι) (i : ι) : ℤˣ := (sigStar G i).1

/-- The integrand of the chart of `A`: the frame of `A`, the exceptional factor, and the lower factor `Ψ(t_b, E, F_r)`
where `E` and `F_r` are the labels (in the chart of `A`) of the lower joint and of the retained leaf. -/
@[expose] noncomputable def bundleInt (κ : KPar d) (A : FamilyReconstruction w ι)
    (sp : SplitAt A.skeleton A.family pstar J) (Ψ : ℝ → Mom d → Mom d → ℂ) (tw : Bool) (ν : ℤˣ)
    (rq rt : ℝ → ℝ → Mom d → ℂ) (x : ExtS sp.RS κ.L κ.base κ.e κ.f) (σ : CLInternalTime sp.RS) : ℂ :=
  spartFrame A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base sp.sb.U sp.sb.a sp.sb.b
      (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) x.1
      (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ) *
    (rowVal ν rq rt (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ sp.sb.b)
        (if tw then clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ (qrOf (A.family.placement pstar))
          else clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ (qbOf (A.family.placement pstar)))
        (if tw then clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ (qbOf (A.family.placement pstar))
          else clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ (qrOf (A.family.placement pstar)))
        (if tw then κ.base + latticePoint κ.L (x.1 (A.family.placement pstar).lower.toNode)
          else κ.base + latticePoint κ.L (x.1 (A.family.placement pstar).retained.toNode))
        (if tw then κ.base + latticePoint κ.L (x.1 (A.family.placement pstar).retained.toNode)
          else κ.base + latticePoint κ.L (x.1 (A.family.placement pstar).lower.toNode)) *
      Ψ (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ sp.sb.b)
        (κ.base + latticePoint κ.L (x.1 (A.family.placement pstar).lower.toNode))
        (κ.base + latticePoint κ.L (x.1 (A.family.placement pstar).retained.toNode)))

/-- The S-side of the skipped state `A`. -/
theorem sSumAt_skip (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
    (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumAt κ A sp Φ =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 sp.RS * clLocalZeta sp.RS *
        ∑' x : ExtS sp.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp.RS,
          bundleInt κ A sp Φ false (nuOf A pstar) (rowQ κ A pstar) (rowT κ A pstar) x σ := by
  have hS := SplitAt.slow sp
  unfold sSumAt
  rw [sSum_same A.plain A.data A.data κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) (stateLayer A)
    (stateLayer_isLayering A) κ.base (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) sp.RS
    κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ hS.b_mem_erase hS.p0_mem
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (VineEst.SelDataEq.refl _ _ _ _ _ _)]
  congr 1
  refine tsum_congr fun x => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  have hn0 : sp.sb.b.toNode = (A.family.placement pstar).lower.toNode := congrArg GBranch.toNode hS.lower
  have hn1 : sp.sb.b.child sp.RS.kept = (A.family.placement pstar).retained.toNode := by
    rw [hS.keep, hS.lower]
    exact (A.family.placement pstar).child.symm
  have hex := exc_same (A.family.placement pstar) A.plain A.data κ.L κ.γ κ.δ κ.F (stateLayer A)
    (stateLayer_isLayering A) κ.base (S := sp.sb.U) (a := sp.sb.a) hS.lower x.1 (hS.pairedAt_ext x)
    (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ)
  have hT : VineEst.selTreeRow κ.L κ.γ κ.δ κ.F A.data A.plain (stateLayer A) (stateLayer_isLayering A) sp.sb.b =
      VineEst.selTreeRow κ.L κ.γ κ.δ κ.F A.data A.plain (stateLayer A) (stateLayer_isLayering A)
        (A.family.placement pstar).lower := by
    rw [hS.lower]
  unfold sameInt bundleInt
  rw [hex, hn0, hn1, hT]
  rfl

end WaveTurbulence.VineEstS5B
