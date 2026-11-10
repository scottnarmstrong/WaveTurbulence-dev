/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLF
public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot11

/-! # V5 Step 4d-B2: the bottom vine, part 14 (`botState_true`)

See `Bot13`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} [Fintype ι] [DecidableEq ι]

/-- TRUE-choice states: `twIntB` is `botKernel` with the pattern `tw = true`. -/
theorem twIntB_eq_botKernel (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hb0 : c0.b = (A.family.placement pstar).lower) (G : FamilyReconstruction w ι)
    (D' : ReconstructionData (unitTwistGarden A.skeleton (A.family.placement pstar)))
    (layer' : GNode (D'.forest (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)) → ℕ)
    (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)) layer')
    (hσ : sigStar G pstar = ((unitTwistGarden A.skeleton (A.family.placement pstar)).sign
        (eB (A.family.placement pstar) (A.family.placement pstar).lower).toNode,
      nativeCoupleLayered D' (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain) layer' hLayer'
        (tp (A.family.placement pstar) A.plain (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)),
      nativeChainLayered D' (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain) layer' hLayer'
        (eB (A.family.placement pstar) (A.family.placement pstar).lower)))
    (hQ : rowQ κ G pstar = VineEst.selCoupleRow κ.L κ.γ κ.δ κ.F D'
      (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain) layer' hLayer'
      (tp (A.family.placement pstar) A.plain (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)))
    (hT : rowT κ G pstar = VineEst.selTreeRow κ.L κ.γ κ.δ κ.F D'
      (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain) layer' hLayer'
      (eB (A.family.placement pstar) (A.family.placement pstar).lower))
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch A.skeleton.tree → ℝ)
    (u' : GBranch (unitTwistGarden A.skeleton (A.family.placement pstar)).tree → ℝ)
    (hub : u' (eB (A.family.placement pstar) c0.b) = u c0.b)
    (hqb : u' (eB (A.family.placement pstar) (qbOf (A.family.placement pstar))) = u (qbOf (A.family.placement pstar)))
    (hqr : u' (eB (A.family.placement pstar) (qrOf (A.family.placement pstar))) = u (qrOf (A.family.placement pstar))) :
    twIntB (RS := botR A c0) (A.family.placement pstar) A.plain A.data D' κ.L κ.γ κ.δ κ.F (stateLayer A)
        (stateLayer_isLayering A) layer' hLayer' κ.base t x u u' =
      botKernel κ A c0 pstar true (nuOf G pstar) (rowQ κ G pstar) (rowT κ G pstar) x t u := by
  have hex := exc_tw (A.family.placement pstar) A.plain D' κ.L κ.γ κ.δ κ.F layer' hLayer' κ.base c0.U (a := c0.a)
    hb0 x u' u hub hqb hqr
  unfold twIntB botKernel
  rw [hex, hQ, hT]
  unfold nuOf
  rw [hσ]
  simp only [if_true]
  have e1 : eB (A.family.placement pstar) c0.b = eB (A.family.placement pstar) (A.family.placement pstar).lower := by
    rw [hb0]
  have e2 : u c0.b = u c0.b := rfl
  rw [e1]

section Ops
variable (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
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

end Ops

end WaveTurbulence.VineEstS5B2
