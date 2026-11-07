/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.SelDataLF
public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLF
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.StateInt3
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Transport
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp14Op

/-! # V5 Step 4d-B: integrability and summability of the A-chart integrands of the states of `Zp(A)`

`BOK`: the pair (integrable in the times for every decoration, summable `L¹` norms in the decorations).
`bok_skip`, `bok_false`, `bok_true`: `BOK` of the A-chart integrand `bundleInt` of the skipped state, of a FALSE-choice output and
of a TRUE-choice output (twisted state), from `SOKAt` of the respective state (transport along `extEquiv` and `tEquivS`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} {d : ℕ}

/-- Integrable in the times for every decoration, with summable `L¹` norms. -/
@[expose] def BOK {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (RS : CLRegionData G S a b)
    (L : ℝ) (base e f : Mom d) (g : ExtS RS L base e f → CLInternalTime RS → ℂ) : Prop :=
  (∀ x, Integrable (g x)) ∧ Summable fun x => ∫ σ, ‖g x σ‖

theorem sok_RS_irrel {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R R' : CLRegionData G S a b)
    (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d) (n0 : GNode G.tree)
    (Φ : ℝ → Mom d → Mom d → ℂ) :
    SOK R D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 (b.child R.kept) Φ ↔
      SOK R' D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 (b.child R'.kept) Φ := by
  rw [regionData_subsingleton R R']

theorem bok_skip (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
    (Φ : ℝ → Mom d → Mom d → ℂ) (hok : SOKAt κ A sp Φ) :
    BOK sp.RS κ.L κ.base κ.e κ.f
      (bundleInt κ A sp Φ false (nuOf A pstar) (rowQ κ A pstar) (rowT κ A pstar)) := by
  have hS := SplitAt.slow sp
  have hfun : bundleInt κ A sp Φ false (nuOf A pstar) (rowQ κ A pstar) (rowT κ A pstar) =
      sInt sp.RS A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f
        sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ := by
    funext x σ
    rw [sInt_same A.plain A.data A.data κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) (stateLayer A)
      (stateLayer_isLayering A) κ.base (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) sp.RS
      κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ hS.b_mem_erase hS.p0_mem
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (VineEst.SelDataEq.refl _ _ _ _ _ _) x σ]
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
  unfold BOK
  rw [hfun]
  exact hok

section Ops
variable (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
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

theorem bok_false (con : LFConstruction (A.source pstar hcan hel htc hcc) false) (Φ : ℝ → Mom d → Mom d → ℂ)
    (hok : SOKAt κ (opOut A pstar hcan hel htc hcc con) (SplitAt.nextA A sp pstar false) Φ) :
    BOK sp.RS κ.L κ.base κ.e κ.f
      (bundleInt κ A sp Φ false (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
        (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar)) := by
  have hS := SplitAt.slow sp
  have hfun : bundleInt κ A sp Φ false (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
        (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) =
      sInt sp.RS con.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
        (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f
        sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ := by
    funext x σ
    rw [← sameInt_false_eq κ A sp hcan hel htc hcc con Φ x σ]
    refine (sInt_same A.plain A.data con.data κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A)
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      κ.base (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) sp.RS κ.t0 κ.t1 κ.t2 κ.e κ.f
      sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ hS.b_mem_erase hS.p0_mem ?_ ?_ ?_
      (VineEst.selDataEq_LF_false con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) _ _ (fun q hq => (Finset.mem_erase.mp hq).1)
        (fun v hv => hS.lower ▸ (Finset.mem_erase.mp hv).1)).symm x σ).symm
    · intro q hq
      obtain ⟨hq0, _⟩ := Finset.mem_erase.mp hq
      have := native_couple_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) q hq0
      have hp : (A.source pstar hcan hel htc hcc).pairs false q = q := pairOfLeaf_firstLeaf A.skeleton A.plain q
      rw [hp] at this
      exact this.symm
    · intro v hv
      exact (native_tree_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v (hS.lower ▸ (Finset.mem_erase.mp hv).1)).symm
    · intro v _
      exact (coreLayer_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v).symm
  unfold BOK
  rw [hfun]
  unfold SOKAt at hok
  exact (sok_RS_irrel (SplitAt.nextA A sp pstar false).RS sp.RS _ _ κ.L κ.γ κ.δ κ.F _ _ κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f
    sp.sb.b.toNode Φ).mp hok

theorem bok_true (con : LFConstruction (A.source pstar hcan hel htc hcc) true) (Φ' : ℝ → Mom d → Mom d → ℂ)
    (hok : SOKAt κ (opOut A pstar hcan hel htc hcc con) (SplitAt.nextA A sp pstar true) Φ') :
    BOK sp.RS κ.L κ.base κ.e κ.f
      (bundleInt κ A sp (fun t E Fr => Φ' t Fr E) true (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
        (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar)) := by
  have hS := SplitAt.slow sp
  have hT := stw_true A sp
  unfold BOK
  refine sok_transport (hT.extEquiv κ.L κ.base κ.e κ.f)
    (tEquivS (A.family.placement pstar) sp.RS (SplitAt.nextA A sp pstar true).RS)
    (tEquivS_measurePreserving (A.family.placement pstar) sp.RS (SplitAt.nextA A sp pstar true).RS) _
    (sInt (SplitAt.nextA A sp pstar true).RS con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)
      κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
      (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f
      (eB (A.family.placement pstar) sp.sb.b).toNode
      ((eB (A.family.placement pstar) sp.sb.b).child (SplitAt.nextA A sp pstar true).RS.kept) Φ') ?_ hok
  intro x σ
  rw [← twInt_true_eq κ A sp hcan hel htc hcc con Φ' x σ]
  exact sInt_tw hT A.plain A.data con.data κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A)
    (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
    κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f Φ'
    (fun q _ hq => native_couple_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) q hq)
    (fun v _ hv => native_tree_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v (hS.lower ▸ hv))
    (fun v _ => coreLayer_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v)
      (fun q _ hq => Flower.V5W.coupleIncoh_LF con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) q hq)
      (fun v _ hv => Flower.V5W.treeIncoh_LF con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v (hS.lower ▸ hv))
      (fun v _ => coreLayer_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v) x σ

end Ops

end WaveTurbulence.VineEstS5B
