/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLF
public import WaveTurbulence.Foundations.VineEst.RowSel.RowTransport
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp13Rig
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp4Rigid

/-! # `SOK` along operations and batches below the split (V5 Step 4b, step 4, WP-E, part 4)

`SOKAt κ X sp Φ`: the integrand of `sSumAt κ X sp Φ` is integrable / summable.  `SOKAt_op`: invariant under an operation at a member of
`J`; `SOKAt_reachBelow`: invariant along a `ReachSp` over members of `J`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2 WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι}

/-- The integrand of the S-side is integrable and summable. -/
@[expose] def SOKAt (κ : KPar d) (X : FamilyReconstruction w ι) (sp : SplitAt X.skeleton X.family pstar J)
    (Φ : ℝ → Mom d → Mom d → ℂ) : Prop :=
  SOK sp.RS X.data X.plain κ.L κ.γ κ.δ κ.F (stateLayer X) (stateLayer_isLayering X) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f
    sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ

section LF
variable {LG : LayeredGarden w} (s : LFSource p kind LG)

/-- `SOK` invariance for a TRUE-choice LF construction at a member below the split. -/
theorem SOK_rigid_LF_iff (h : LFConstruction s true) {S : Finset (GBranch s.skeleton.tree)} {a b : GBranch s.skeleton.tree}
    (hS : s.skeleton.molecule.IsBlock S a b) (hR : RigidAt s.placement S b) (RS : CLRegionData s.skeleton S a b)
    (RS' : CLRegionData (unitTwistGarden s.skeleton s.placement) (twistedAtoms s.skeleton s.placement S)
      (eB s.placement a) (eB s.placement b))
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain true)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain true)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain true) layer' hLayer' = h.output)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d) (n0 n1 : GNode s.skeleton.tree)
    (Φ : ℝ → Mom d → Mom d → ℂ) :
    SOK RS' h.data (s.chosen_plain true) L γ δ F layer' hLayer' base t0 t1 t2 e f
        (naiveNodeEquiv s.skeleton s.placement n0) (naiveNodeEquiv s.skeleton s.placement n1) Φ ↔
      SOK RS s.data s.plain L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ := by
  refine SOK_rigid_iff s.placement hS hR RS RS' s.plain s.data h.data L γ δ F layer hLayer layer' hLayer' base ?_ ?_ ?_ ?_ ?_ ?_
    t0 t1 t2 e f n0 n1 Φ
  · intro q hq
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hne : q ≠ s.exceptional := by
      intro hqe
      have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
      subst hqe'
      rcases pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained with hq' | hq'
      · exact not_internal_retained_of s.placement hR.lower_notMem (hq' ▸ hint)
      · exact not_internal_pair_of s.placement hR.lower_notMem (hq' ▸ hint)
    exact native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hne
  · intro v hv
    exact native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v (hR.ne_lower (Finset.mem_of_mem_erase hv))
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v
  · intro q hq
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hne : q ≠ s.exceptional := by
      intro hqe
      have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
      subst hqe'
      rcases pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained with hq' | hq'
      · exact not_internal_retained_of s.placement hR.lower_notMem (hq' ▸ hint)
      · exact not_internal_pair_of s.placement hR.lower_notMem (hq' ▸ hint)
    exact Flower.V5W.coupleIncoh_LF h layer hLayer hspec layer' hLayer' hspec' q hne
  · intro v hv
    exact Flower.V5W.treeIncoh_LF h layer hLayer hspec layer' hLayer' hspec' v (hR.ne_lower (Finset.mem_of_mem_erase hv))
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v

/-- `SOK` invariance for a FALSE-choice LF construction (same skeleton and region). -/
theorem SOK_false_LF_iff (h : LFConstruction s false) {S : Finset (GBranch s.skeleton.tree)} {a b : GBranch s.skeleton.tree}
    (hlow : s.placement.lower ∉ S) (RS : CLRegionData s.skeleton S a b)
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain false)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain false)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain false) layer' hLayer' = h.output)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d) (n0 n1 : GNode s.skeleton.tree)
    (Φ : ℝ → Mom d → Mom d → ℂ) :
    SOK RS h.data (s.chosen_plain false) L γ δ F layer' hLayer' base t0 t1 t2 e f n0 n1 Φ ↔
      SOK RS s.data s.plain L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ := by
  have hpt : ∀ (xS : ExtS RS L base e f) σ,
      sInt RS h.data (s.chosen_plain false) L γ δ F layer' hLayer' base t0 t1 t2 e f n0 n1 Φ xS σ =
        sInt RS s.data s.plain L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ xS σ := by
    intro xS σ
    have hsp := spart_congr_data (a := a) (S := S) s.plain h.data s.data L γ δ F layer' hLayer' layer hLayer base ?_ ?_ ?_ ?_ ?_ ?_ ?_ b
      xS.1 (clLocalClock RS ![t0, t1, t2] σ)
    · unfold sInt
      rw [hsp]
    · intro q hq
      have hint := (mem_clRegionalPairs s.skeleton).mp hq
      have hne : q ≠ s.exceptional := by
        intro hqe
        have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
        subst hqe'
        rcases pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained with hq' | hq'
        · exact not_internal_retained_of s.placement hlow (hq' ▸ hint)
        · exact not_internal_pair_of s.placement hlow (hq' ▸ hint)
      have := native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hne
      have hp : s.pairs false q = q := pairOfLeaf_firstLeaf s.skeleton s.plain q
      rwa [hp] at this
    · intro v hv
      exact native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v (fun e => hlow (e ▸ (Finset.mem_of_mem_erase hv)))
    · intro v _
      exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v
    · intro q hq
      have hint := (mem_clRegionalPairs s.skeleton).mp hq
      have hne : q ≠ s.exceptional := by
        intro hqe
        have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
        subst hqe'
        rcases pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained with hq' | hq'
        · exact not_internal_retained_of s.placement hlow (hq' ▸ hint)
        · exact not_internal_pair_of s.placement hlow (hq' ▸ hint)
      have := Flower.V5W.coupleIncoh_LF h layer hLayer hspec layer' hLayer' hspec' q hne
      have hp : s.pairs false q = q := pairOfLeaf_firstLeaf s.skeleton s.plain q
      rwa [hp] at this
    · intro v hv
      exact Flower.V5W.treeIncoh_LF h layer hLayer hspec layer' hLayer' hspec' v
        (fun e => hlow (e ▸ (Finset.mem_of_mem_erase hv)))
    · intro pp q _ i
      exact VineEst.coupleRootParents_congr_all s.plain h.data s.data layer' hLayer' layer hLayer
        (fun v => coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v) pp q i
    · intro pp v _
      exact VineEst.treeRootParent_congr_all s.plain h.data s.data layer' hLayer' layer hLayer
        (fun v => coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v) pp v
  have hfun : ∀ xS : ExtS RS L base e f,
      sInt RS h.data (s.chosen_plain false) L γ δ F layer' hLayer' base t0 t1 t2 e f n0 n1 Φ xS =
        sInt RS s.data s.plain L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ xS := fun xS => funext (hpt xS)
  unfold SOK
  simp only [hfun]

end LF

end WaveTurbulence.VineEstS4
