/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.SelDataLF
public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLF
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Low
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Op1Step

/-! # V5 Step 4d-B: the S-side of the output of one LF operation at the member `p*` (the member whose lower joint is the
bottom joint of the upper block)

`sSum_twLF` (TRUE choice): the original-chart form with the sign `-1`, the frame of the source data and the exceptional factor
of the output data.  `sSum_falseLF` (FALSE choice / skip): the same chart.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4 WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

section True
variable (h : LFConstruction s true) {S : Finset (GBranch s.skeleton.tree)} {a b : GBranch s.skeleton.tree}
  (RS : CLRegionData s.skeleton S a b)
  (RS' : CLRegionData (unitTwistGarden s.skeleton s.placement) (twistedAtoms s.skeleton s.placement S)
    (eB s.placement a) (eB s.placement b))
  (hS : STw s.placement RS RS')
  (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
  (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
  (layer' : GNode (h.data.forest (s.chosen_plain true)) → ℕ)
  (hLayer' : IsLayering (h.data.garden (s.chosen_plain true)) layer')
  (hspec' : layeredReconstruction h.data (s.chosen_plain true) layer' hLayer' = h.output)

include hS hspec hspec' in
theorem sSum_twLF {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d)
    (Φ' : ℝ → Mom d → Mom d → ℂ) :
    sSum RS' h.data (s.chosen_plain true) L γ δ F layer' hLayer' base t0 t1 t2 e f (eB s.placement b).toNode
        ((eB s.placement b).child RS'.kept) Φ' =
      -((coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * clLocalZeta RS *
        ∑' x : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
          twInt (RS' := RS') s.plain s.data h.data L γ δ F layer hLayer layer' hLayer' base t0 t1 t2 e f Φ' x σ) := by
  refine sSum_tw hS s.plain s.data h.data L γ δ F layer hLayer layer' hLayer' base t0 t1 t2 e f Φ' ?_ ?_ ?_ ?_ ?_ ?_
  · intro q _ hq
    exact native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hq
  · intro v _ hv
    exact native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v (hS.lower ▸ hv)
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v
  · intro q _ hq
    exact Flower.V5W.coupleIncoh_LF h layer hLayer hspec layer' hLayer' hspec' q hq
  · intro v _ hv
    exact Flower.V5W.treeIncoh_LF h layer hLayer hspec layer' hLayer' hspec' v (hS.lower ▸ hv)
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v

end True

section False
variable (h : LFConstruction s false) {S : Finset (GBranch s.skeleton.tree)} {a b : GBranch s.skeleton.tree}
  (RS : CLRegionData s.skeleton S a b) (hS : SLow s.placement RS)
  (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
  (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
  (layer' : GNode (h.data.forest (s.chosen_plain false)) → ℕ)
  (hLayer' : IsLayering (h.data.garden (s.chosen_plain false)) layer')
  (hspec' : layeredReconstruction h.data (s.chosen_plain false) layer' hLayer' = h.output)

include hS hspec hspec' in
theorem sSum_falseLF {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d)
    (n0 n1 : GNode s.skeleton.tree) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSum RS h.data (s.chosen_plain false) L γ δ F layer' hLayer' base t0 t1 t2 e f n0 n1 Φ =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * clLocalZeta RS *
        ∑' x : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
          sameInt s.plain s.data h.data L γ δ F layer hLayer layer' hLayer' base
            (pairOfLeaf s.skeleton s.plain s.placement.retained) RS t0 t1 t2 e f n0 n1 Φ x σ := by
  refine sSum_same s.plain s.data h.data L γ δ F layer hLayer layer' hLayer' base
    (pairOfLeaf s.skeleton s.plain s.placement.retained) RS t0 t1 t2 e f n0 n1 Φ hS.b_mem_erase hS.p0_mem ?_ ?_ ?_
    (VineEst.selDataEq_LF_false h layer hLayer hspec layer' hLayer' hspec' _ _ (fun q hq => (Finset.mem_erase.mp hq).1)
      (fun v hv => hS.lower ▸ (Finset.mem_erase.mp hv).1)).symm
  · intro q hq
    obtain ⟨hq0, _⟩ := Finset.mem_erase.mp hq
    have := native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hq0
    have hp : s.pairs false q = q := pairOfLeaf_firstLeaf s.skeleton s.plain q
    rw [hp] at this
    exact this.symm
  · intro v hv
    exact (native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v (hS.lower ▸ (Finset.mem_erase.mp hv).1)).symm
  · intro v _
    exact (coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v).symm

end False

end WaveTurbulence.VineEstS5B
