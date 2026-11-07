/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLF
public import WaveTurbulence.Foundations.VineEst.RowSel.RowTransport

/-! # V5W-B (ruling F2): a FALSE-choice LF construction keeps the selection data of the ordinary rows

`selDataEq_LF_false`: the output and source data of a FALSE-choice LF construction (same skeleton) have the same
incoherency on every ordinary row (`coupleIncoh_LF`, `treeIncoh_LF`) and the same core layers (`coreLayer_eq`), i.e.
`SelDataEq` on every set of non-exceptional pairs and non-lower branches.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEst
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree

variable {w : ℕ} {p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG}

theorem selDataEq_LF_false (h : LFConstruction s false)
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain false)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain false)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain false) layer' hLayer' = h.output)
    (Ps : Finset (SourcePair s.skeleton)) (Vs : Finset (GBranch s.skeleton.tree))
    (hP : ∀ q ∈ Ps, q ≠ s.exceptional) (hV : ∀ v ∈ Vs, v ≠ s.placement.lower) :
    SelDataEq s.plain h.data s.data layer' hLayer' layer hLayer Ps Vs := by
  refine ⟨fun q hq => ?_, fun v hv => Flower.V5W.treeIncoh_LF h layer hLayer hspec layer' hLayer' hspec' v (hV v hv),
    fun v => coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v⟩
  have := Flower.V5W.coupleIncoh_LF h layer hLayer hspec layer' hLayer' hspec' q (hP q hq)
  have hp : s.pairs false q = q := pairOfLeaf_firstLeaf s.skeleton s.plain q
  rwa [hp] at this

end WaveTurbulence.VineEst
