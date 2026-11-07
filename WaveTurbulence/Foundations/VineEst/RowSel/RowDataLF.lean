/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.RowData
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw9Native

/-! # V5W-B (ruling F2): the incoherency of the ordinary rows under an LF construction, copied by source

Verbatim copy (statements, proofs, namespace `WaveTurbulence.Flower.V5W` unchanged) of V5W-0's
`Flower/V5W/RowData.lean` (sha256 `7de6c466f12ddcffe94a8c1399fb30291e6d94ec2b1d8440e60b0d561bfda5e2`), section `LF`
(lines 118–140): `treeIncoh_LF`, `coupleIncoh_LF`.  An LF construction keeps the incoherency of every ordinary row
(rows unchanged by `tree_other`/`couple_other`, native layered rows unchanged by `native_tree_eq`/`native_couple_eq`).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Links
  WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree

/-! ## The incoherency of the ordinary rows under an LF construction -/

section LF
variable {w : ℕ} {p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
  (h : LFConstruction s ε)
  (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
  (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
  (layer' : GNode (h.data.forest (s.chosen_plain ε)) → ℕ) (hLayer' : IsLayering (h.data.garden (s.chosen_plain ε)) layer')
  (hspec' : layeredReconstruction h.data (s.chosen_plain ε) layer' hLayer' = h.output)

include hspec hspec' in
theorem treeIncoh_LF (b : GBranch s.skeleton.tree) (hb : b ≠ s.placement.lower) :
    treeIncoh h.data (s.chosen_plain ε) layer' hLayer' (s.branches ε b) = treeIncoh s.data s.plain layer hLayer b := by
  unfold treeIncoh
  rw [native_tree_eq h layer hLayer hspec layer' hLayer' hspec' b hb, h.tree_other b hb]

include hspec hspec' in
theorem coupleIncoh_LF (q : SourcePair s.skeleton) (hq : q ≠ s.exceptional) :
    coupleIncoh h.data (s.chosen_plain ε) layer' hLayer' (s.pairs ε q) = coupleIncoh s.data s.plain layer hLayer q := by
  unfold coupleIncoh
  rw [native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hq, h.couple_other q hq]

end LF

end WaveTurbulence.Flower.V5W
