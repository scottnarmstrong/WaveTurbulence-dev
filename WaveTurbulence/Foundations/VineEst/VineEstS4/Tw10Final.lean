/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw9Native
public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLF

/-! # K^T twist invariance (V5 Step 4b, step 3): the LF-level statement

`clLocalKernel_twist_LF`: for a TRUE-choice LF construction `h` of a source `s` and a CL block `T` whose upper joint is the
lower joint of the placement of `s`, the kernel of the output garden at the transported block is the kernel of the source at
`T` with the first two boundary momenta exchanged.  This is the `K^T` invariance of TARGET `vineest` Step 4 /
Remark `twistexplain` (d): `K^{T'}_{G_p}(t; e, f, g, h) = K^T_G(t; f, e, g, h)`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG) (h : LFConstruction s true)

/-- **K^T twist invariance.** -/
theorem clLocalKernel_twist_LF {T : Finset (GBranch s.skeleton.tree)} {z : GBranch s.skeleton.tree}
    (hB : s.skeleton.molecule.IsBlock T s.placement.lower z) (hCL : Mole.CLParentPattern s.skeleton T s.placement.lower z)
    (R : CLRegionData s.skeleton T s.placement.lower z) (R' : TwRegion s.placement T z)
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain true)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain true)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain true) layer' hLayer' = h.output)
    {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    clLocalKernel h.data (s.chosen_plain true) R' L γ δ F layer' hLayer' base t0 t1 t2 e f g k =
      clLocalKernel s.data s.plain R L γ δ F layer hLayer base t0 t1 t2 f e g k := by
  refine clLocalKernel_twist s.placement hB hCL R R' s.plain s.data h.data L γ δ F layer hLayer layer' hLayer' base
    t0 t1 t2 e f g k ?_ ?_ ?_ ?_ ?_
  · intro q hq
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hne : q ≠ s.exceptional := by
      intro hqe
      have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
      subst hqe'
      have hq' := pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained
      rcases hq' with hq' | hq'
      · exact not_internal_retained s.placement hB hCL (hq' ▸ hint)
      · exact not_internal_pair s.placement hB hCL (hq' ▸ hint)
    exact native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hne
  · intro v hv
    have hvl : v ≠ s.placement.lower := (Finset.mem_erase.mp hv).1
    exact native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v hvl
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v
  · intro q hq
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hne : q ≠ s.exceptional := by
      intro hqe
      have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
      subst hqe'
      have hq' := pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained
      rcases hq' with hq' | hq'
      · exact not_internal_retained s.placement hB hCL (hq' ▸ hint)
      · exact not_internal_pair s.placement hB hCL (hq' ▸ hint)
    exact Flower.V5W.coupleIncoh_LF h layer hLayer hspec layer' hLayer' hspec' q hne
  · intro v hv
    have hvl : v ≠ s.placement.lower := (Finset.mem_erase.mp hv).1
    exact Flower.V5W.treeIncoh_LF h layer hLayer hspec layer' hLayer' hspec' v hvl

end WaveTurbulence.VineEstS4
