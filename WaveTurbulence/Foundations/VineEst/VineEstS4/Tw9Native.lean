/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw8Kernel
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowCanon
public import WaveTurbulence.Foundations.VineEst.VineEstS4.OrderStep
public import WaveTurbulence.Foundations.VineEst.VineEstS4.AtomLayers

/-! # K^T twist invariance, native layered objects of the ordinary rows (V5 Step 4b, step 3, part 9)

For an `LFConstruction h` of a source `s`, the native layered couple (resp. tree) of every ordinary row (`q ≠ s.exceptional`,
resp. `b ≠ s.placement.lower`) is the same layered garden for the source and the output reconstruction
(`native_couple_eq`, `native_tree_eq`): the replacement code is unchanged (`couple_other`, `tree_other`) and the layers are
carried by `ordinaryCoupleLayers`, `ordinaryTreeLayers`.  `coreLayer_eq`: the atom layers.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree

theorem layeredGarden_eq_of_layerAt {n : ℕ} (g1 g2 : LayeredGarden n) (hg : g1.garden = g2.garden)
    (h : ∀ z, layerAt g1 z = layerAt g2 z) : g1 = g2 := by
  obtain ⟨a1, l1, i1⟩ := g1
  obtain ⟨a2, l2, i2⟩ := g2
  change a1 = a2 at hg
  subst hg
  have : l1 = l2 := by
    funext x
    have := h x.1
    rwa [layerAt_node ⟨a1, l1, i1⟩ x, layerAt_node ⟨a1, l2, i2⟩ x] at this
  subst this
  rfl

variable {w : ℕ}

section Native
variable {p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool} (h : LFConstruction s ε)
  (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
  (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
  (layer' : GNode (h.data.forest (s.chosen_plain ε)) → ℕ) (hLayer' : IsLayering (h.data.garden (s.chosen_plain ε)) layer')
  (hspec' : layeredReconstruction h.data (s.chosen_plain ε) layer' hLayer' = h.output)

include hspec hspec' in
theorem native_couple_eq (q : SourcePair s.skeleton) (hq : q ≠ s.exceptional) :
    nativeCoupleLayered h.data (s.chosen_plain ε) layer' hLayer' (s.pairs ε q) =
      nativeCoupleLayered s.data s.plain layer hLayer q := by
  have hc := h.couple_other q hq
  refine layeredGarden_eq_of_layerAt _ _ ?_ ?_
  · rw [nativeCoupleLayered_garden, nativeCoupleLayered_garden, hc]
  · rintro ⟨i, r⟩
    by_cases hz : r ∈ ((decodedCouple (s.data.couple q)).tree i).nodes
    · have hz' : r ∈ ((decodedCouple (h.data.couple (s.pairs ε q))).tree i).nodes := by rw [hc]; exact hz
      rw [layerAt_nativeCouple h.data (s.chosen_plain ε) layer' hLayer' (s.pairs ε q) (i, r) hz',
        layerAt_nativeCouple s.data s.plain layer hLayer q (i, r) hz, hspec', hspec]
      exact (h.ordinaryCoupleLayers q hq i r hz).symm
    · have hz' : r ∉ ((decodedCouple (h.data.couple (s.pairs ε q))).tree i).nodes := by rw [hc]; exact hz
      have e1 : layerAt (nativeCoupleLayered h.data (s.chosen_plain ε) layer' hLayer' (s.pairs ε q)) (i, r) = 0 := by
        unfold layerAt
        rw [dif_neg]
        rw [nativeCoupleLayered_garden]; exact hz'
      have e2 : layerAt (nativeCoupleLayered s.data s.plain layer hLayer q) (i, r) = 0 := by
        unfold layerAt
        rw [dif_neg]
        rw [nativeCoupleLayered_garden]; exact hz
      rw [e1, e2]

include hspec hspec' in
theorem native_tree_eq (b : GBranch s.skeleton.tree) (hb : b ≠ s.placement.lower) :
    nativeChainLayered h.data (s.chosen_plain ε) layer' hLayer' (s.branches ε b) =
      nativeChainLayered s.data s.plain layer hLayer b := by
  have ht := h.tree_other b hb
  have hs := s.ordinary_branch_sign ε b hb
  refine layeredGarden_eq_of_layerAt _ _ ?_ ?_
  · change decodedTree (h.data.tree (s.branches ε b)) (nodeSign (s.chosen ε).sig (s.branches ε b).1) =
      decodedTree (s.data.tree b) (nodeSign s.skeleton.sig b.1)
    rw [ht, hs]
  · rintro ⟨i, r⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    by_cases hz : r ∈ ((s.data.tree b).plug (nodeSign s.skeleton.sig b.1) .leaf).nodes
    · have hz1 : r ∈ ((decodedTree (s.data.tree b) (nodeSign s.skeleton.sig b.1)).tree 0).nodes := hz
      have hz2 : r ∈ ((decodedTree (h.data.tree (s.branches ε b)) (nodeSign (s.chosen ε).sig (s.branches ε b).1)).tree 0).nodes := by
        rw [ht, hs]; exact hz1
      rw [layerAt_nativeTree h.data (s.chosen_plain ε) layer' hLayer' (s.branches ε b) (0, r) hz2,
        layerAt_nativeTree s.data s.plain layer hLayer b (0, r) hz1, hspec', hspec]
      exact (h.ordinaryTreeLayers b hb r hz).symm
    · have e1 : layerAt (nativeChainLayered h.data (s.chosen_plain ε) layer' hLayer' (s.branches ε b)) (0, r) = 0 := by
        unfold layerAt
        rw [dif_neg]
        change ¬ r ∈ ((decodedTree (h.data.tree (s.branches ε b)) (nodeSign (s.chosen ε).sig (s.branches ε b).1)).tree 0).nodes
        rw [ht, hs]; exact hz
      have e2 : layerAt (nativeChainLayered s.data s.plain layer hLayer b) (0, r) = 0 := by
        unfold layerAt
        rw [dif_neg]
        exact hz
      rw [e1, e2]

include hspec hspec' in
theorem coreLayer_eq (v : GBranch s.skeleton.tree) :
    layer' (h.data.coreBranch (s.chosen_plain ε) (s.branches ε v)).toNode =
      layer (s.data.coreBranch s.plain v).toNode := by
  have e1 : layer (s.data.coreBranch s.plain v).toNode =
      layerAt (layeredReconstruction s.data s.plain layer hLayer) (s.data.corePosition v) :=
    (layerAt_node (layeredReconstruction s.data s.plain layer hLayer) (s.data.coreBranch s.plain v).toNode).symm
  have e2 : layer' (h.data.coreBranch (s.chosen_plain ε) (s.branches ε v)).toNode =
      layerAt (layeredReconstruction h.data (s.chosen_plain ε) layer' hLayer')
        (h.data.corePosition (s.branches ε v)) :=
    (layerAt_node (layeredReconstruction h.data (s.chosen_plain ε) layer' hLayer')
      (h.data.coreBranch (s.chosen_plain ε) (s.branches ε v)).toNode).symm
  rw [e1, e2, hspec, hspec']
  exact (h.coreLayers v).symm

end Native

end WaveTurbulence.VineEstS4
