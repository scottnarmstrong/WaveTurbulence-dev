/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Cls3Inv
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Cls2Comb
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw9Native

/-! # Class combinatorics, part 3: row extensionality (V5 Step 4b, WP-A, injectivity)

`Compat A i hS eB eP D W`: the reconstruction data `D` and the layered garden `W` over the plain skeleton `S` agree with the state `A`
on every ordinary row (rows other than the exceptional couple and the tree at the lower joint of the member `i`), up to the branch / pair
bijections `eB`, `eP`, and on all layers there.  An LF operation at `i` (any choice) gives a `Compat`; so does `A` itself (`eB = eP = id`).
`Compat.layered_eq`: two `Compat` objects with the same exceptional native layered rows are equal (`Stage1.layered_eq_of_classes`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {ι : Type*}

/-- The data `D`, the layered garden `W` and its layering over `S` agree with `A` on the ordinary rows of the member `i`. -/
structure Compat (p : ℕ) (A : FamilyReconstruction w ι) (i : ι) {S : Garden w} (hS : S.IsPlain)
    (eB : GBranch A.skeleton.tree ≃ GBranch S.tree) (eP : SourcePair A.skeleton ≃ SourcePair S)
    (D : ReconstructionData S) (W : LayeredGarden w) : Type where
  layer : GNode (D.forest hS) → ℕ
  hlay : IsLayering (D.garden hS) layer
  spec : layeredReconstruction D hS layer hlay = W
  decodes : D.Decodes hS W.garden
  crit : W.CanonCriterion p
  sign_other : ∀ b, b ≠ (A.family.placement i).lower → nodeSign S.sig (eB b).1 = nodeSign A.skeleton.sig b.1
  tree_other : ∀ b, b ≠ (A.family.placement i).lower → D.tree (eB b) = A.data.tree b
  couple_other : ∀ q, q ≠ pairOfLeaf A.skeleton A.plain (A.family.placement i).retained →
    D.couple (eP q) = A.data.couple q
  core : ∀ b, layerAt A.layered (A.data.corePosition b) = layerAt W (D.corePosition (eB b))
  treeL : ∀ b, b ≠ (A.family.placement i).lower →
    ∀ q ∈ ((A.data.tree b).plug (nodeSign A.skeleton.sig b.1) .leaf).nodes,
      layerAt A.layered (addrExt (inflatedPosition A.skeleton A.data.tree b.toNode) q) =
        layerAt W (addrExt (inflatedPosition S D.tree (eB b).toNode) q)
  coupleL : ∀ q, q ≠ pairOfLeaf A.skeleton A.plain (A.family.placement i).retained →
    ∀ (j : Fin 2) (r : Path), r ∈ ((decodedCouple (A.data.couple q)).tree j).nodes →
      layerAt A.layered (addrExt (coupleRoot A.data A.plain q j) r) =
        layerAt W (addrExt (coupleRoot D hS (eP q) j) r)

variable {p : ℕ}

theorem Compat.layered_eq {A : FamilyReconstruction w ι} {i : ι} {S : Garden w} {hS : S.IsPlain}
    {eB : GBranch A.skeleton.tree ≃ GBranch S.tree} {eP : SourcePair A.skeleton ≃ SourcePair S}
    {D D' : ReconstructionData S} {W W' : LayeredGarden w}
    (h : Compat p A i hS eB eP D W) (h' : Compat p A i hS eB eP D' W')
    (hexT : nativeChainLayered D hS h.layer h.hlay (eB (A.family.placement i).lower) =
      nativeChainLayered D' hS h'.layer h'.hlay (eB (A.family.placement i).lower))
    (hexC : nativeCoupleLayered D hS h.layer h.hlay
        (eP (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)) =
      nativeCoupleLayered D' hS h'.layer h'.hlay
        (eP (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained))) : W = W' := by
  have hDT : D.tree = D'.tree := by
    funext c
    obtain ⟨b, rfl⟩ := eB.surjective c
    by_cases hb : b = (A.family.placement i).lower
    · subst hb
      have hg := congrArg LayeredGarden.garden hexT
      change decodedTree _ _ = decodedTree _ _ at hg
      have := decodedTree_wf_injective (nodeSign S.sig (eB (A.family.placement i).lower).1)
        (a₁ := ⟨D.tree _, D.tree_wf _⟩) (a₂ := ⟨D'.tree _, D'.tree_wf _⟩) hg
      exact congrArg Subtype.val this
    · exact (h.tree_other b hb).trans (h'.tree_other b hb).symm
  have hDC : D.couple = D'.couple := by
    funext c
    obtain ⟨q, rfl⟩ := eP.surjective c
    by_cases hq : q = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained
    · subst hq
      have hg := congrArg LayeredGarden.garden hexC
      rw [nativeCoupleLayered_garden, nativeCoupleLayered_garden] at hg
      have := decodedCouple_wf_injective (a₁ := ⟨D.couple _, D.couple_wf _⟩) (a₂ := ⟨D'.couple _, D'.couple_wf _⟩) hg
      exact congrArg Subtype.val this
    · exact (h.couple_other q hq).trans (h'.couple_other q hq).symm
  have hD : D = D' := ReconstructionData.ext_tree_couple D D' hDT hDC
  subst hD
  refine Stage1.layered_eq_of_classes (p := p) D hS W W' h.decodes h'.decodes h.crit h'.crit ?_ ?_ ?_
  · intro b'
    obtain ⟨b, rfl⟩ := eB.surjective b'
    exact (h.core b).symm.trans (h'.core b)
  · intro b' q hq
    obtain ⟨b, rfl⟩ := eB.surjective b'
    by_cases hb : b = (A.family.placement i).lower
    · subst hb
      have hz : q ∈ ((decodedTree (D.tree (eB (A.family.placement i).lower))
          (nodeSign S.sig (eB (A.family.placement i).lower).1)).tree 0).nodes :=
        TTree.branching_subset_nodes _ hq
      have e1 := layerAt_nativeTree D hS h.layer h.hlay _ ((0 : Fin 1), q) hz
      have e2 := layerAt_nativeTree D hS h'.layer h'.hlay _ ((0 : Fin 1), q) hz
      rw [h.spec] at e1
      rw [h'.spec] at e2
      have e3 := congrArg (fun g => layerAt g ((0 : Fin 1), q)) hexT
      exact e1.symm.trans (e3.trans e2)
    · have hq' : q ∈ ((A.data.tree b).plug (nodeSign A.skeleton.sig b.1) .leaf).nodes := by
        rw [← h.tree_other b hb, ← h.sign_other b hb]
        exact TTree.branching_subset_nodes _ hq
      exact (h.treeL b hb q hq').symm.trans (h'.treeL b hb q hq')
  · intro qq j r hr
    obtain ⟨q, rfl⟩ := eP.surjective qq
    by_cases hq : q = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained
    · subst hq
      have hz : r ∈ ((decodedCouple (D.couple (eP (pairOfLeaf A.skeleton A.plain
          (A.family.placement i).retained)))).tree j).nodes := TTree.branching_subset_nodes _ hr
      have e1 := layerAt_nativeCouple D hS h.layer h.hlay _ (j, r) hz
      have e2 := layerAt_nativeCouple D hS h'.layer h'.hlay _ (j, r) hz
      rw [h.spec] at e1
      rw [h'.spec] at e2
      have e3 := congrArg (fun g => layerAt g (j, r)) hexC
      exact e1.symm.trans (e3.trans e2)
    · have hr' : r ∈ ((decodedCouple (A.data.couple q)).tree j).nodes := by
        rw [← h.couple_other q hq]
        exact TTree.branching_subset_nodes _ hr
      exact (h.coupleL q hq j r hr').symm.trans (h'.coupleL q hq j r hr')

end WaveTurbulence.VineEstS4
