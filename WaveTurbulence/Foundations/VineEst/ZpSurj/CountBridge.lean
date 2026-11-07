/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.NativeEq
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowBridge

/-! # ZP-SURJ: the layer-`p` count bridge -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.Stage1 WaveTurbulence.LGSpine

theorem topBranchCount_eq_sum {w : ℕ} (LG : LayeredGarden w) (p : ℕ) :
    topBranchCount LG p = ∑ b : GBranch LG.garden.tree, if layerAt LG b.1 = p then 1 else 0 := by
  classical
  unfold topBranchCount
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← layerAt_node LG b.toNode]; rfl

theorem topBranchCount_tree (X : RegChain) (LX : LayeredGarden 1) (ζ : ℤˣ)
    (hX : X.DecodesTree LX.garden) (hs : LX.garden.sig 0 = ζ) (p : ℕ) :
    topBranchCount LX p =
      ((((X.plug ζ .leaf).branching).filter (fun q => layerAt LX ((0 : Fin 1), q) = p)).card) := by
  classical
  have hg : LX.garden = decodedTree X ζ := decodedTree_unique X ζ LX.garden hX hs
  rw [topBranchCount_eq_sum, Finset.card_filter]
  have ht : LX.garden.tree 0 = X.plug ζ .leaf := by rw [hg]; rfl
  refine Finset.sum_bij (fun b _ => b.1.2) (fun b _ => ?_) (fun b _ b' _ h => ?_) (fun q hq => ?_) (fun b _ => ?_)
  · have := b.2
    rw [Subsingleton.elim b.1.1 0, ht] at this
    exact this
  · exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) h)
  · refine ⟨⟨((0 : Fin 1), q), by rw [ht]; exact hq⟩, Finset.mem_univ _, rfl⟩
  · have : b.1 = ((0 : Fin 1), b.1.2) := Prod.ext (Subsingleton.elim _ _) rfl
    rw [this]

theorem topBranchCount_couple (Q : RegCpl) (LQ : LayeredGarden 2) (hQ : Q.Decodes LQ.garden) (p : ℕ) :
    topBranchCount LQ p = Stage1.coupleSum Q (fun j r => layerAt LQ (j, r)) p := by
  classical
  have hg : LQ.garden = decodedCouple Q := decodedCouple_unique Q LQ.garden hQ
  rw [topBranchCount_eq_sum]
  unfold Stage1.coupleSum
  obtain ⟨g, l, hl⟩ := LQ
  change g = _ at hg
  subst hg
  rfl

section Raw
variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hL : IsLayering (D.garden hS) layer) (p : ℕ)

theorem raw_tree_bridge (b : GBranch S.tree) :
    rawTreeLayerCount (layeredReconstruction D hS layer hL) D hS p b =
      topBranchCount (nativeChainLayered D hS layer hL b) p := by
  classical
  rw [rawTreeLayerCount_eq, topBranchCount_tree (D.tree b) _ (nodeSign S.sig b.1) (decodedTree_decodes _ _) rfl]
  congr 1
  refine Finset.filter_congr (fun q hq => ?_)
  have hz : q ∈ ((decodedTree (D.tree b) (nodeSign S.sig b.1)).tree 0).nodes :=
    TTree.branching_subset_nodes _ hq
  have := VineEstS4.layerAt_nativeTree D hS layer hL b ((0 : Fin 1), q) hz
  rw [this]; rfl

theorem raw_couple_bridge (q : SourcePair S) :
    rawCoupleLayerCount (layeredReconstruction D hS layer hL) D hS p q =
      topBranchCount (nativeCoupleLayered D hS layer hL q) p := by
  classical
  rw [rawCoupleLayerCount_eq, topBranchCount_couple (D.couple q) _ ?_ p]
  swap
  · rw [nativeCoupleLayered_garden]; exact decodedCouple_decodes _
  refine coupleSum_congr _ _ _ p (fun j r hr => ?_)
  have hz : r ∈ ((decodedCouple (D.couple q)).tree j).nodes := TTree.branching_subset_nodes _ hr
  have := VineEstS4.layerAt_nativeCouple D hS layer hL q (j, r) hz
  rw [this]; rfl

end Raw

section Native2
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
variable {Q : RegCpl} {X : RegChain} {LQ : LayeredGarden 2} {LX : LayeredGarden 1}
variable (hD : ExcDatum s ε Q X LQ LX) (t : TTree)
  (hEO : ChainEmb (midG hD).garden .nil (srcSign s ε) (tA s ε) t)
  (hEN : ChainEmb ((s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε)) X (srcSign s ε) (tA s ε) t)
  (hOutT : GOutT (midG hD).garden ((s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε)) (tA s ε)
    (addrExt (tA s ε) X.lonePath))

include hD hEO hEN hOutT

theorem native_couple_eq :
    nativeCoupleLayered (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε) (outG hD t hEO hEN hOutT).layer
      (outG hD t hEO hEN hOutT).isLayering (s.pairs ε s.exceptional) = LQ := by
  have hFD : (s.finalData ε X Q hD.hX hD.hQ).couple (s.pairs ε s.exceptional) = Q := Function.update_self _ _ _
  have hg : (nativeCoupleLayered (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε) (outG hD t hEO hEN hOutT).layer
      (outG hD t hEO hEN hOutT).isLayering (s.pairs ε s.exceptional)).garden = LQ.garden := by
    refine (nativeCoupleLayered_garden _ _ _ _ _).trans ?_
    rw [hFD]
    exact (decodedCouple_unique Q _ hD.dQ).symm
  refine layered_ext hg ?_
  intro x
  obtain ⟨i, r⟩ := x
  by_cases hx : r ∈ (((nativeCoupleLayered (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε)
      (outG hD t hEO hEN hOutT).layer (outG hD t hEO hEN hOutT).isLayering
      (s.pairs ε s.exceptional)).garden.tree i)).nodes
  · have hx' : r ∈ (LQ.garden.tree i).nodes := by rw [← hg]; exact hx
    have hx'' : r ∈ ((decodedCouple ((s.finalData ε X Q hD.hX hD.hQ).couple (s.pairs ε s.exceptional))).tree i).nodes := by
      exact hx
    have h1 := VineEstS4.layerAt_nativeCouple (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε)
      (outG hD t hEO hEN hOutT).layer (outG hD t hEO hEN hOutT).isLayering (s.pairs ε s.exceptional) (i, r) hx''
    rw [h1]
    exact outG_layer_couple hD t hEO hEN hOutT i r
  · have hx' : r ∉ (LQ.garden.tree i).nodes := by rw [← hg]; exact hx
    have e1 : layerAt (nativeCoupleLayered (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε)
        (outG hD t hEO hEN hOutT).layer (outG hD t hEO hEN hOutT).isLayering (s.pairs ε s.exceptional)) (i, r) = 0 := by
      unfold layerAt; exact dif_neg hx
    have e2 : layerAt LQ (i, r) = 0 := by unfold layerAt; exact dif_neg hx'
    rw [e1, e2]

end Native2

end WaveTurbulence.ZpSurj
