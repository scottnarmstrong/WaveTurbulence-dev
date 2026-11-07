/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVD3
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG14
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG8
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 12: R-GSB leaf-ness (`hleaf1`, `hleaf2` of `unitHk_hind`)

`not_branch_of_nodeClk_inl_shape`: `not_branch_of_nodeClk_inl` for an arbitrary splice shape.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf

variable {w : ℕ}

theorem not_branch_of_nodeClk_inl_shape {S Gsb : Garden w} {J : Type} [Fintype J] [DecidableEq J]
    {blk : J → CLBlock S} (Φ : SpliceShape blk Gsb) (hd : Disj blk) (j : J) (k : Fin 4) (r : Fin w)
    (hc : nodeClk Gsb (Φ.hmom hd j k) = Sum.inl r) :
    (bnodes (blk j) k).1.2 ∉ (S.tree (bnodes (blk j) k).1.1).branching := by
  intro h
  set b' : GBranch S.tree := ⟨(bnodes (blk j) k).1, h⟩ with hb'
  have hbn : b'.toNode = bnodes (blk j) k := rfl
  have hr : Ret blk b'.toNode := by
    rw [hbn]; exact Φ.ret_bdryNode hd j k
  obtain ⟨c, hcb⟩ := Φ.exists_br hr
  have h1 : Φ.node c.toNode = Φ.node (Φ.hmom hd j k) := by
    rw [← Φ.br_node, hcb, hbn, Φ.node_hmom]
  have h2 := Φ.inj h1
  rw [← h2] at hc
  have hcc : nodeClk Gsb c.toNode = Sum.inr c := by
    unfold nodeClk
    rw [dif_pos (show c.toNode.1.2 ∈ (Gsb.tree c.toNode.1.1).branching from c.2)]
    rfl
  rw [hcc] at hc
  exact absurd hc (by simp)


section Local
variable {S : Garden w} (hM : S.molecule.IsMolecule) (σ : Prescription S)
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

theorem unit_hleaf_aux (hp : IsPrimeGarden S) {p : ℕ} {kind : Bool} (j : Fin (unitBlocks S σ).length) (k : Fin 4) (r : Fin w)
    (hflag : nodeClk (stSt S σ).G ((stShape hM σ).hmom (unitBlk_disj hM σ) j k) = Sum.inl r)
    (x : Σ X : FamilyReconstruction w (assemblySourceFamily (alignedAssembly hM σ j)).CoreIndex,
      ChainAt X.skeleton X.family)
    (hx : x ∈ canonFinsetK p kind (startState (alignedAssembly hM σ j) D hS layer hLayer)
      (chainStart (alignedAssembly hM σ j))) :
    (bnodes (⟨x.2.U, x.2.a, x.2.b, x.2.block, x.2.cl⟩ : CLBlock x.1.skeleton) k).1.2 ∉
      (x.1.skeleton.tree (bnodes (⟨x.2.U, x.2.a, x.2.b, x.2.block, x.2.cl⟩ : CLBlock x.1.skeleton) k).1.1).branching := by
  obtain ⟨X, c⟩ := x
  obtain ⟨N, hN, hR⟩ := (mem_canonFinsetK hp).mp hx
  obtain ⟨Z, hZb, hZe⟩ := batch_lift (e := (unitsSplit (alignedAssembly hM σ)).emb j)
    ((unitsSplit (alignedAssembly hM σ)).inj j) hR.batch
    (X := unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer) rfl
  obtain ⟨vs, hRZ⟩ := batch_reachU (Qm := (unitsSplit (alignedAssembly hM σ)).Q) hZb
    (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ))
  have hN' : N.Nodup := perm_univ_nodup hN
  have hproj := ReachU.proj (e := (unitsSplit (alignedAssembly hM σ)).emb j)
    (he := (unitsSplit (alignedAssembly hM σ)).inj j) j ((unitsSplit (alignedAssembly hM σ)).q_emb j) N hRZ
  subst hZe
  have hc := Reach.region_unique hN' hN' hR hproj
  subst hc
  have hn : (N.map ((unitsSplit (alignedAssembly hM σ)).emb j)).Nodup :=
    hN'.map ((unitsSplit (alignedAssembly hM σ)).inj j)
  have hm := congrFun (congrFun (commonShape_hmom hM σ D hS layer hLayer hRZ hn) j) k
  refine not_branch_of_nodeClk_inl_shape (commonShape hM σ D hS layer hLayer hRZ hn)
    (member_disj hM σ D hS layer hLayer hRZ hn) j k r ?_
  rw [hm]
  exact hflag

theorem unit_hleaf1 (hp : IsPrimeGarden S) {p : ℕ} (j : Fin (unitBlocks S σ).length)
    (h1 : leafFlag hM σ j 1) :
    ∀ x ∈ canonFinsetK p (objKind w) (startState (alignedAssembly hM σ j) D hS layer hLayer)
      (chainStart (alignedAssembly hM σ j)),
      (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).positive).1.2 ∉
        (x.1.skeleton.tree (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).positive).1.1).branching := by
  intro x hx
  obtain ⟨r, hr⟩ := (leafFlag_one hM σ j).mp h1
  exact unit_hleaf_aux hM σ D hS layer hLayer hp j 2 r hr x hx

theorem unit_hleaf2 (hp : IsPrimeGarden S) {p : ℕ} (j : Fin (unitBlocks S σ).length)
    (h2 : leafFlag hM σ j 2) :
    ∀ x ∈ canonFinsetK p (objKind w) (startState (alignedAssembly hM σ j) D hS layer hLayer)
      (chainStart (alignedAssembly hM σ j)),
      (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).negative).1.2 ∉
        (x.1.skeleton.tree (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).negative).1.1).branching := by
  intro x hx
  obtain ⟨r, hr⟩ := (leafFlag_two hM σ j).mp h2
  exact unit_hleaf_aux hM σ D hS layer hLayer hp j 3 r hr x hx

end Local

end WaveTurbulence.Represents
