/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVC3
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 12: per-member facts (F-lay)

`member_core_layer`: along the actual batch map `e` of a class member `y`, the layer of the core of the skeleton branch `e b`
(for the member's own layering `stateLayer`) is the representative's layer of the core of `b`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign

variable {w p : ℕ} {kind : Bool}

theorem coreLayer_of_spec {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (LG : LayeredGarden w)
    (hspec : layeredReconstruction D hS layer hLayer = LG) (hd : D.Decodes hS LG.garden) (v : GBranch S.tree) :
    RegRed.coreLayer LG D hS hd v = layer (D.coreBranch hS v).toNode := by
  subst hspec
  rfl

theorem member_core_layer (a : PrescribedPrimeGarden w) (y : UState w (unitsSplit (sourceAssembly a)))
    (M : List (UnitsIndex (sourceAssembly a)))
    (hr : ReachU p kind (unitsSplit (sourceAssembly a)).Q M (sourceStart a) (sourceUnits a) y.1 y.2)
    (b : GBranch a.prime.skeleton.tree) :
    stateLayer y.1 (y.1.data.coreBranch y.1.plain ((batchMolIso hr.batch).e b)).toNode =
      sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode := by
  have h := BatchIso.coreLayer (batchMolIso_spec hr.batch) b
  rw [coreLayer_of_spec y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) y.1.layered
    (stateLayer_spec y.1)] at h
  rw [h]
  exact coreLayer_of_spec a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    (sourceStart a).layered rfl _ b


theorem sourceShape_br_eq {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (y : UState (2 * R) (unitsSplit (sourceAssembly a)))
    (hy : y ∈ sourceClass a p kind) (c : GBranch a.fullProfile.piece.gap.garden.tree) :
    ∃ (M : List (UnitsIndex (sourceAssembly a)))
      (hr : ReachU p kind (unitsSplit (sourceAssembly a)).Q M (sourceStart a) (sourceUnits a) y.1 y.2),
      (sourceShape a y hy).br c = (batchMolIso hr.batch).e ((stSt a.prime.skeleton a.totalSigma).M.ob c) := by
  obtain ⟨hn, hr⟩ := (class_member_trace (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec
  exact ⟨_, hr, commonShape_br _ _ _ _ _ _ hr hn c⟩

theorem sourceShape_core_layer {R : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind)
    (c : GBranch a.fullProfile.piece.gap.garden.tree) :
    stateLayer y.1 (y.1.data.coreBranch y.1.plain ((sourceShape a y hy).br c)).toNode =
      a.fullProfile.piece.layer c := by
  obtain ⟨M, hr, h⟩ := sourceShape_br_eq a y hy c
  rw [h, member_core_layer a y M hr]
  exact (coreLayer_of_spec a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
    (sourceLayer_reconstructs a) a.prime.decodes _).symm


theorem sourceShape_trace {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (y : UState (2 * R) (unitsSplit (sourceAssembly a)))
    (hy : y ∈ sourceClass a p kind) :
    ∃ (M : List (UnitsIndex (sourceAssembly a)))
      (hr : ReachU p kind (unitsSplit (sourceAssembly a)).Q M (sourceStart a) (sourceUnits a) y.1 y.2),
      (∀ c : GBranch a.fullProfile.piece.gap.garden.tree,
        (sourceShape a y hy).br c = (batchMolIso hr.batch).e ((stSt a.prime.skeleton a.totalSigma).M.ob c)) ∧
      ∀ j : Fin (unitBlocks a.prime.skeleton a.totalSigma).length,
        (y.2 j).blk.b = (batchMolIso hr.batch).e
          (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma j).lower := by
  obtain ⟨hn, hr⟩ := (class_member_trace (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec
  refine ⟨_, hr, fun c => commonShape_br _ _ _ _ _ _ hr hn c, fun j => ?_⟩
  exact (reachU_coordinates hr hn (batchMolIso_spec hr.batch) j).2.2

theorem profileShape_core_layer {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (c : GBranch a.fullProfile.piece.gap.garden.tree) :
    sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 ((profileShape a).br c)).toNode =
      a.fullProfile.piece.layer c :=
  (coreLayer_of_spec a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
    (sourceLayer_reconstructs a) a.prime.decodes _).symm

theorem sourceShape_clkLayer {R : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind)
    (hG : a.fullProfile.piece.gap.garden.IsPlain) (s : ReplacementSlot a.fullProfile.piece.gap.garden) (i : Fin 2) :
    clkLayer p (fun b => stateLayer y.1 (y.1.data.coreBranch y.1.plain b).toNode)
        (argSrc y.1.plain ((sourceShape a y hy).iota y.1.plain hG s) i) =
      clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        (argSrc a.prime.prime.1 ((profileShape a).iota a.prime.prime.1 hG s) i) := by
  obtain ⟨M, hr, hbr, hlow⟩ := sourceShape_trace a y hy
  have hroute := congrFun (congrFun (sourceShape_route a y hy hG) s) i
  rcases hr' : (profileShape a).route a.prime.prime.1 hG s i with y' | j
  · rw [hr'] at hroute
    rw [(sourceShape a y hy).route_inl _ hG hroute, (profileShape a).route_inl _ hG hr']
    rcases y' with r | c
    · rfl
    · show stateLayer y.1 (y.1.data.coreBranch y.1.plain ((sourceShape a y hy).br c)).toNode =
        sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 ((profileShape a).br c)).toNode
      rw [sourceShape_core_layer, profileShape_core_layer]
  · rw [hr'] at hroute
    rw [(sourceShape a y hy).route_inr _ hG hroute, (profileShape a).route_inr _ hG hr']
    show stateLayer y.1 (y.1.data.coreBranch y.1.plain (y.2 j).blk.b).toNode =
      sourceLayer a (a.prime.data.coreBranch a.prime.prime.1
        (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma j).lower).toNode
    rw [hlow j]
    exact member_core_layer a y M hr _

end WaveTurbulence.Represents
