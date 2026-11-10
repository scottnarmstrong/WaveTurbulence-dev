/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnits.WMember
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WClass
public import WaveTurbulence.Foundations.Flower.MkUnits.UnitGap

/-! # MK-UNITS: the hinge data of the weighted units at a marking

Stage1WVine's `unit_hinge_dataW` (main's `unit_hinge_data` on the on-chain route `hinge_units_const →
exists_hinge_data_mod_ck_w`, uclock Rev. 1 U-F6, through Stage1WVine's generic `hinge_units_constW`) for the run
assembly `sourceAssemblyMk a mk` of the representative:
* G1 (time box): main's `g1_unitsMk`, `qOut_one_eq_layMk`, `qOut_two_eq_layMk`, `hqle_unitsMk`;
* G2 (`outSet`): `mem_outSet_of_gsbNMk` (`UnitGap`, the runs' gap from the σ-restriction);
* leaf independence: main's `unit_hleaf1`/`unit_hleaf2` at a marking (`unit_hleaf1Mk`, `unit_hleaf2Mk`), through the
  common shape of the lifted batch with the image marking.

Adapted from `Flower/Stage1WVine/WHinge2.lean` and main's `Stage1/Represents/RepVD4.lean` (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnits
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS5C
  VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.Represents
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.Flower.Stage1WVine

/-! ## Leaf independence of the unit class kernels at a marking -/

section Local
variable {w : ℕ} {S : Garden w} (hM : S.molecule.IsMolecule) (σ : Prescription S) (Mk : Set (CLVine S))
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

theorem unit_hleaf_auxMk (hp : IsPrimeGarden S) {p : ℕ} {kind : Bool} (j : Fin (unitBlocks S σ Mk).length)
    (k : Fin 4) (r : Fin w)
    (hflag : nodeClk (stSt S σ Mk).G ((stShape hM σ Mk).hmom (unitBlkMk_disj hM σ Mk) j k) = Sum.inl r)
    (x : Σ X : FamilyReconstruction w (assemblySourceFamily (alignedAssemblyMk hM σ Mk j)).CoreIndex,
      ChainAt X.skeleton X.family)
    (hx : x ∈ canonFinsetK p kind (startState (alignedAssemblyMk hM σ Mk j) D hS layer hLayer)
      (chainStart (alignedAssemblyMk hM σ Mk j))) :
    (bnodes (⟨x.2.U, x.2.a, x.2.b, x.2.block, x.2.cl⟩ : CLBlock x.1.skeleton) k).1.2 ∉
      (x.1.skeleton.tree
        (bnodes (⟨x.2.U, x.2.a, x.2.b, x.2.block, x.2.cl⟩ : CLBlock x.1.skeleton) k).1.1).branching := by
  obtain ⟨X, c⟩ := x
  obtain ⟨N, hN, hR⟩ := (mem_canonFinsetK hp).mp hx
  obtain ⟨Z, hZb, hZe⟩ := batch_lift (e := (unitsSplit (alignedAssemblyMk hM σ Mk)).emb j)
    ((unitsSplit (alignedAssemblyMk hM σ Mk)).inj j) hR.batch
    (X := unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer) rfl
  obtain ⟨vs, hRZ⟩ := batch_reachU (Qm := (unitsSplit (alignedAssemblyMk hM σ Mk)).Q) hZb
    (unitsRegion (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk))
  have hN' : N.Nodup := perm_univ_nodup hN
  have hproj := ReachU.proj (e := (unitsSplit (alignedAssemblyMk hM σ Mk)).emb j)
    (he := (unitsSplit (alignedAssemblyMk hM σ Mk)).inj j) j ((unitsSplit (alignedAssemblyMk hM σ Mk)).q_emb j) N hRZ
  subst hZe
  have hc := Reach.region_unique hN' hN' hR hproj
  subst hc
  have hn : (N.map ((unitsSplit (alignedAssemblyMk hM σ Mk)).emb j)).Nodup :=
    hN'.map ((unitsSplit (alignedAssemblyMk hM σ Mk)).inj j)
  have hm := congrFun (congrFun (commonShape_hmomMk hM σ D hS layer hLayer hRZ hn
    (markTransported_imageMark _ Mk)) j) k
  refine not_branch_of_nodeClk_inl_shape (commonShapeMk hM σ D hS layer hLayer hRZ hn
    (markTransported_imageMark _ Mk)) (member_disjMk hM σ D hS layer hLayer hRZ hn) j k r ?_
  rw [hm]
  exact hflag

theorem unit_hleaf1Mk (hp : IsPrimeGarden S) {p : ℕ} (j : Fin (unitBlocks S σ Mk).length)
    (h1 : leafFlag hM σ j 1) :
    ∀ x ∈ canonFinsetK p (objKind w) (startState (alignedAssemblyMk hM σ Mk j) D hS layer hLayer)
      (chainStart (alignedAssemblyMk hM σ Mk j)),
      (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).positive).1.2 ∉
        (x.1.skeleton.tree (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).positive).1.1).branching := by
  intro x hx
  obtain ⟨r, hr⟩ := (leafFlag_oneMk hM σ j).mp h1
  exact unit_hleaf_auxMk hM σ Mk D hS layer hLayer hp j 2 r hr x hx

theorem unit_hleaf2Mk (hp : IsPrimeGarden S) {p : ℕ} (j : Fin (unitBlocks S σ Mk).length)
    (h2 : leafFlag hM σ j 2) :
    ∀ x ∈ canonFinsetK p (objKind w) (startState (alignedAssemblyMk hM σ Mk j) D hS layer hLayer)
      (chainStart (alignedAssemblyMk hM σ Mk j)),
      (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).negative).1.2 ∉
        (x.1.skeleton.tree (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).negative).1.1).branching := by
  intro x hx
  obtain ⟨r, hr⟩ := (leafFlag_twoMk hM σ j).mp h2
  exact unit_hleaf_auxMk hM σ Mk D hS layer hLayer hp j 3 r hr x hx

end Local

/-! ## The hinge data -/

end WaveTurbulence.Flower.MkUnits
