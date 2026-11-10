/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnits.Member0
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WAlign1

/-! # MK-UNITS: the weighted R-SLOT at a marking

Stage1WVine's `WAlign2`/`WAlign3` (the frontier-weighted outer slot kernels of a run-class member are the
representative's) at the marking `Mk`: the splice is `stSt A.skeleton σ Mk`, the batch carries the marking
(`MarkTransported`), and the chain is main's B1b-3 `batch_spliceKernelMk` → `commonShape_slotFnMk` with main's native
kernel replaced by Stage1WVine's `slotKerQ` (the per-operation step `operation_kerQ` is marking-free and imported).

Adapted from `Flower/Stage1WVine/WAlign2.lean`, `WAlign3.lean` and main's `Vine/Align/{OperationKernels,BatchKernels,
MemberKernels,ClassKernels}.lean` (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnits
open TTree WaveTurbulence WaveTurbulence.RegRed Finset WaveTurbulence.Represents Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W
  WaveTurbulence.LFTwist WaveTurbulence.VineAlign WaveTurbulence.VineA WaveTurbulence.VineB WaveTurbulence.VineC
  WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine

variable {w p d : ℕ} {kind : Bool} {ι : Type*}

section Member
variable {S : Garden w} (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (CLVine S)}
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {Y : FamilyReconstruction w (UnitsIndex (alignedAssemblyMk hM σ Mk))}
  {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (alignedAssemblyMk hM σ Mk)).Q j)}
  {xs : List (UnitsIndex (alignedAssemblyMk hM σ Mk))}
  (hr : ReachU p kind (unitsSplit (alignedAssemblyMk hM σ Mk)).Q xs
    (unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer)
    (unitsRegion (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk)) Y vs)
  (hn : xs.Nodup)
  {Mk' : Set (CLVine Y.skeleton)} (hT : Stage1Mk.MarkTransported (batchMolIso hr.batch) Mk Mk')

end Member

/-- The weight layers of the arguments of the outer slots are common to the class (at a marking). -/
theorem memShape_wLay {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (s : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) (i : Fin 2) (pw : ℕ) :
    wLay pw (fun b => stateLayer y.1 (y.1.data.coreBranch y.1.plain b).toNode)
        (argSrc y.1.plain ((memShape a mk y hy).iota y.1.plain hG s) i) =
      wLay pw (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        (argSrc a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s)
          i) := by
  obtain ⟨M, hr, hbr, hlow⟩ := memShape_trace a mk y hy
  have hroute := congrFun (congrFun (memShape_route a mk y hy hG) s) i
  rcases hr' : (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route
      a.prime.prime.1 hG s i with y' | j
  · rw [hr'] at hroute
    rw [(memShape a mk y hy).route_inl _ hG hroute,
      (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route_inl _ hG hr']
    rcases y' with r | c
    · rfl
    · show stateLayer y.1 (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)).toNode =
        sourceLayer a (a.prime.data.coreBranch a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)).toNode
      rw [memShape_core_layer, shape_core_layerMk]
  · rw [hr'] at hroute
    rw [(memShape a mk y hy).route_inr _ hG hroute,
      (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route_inr _ hG hr']
    show stateLayer y.1 (y.1.data.coreBranch y.1.plain (y.2 j).blk.b).toNode =
      sourceLayer a (a.prime.data.coreBranch a.prime.prime.1
        (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).lower).toNode
    rw [hlow j]
    exact member_core_layerMk a mk y M hr _

end WaveTurbulence.Flower.MkUnits
