/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSrcStep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.BotSrcOf
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxLeaf2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.BotGeo
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz4
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecBotSz1
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecCoh
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecSz5
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecBotSz1` (sha256 4f1e25a39a1e368e…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 19, step 2): the bottom bundle, sizes and constants (copy of RecSz1, RecSz4, RecSrcChoice for `botSrcOf`)

`bot_half_sizes`, `bot_leafCost_eq_native`, `botCertC_good_vals`, `botCertT_good_vals`, `botSzQ_good`, `botSzT_good`, `bot_sz_idx`, `crqChoiceB`, `crtChoiceB`, `botSrcOfC`, `botSrcOfC_idx`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W13
  WaveTurbulence.LGSpine TTree WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  Set WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} [Fintype ι] [DecidableEq ι]
variable {P : WTParams} {κ : KPar P.d} {B0 : ℝ}

variable (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family) (hA : IsPrimeGarden A.skeleton)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
    (A.family.atoms pstar) (A.family.upper pstar))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))
  (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))

section Native
variable {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

include hA hup hcan hel htc hcc in
theorem bot_leafCost_eq_nativeΓ (i : (assemblySourceFamilyΓ B).CoreIndex) (hN : zpN A pstar = zpN (startStateΓ B RD hG layer hLayer) i)
    (b' : BT w ι) (hb : b' ∈ canonFinsetK p kind A c0) (B0 : ℝ) :
    layerCost (fun _ => B0) (zpObjC b'.1 pstar) * layerCost (fun _ => B0) (zpObjT b'.1 pstar) =
      layerCost (fun _ => B0) (nativeCoupleLayered RD hG layer hLayer
          (pairOfLeaf G hG ((startStateΓ B RD hG layer hLayer).family.placement i).retained)) *
        layerCost (fun _ => B0) (nativeChainLayered RD hG layer hLayer
          ((startStateΓ B RD hG layer hLayer).family.placement i).lower) := by
  rw [layerCost_const, layerCost_const, layerCost_const, layerCost_const, ← pow_add, ← pow_add,
    bot_leafCard A c0 hA hcan hel htc hcc hup b' hb, native_leafCard_startΓ B RD hG layer hLayer i, hN]

end Native

section Cert
variable {Bh : ℕ → ℝ} (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)

end Cert

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
