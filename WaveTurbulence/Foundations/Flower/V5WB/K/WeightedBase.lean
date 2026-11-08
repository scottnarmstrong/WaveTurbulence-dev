/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WB.Common
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.Engine
public import WaveTurbulence.Foundations.Flower.V5WB.K.Kernel
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.FlatBase
/-! Weighted FLAT-MOD base case: the literal native class with no operative
member, with an arbitrary spatial weight kept inside the decoration sum. -/
/-! Copied by source (V5W-B-WORLD) from V5W-A's port `Flower/V5WA/VineSpaceK/WeightedBase.lean` (see `COPIED-SHA256SUMS`): namespace `WaveTurbulence.Flower.V5WB`, every row selector (`variable [RowSel]`), the bond weight `bW` replaced by the masked, normalized `bWN` (`ψ : WD d`, bound `bWNB`). -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.Flower.V5WB
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
variable {kind : Bool}
open TTree LFTwist RegRed Reg.Skeleton MeasureTheory VineEstS4 VineEstS5C VineEstS5C.Cont
variable {w d : ℕ} {G : Garden w}

theorem memberMX_eq_lkRaw {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (lam L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (m : (GNode G.tree → Fin d → ℤ) → ℂ) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    memberMX D hG R L γ δ F layer hLayer base lam m t0 t1 t2 e f g h =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        lkRaw R L base (spatialMul m (modPsi b lam (psiNat D hG R L γ δ F layer hLayer base)))
          ![t0, t1, t2] ![e, f, g, h] := by
  unfold memberMX lkRaw spatialMul modPsi
  congr 1
  refine tsum_congr fun kd => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  beta_reduce
  rw [clLocalSummand_eq_psiNat D hG R L γ δ F layer hLayer base _ _ kd τ]
  rfl

theorem classMX_noop_eq_flat {ι : Type*} [Fintype ι] {p : ℕ}
    (A : FamilyReconstruction w ι) (hA : IsPrimeGarden A.skeleton)
    (c : ChainAt A.skeleton A.family)
    (hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (κ : KPar d) (lam : ℝ)
    (m : (z : ClassMember w ι) → (GNode z.1.skeleton.tree → Fin d → ℤ) → ℂ) :
    (∑ z ∈ canonFinsetK p kind A c, memberMX z.1.data z.1.plain
      (clRegionData z.1.skeleton z.2.block z.2.cl) κ.L κ.γ κ.δ κ.F
      (stateLayer z.1) (stateLayer_isLayering z.1) κ.base lam (m z)
      κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h) =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 (clRegionData A.skeleton c.block c.cl) *
        clLocalZeta (clRegionData A.skeleton c.block c.cl) *
        lkRaw (clRegionData A.skeleton c.block c.cl) κ.L κ.base
          (spatialMul (m ⟨A,c⟩) (modPsi c.b lam
            (psiNat A.data A.plain (clRegionData A.skeleton c.block c.cl) κ.L κ.γ κ.δ κ.F
              (stateLayer A) (stateLayer_isLayering A) κ.base)))
          ![κ.t0, κ.t1, κ.t2] ![κ.e, κ.f, κ.g, κ.h] := by
  classical
  rw [canonFinset_of_noop A hA c hno, Finset.sum_singleton]
  exact memberMX_eq_lkRaw A.data A.plain _ lam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end WaveTurbulence.Flower.V5WB
