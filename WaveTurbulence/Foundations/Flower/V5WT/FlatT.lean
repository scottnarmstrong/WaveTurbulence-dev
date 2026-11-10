/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WT.BottomT
public import WaveTurbulence.Foundations.Flower.V5WB.B.Flat
public import WaveTurbulence.Foundations.Flower.V5WB.K.FlatBound
public import WaveTurbulence.Foundations.Flower.V5WB.B.Bridge

/-! # V5W-T A3 (part 4): top-weighted FLAT-MOD and the class identity at `S = some s`

* `classSumBT_eq_flat`: the top-weighted level sum is `c ζ lkRaw` of the level's top-weighted bond weight
  `lvWT = bWT … lv.c.U lv.c.a` times the unweighted modulated `psiFuel`.  One top-weighted step (`classSumBT_base`,
  `classSumBT_bottom`, `classSumBT_flat_step`) over V5W-B-WORLD's bond-weighted induction `classSumB_flat` for the
  next level: the top `W` lives on the upper block, the next level carries the bond weight only (`hw`: `bWN` splits
  by `bondWD_union`, the node weight is read on the upper restriction, `nodeWeight_rA`).
* `twistedRecenteredModCX_bondT_eq_flatFn`: the literal class sum with every member's `bWT` is the flat observable
  `flatFnRMX` with the representative's multiplier `lvWT (Lvl.top B)`.
* `twistedRecenteredFW_eq`: V5W-0's pinned class kernel at any `S` is the selector class at `selW` with the member
  weight `bWT (wdOf p g cψ) (topFilterWeight S)` (V5W-B-WORLD's `twistedRecenteredFW_none_eq` for every `S`).

Copied by source from V5W-B-WORLD `Flower/V5WB/B/Flat.lean` (from `lvW`), `B/Export.lean`, `B/Bridge.lean`
(sha256 in `COPIED-SHA256SUMS`), edits as listed.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.Flower.V5WT
open WaveTurbulence.Flower.V5WB

section Level
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  TTree MeasureTheory WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont VineEstS5C

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The top-weighted bond weight of a level region, on the representative chart. -/
noncomputable def lvWT (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ) (κ0 : KPar d) (lv : Lvl B) :
    (GNode G.tree → Fin d → ℤ) → ℂ :=
  bWT ψ W κ0 (lv.state B RD hG layer hLayer) lv.c.U lv.c.a

/-- The base case: no operative member. -/
theorem classSumBT_base (lam : ℝ) (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ) (κ0 : KPar d) (hprime : IsPrimeGarden G) (lv : Lvl B)
    (hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    classSumBT (p := p) (kind := kind) B RD hG layer hLayer lam ψ W lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base (spatialMul (lvWT B RD hG layer hLayer ψ W κ0 lv)
          (modPsi b lam (lv.psiBase B RD hG layer hLayer κ0))) ![t0, t1, t2] ![e, f, g, h] := by
  classical
  have hp' : IsPrimeGarden (lv.state B RD hG layer hLayer).skeleton := hprime
  unfold classSumBT
  rw [canonFinset_of_noop (lv.state B RD hG layer hLayer) hp' lv.c hno, Finset.sum_singleton]
  unfold memberBT
  have hh := memberMX_eq_lkRaw (lv.state B RD hG layer hLayer).data
    (lv.state B RD hG layer hLayer).plain lv.region lam κ0.L κ0.γ κ0.δ κ0.F
    (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering _) κ0.base
    (lvWT B RD hG layer hLayer ψ W κ0 lv) t0 t1 t2 e f g h
  have hb : modPsi lv.c.b lam (lv.psiBase B RD hG layer hLayer κ0) =
      modPsi b lam (lv.psiBase B RD hG layer hLayer κ0) := by rw [lv.hcb]
  exact hh.trans (congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
    lkRaw lv.region κ0.L κ0.base (spatialMul (lvWT B RD hG layer hLayer ψ W κ0 lv) Ψ) ![t0,t1,t2] ![e,f,g,h]) hb)

/-- The bottom case: one operative bottom vine. -/
theorem classSumBT_bottom (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C)
    (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW)
    (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    classSumBT (p := p) (kind := kind) B RD hG layer hLayer lam ψ W lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (spatialMul (lvWT B RD hG layer hLayer ψ W κ0 lv)
            (modPsi b lam (WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar)))
          ![t0, t1, t2] ![e, f, g, h] := by
  let κ : KPar d := {κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h}
  have hh := sum_memberBT_bottom_eq_flat (p := p) (kind := kind) κ lam ψ C hC hψ W CW hCW hW
    (lv.state B RD hG layer hLayer) lv.c hprime
    (Lvl.bottom_hb0 B RD hG layer hLayer lv pstar h0) hup hL hF
  have hb : modPsi lv.c.b lam (WaveTurbulence.VineEstS5B2.psiBot p kind κ (lv.state B RD hG layer hLayer) lv.c pstar) =
      modPsi b lam (WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar) := by
    rw [lv.hcb]
    rfl
  exact hh.trans (congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
    lkRaw lv.region κ0.L κ0.base (spatialMul (lvWT B RD hG layer hLayer ψ W κ0 lv) Ψ) ![t0,t1,t2] ![e,f,g,h]) hb)

/-- **One level, flat form, bond-weighted.** -/
theorem classSumBT_flat_step (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C)
    (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW)
    (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
      IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (Ψ' : PsiT G d)
    (hIH : ∀ (t0 t1 t2 : ℝ) (e f g h : Mom d),
      classSumB (p := p) (kind := kind) B RD hG layer hLayer lam ψ (lv.next B RD hG layer hLayer pstar hk) κ0
          t0 t1 t2 e f g h =
        (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (lv.next B RD hG layer hLayer pstar hk).region *
          clLocalZeta (lv.next B RD hG layer hLayer pstar hk).region *
          lkRaw (lv.next B RD hG layer hLayer pstar hk).region κ0.L κ0.base
            (spatialMul (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (modPsi b lam Ψ'))
            ![t0, t1, t2] ![e, f, g, h])
    (hlocS : ∀ x (u u' : GBranch G.tree → ℝ), (∀ v ∈ (lv.split B RD hG layer hLayer pstar hk).sb.U, u v = u' v) →
      psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u =
        psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u')
    (hlocT : ∀ x t' (u u' : GBranch G.tree → ℝ), (∀ v ∈ (lv.split B RD hG layer hLayer pstar hk).tb.U, u v = u' v) →
      Ψ' x t' u = Ψ' x t' u')
    (t0 t1 t2 : ℝ) (e f g h : Mom d)
    (hAbs : GlueAbsConv (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS
      (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h
      (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ')) :
    classSumBT (p := p) (kind := kind) B RD hG layer hLayer lam ψ W lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (spatialMul (lvWT B RD hG layer hLayer ψ W κ0 lv)
            (modPsi b lam (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ')))
          ![t0, t1, t2] ![e, f, g, h] := by
  have hcomm : psiStepSp (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime (modPsi b lam (spatialMul (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) Ψ')) =
      modPsi b lam (spatialMul (fun x => (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (rB (lv.split B RD hG layer hLayer pstar hk).RT x))
        (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ')) := by
    exact (psiStepSp_modPsi κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime b lam _).trans
      (congrArg (modPsi b lam) (psiStepSp_spatialMul κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) Ψ'))
  have hbT : b ∈ (lv.split B RD hG layer hLayer pstar hk).tb.U := Lvl.b_mem B (lv.next B RD hG layer hLayer pstar hk)
  rw [classSumBT_nested (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ W CW hCW hW κ0 hL hF hprime lv pstar hk hA0
    t0 t1 t2 e f g h]
  have hAbs' : GlueAbsConv (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h
      (psiStepSp (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime (modPsi b lam (spatialMul (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) Ψ'))) := by
    rw [hcomm]
    refine glueAbsConv_modPsi _ _ _ κ0.L κ0.base t0 t1 t2 e f g h _ ?_ b lam
    exact glueAbsConv_spatialMul (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h _ hAbs
      (fun x => (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (rB (lv.split B RD hG layer hLayer pstar hk).RT x)) (bWNB ψ ((lv.next B RD hG layer hLayer pstar hk).state B RD hG layer hLayer) (lv.next B RD hG layer hLayer pstar hk).c.U C)
      (fun x => norm_bWN_le ψ κ0 ((lv.next B RD hG layer hLayer pstar hk).state B RD hG layer hLayer) (lv.next B RD hG layer hLayer pstar hk).c.U C hψ _)
  have hmerge := flat_merge_W (p := p) (kind := kind) κ0 hL (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
    (bWT ψ W κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U (lv.split B RD hG layer hLayer pstar hk).sb.a)
    (bWNB ψ (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U C * CW)
    (fun x => norm_bWT_le ψ W κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U (lv.split B RD hG layer hLayer pstar hk).sb.a hψ hW x)
    (modPsi b lam (spatialMul (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) Ψ'))
    (fun t E F' => classSumB (p := p) (kind := kind) B RD hG layer hLayer lam ψ (lv.next B RD hG layer hLayer pstar hk)
      κ0 t t1 t2 E F' g h)
    (lv.next B RD hG layer hLayer pstar hk).region lv.region t0 t1 t2 e f g h
    (fun t E F' => (hIH t t1 t2 E F' g h).trans (congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^
      clLocalOrder1 (lv.next B RD hG layer hLayer pstar hk).region * clLocalZeta (lv.next B RD hG layer hLayer pstar hk).region *
      lkRaw (lv.next B RD hG layer hLayer pstar hk).region κ0.L κ0.base Ψ ![t, t1, t2] ![E, F', g, h]) (spatialMul_modPsi _ _ _ _))) hlocS
    (fun x t' u u' hu => by
      unfold modPsi spatialMul
      rw [hu b hbT, hlocT x t' u u' hu])
    hAbs'
  have hcU : lv.c.U = (lv.split B RD hG layer hLayer pstar hk).sb.U ∪ (lv.split B RD hG layer hLayer pstar hk).tb.U := (lv.split B RD hG layer hLayer pstar hk).union
  have hwB : ∀ x : GNode G.tree → Fin d → ℤ, lvW B RD hG layer hLayer ψ κ0 lv x =
      bWN ψ κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U (rA (lv.split B RD hG layer hLayer pstar hk).RS x) * (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (rB (lv.split B RD hG layer hLayer pstar hk).RT x) := by
    intro x
    unfold lvW bWN
    rw [hcU, bondWD_union (ΨX ψ (lv.state B RD hG layer hLayer)) κ0.L κ0.base (layX (lv.state B RD hG layer hLayer)) (lv.split B RD hG layer hLayer pstar hk).sb.block (lv.split B RD hG layer hLayer pstar hk).hT (lv.split B RD hG layer hLayer pstar hk).hi (lv.split B RD hG layer hLayer pstar hk).hU x,
      bondWD_rA (ΨX ψ (lv.state B RD hG layer hLayer)) κ0.L κ0.base (layX (lv.state B RD hG layer hLayer)) (lv.split B RD hG layer hLayer pstar hk).RS x]
    congr 1
    exact (bondWD_rB (ΨX ψ (lv.state B RD hG layer hLayer)) κ0.L κ0.base (layX (lv.state B RD hG layer hLayer)) (lv.split B RD hG layer hLayer pstar hk).RT x).symm
  have hw : ∀ x : GNode G.tree → Fin d → ℤ, lvWT B RD hG layer hLayer ψ W κ0 lv x =
      bWT ψ W κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U
        (lv.split B RD hG layer hLayer pstar hk).sb.a (rA (lv.split B RD hG layer hLayer pstar hk).RS x) *
        (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (rB (lv.split B RD hG layer hLayer pstar hk).RT x) := by
    intro x
    have hn : nodeWeight W κ0.L κ0.base (lv.split B RD hG layer hLayer pstar hk).sb.a
        (rA (lv.split B RD hG layer hLayer pstar hk).RS x) = nodeWeight W κ0.L κ0.base lv.c.a x :=
      (nodeWeight_rA (lv.split B RD hG layer hLayer pstar hk).sb.block (lv.split B RD hG layer hLayer pstar hk).hT
        (lv.split B RD hG layer hLayer pstar hk).hi (lv.split B RD hG layer hLayer pstar hk).hU
        (lv.split B RD hG layer hLayer pstar hk).RS W κ0.L κ0.base x).trans
        (by rw [(lv.split B RD hG layer hLayer pstar hk).sa]; rfl)
    have hb := hwB x
    unfold lvW at hb
    unfold lvWT bWT lvW
    rw [hb, hn]
    exact mul_right_comm _ _ _
  have hΨ := spatialMul_combine (G' := G) (lvWT B RD hG layer hLayer ψ W κ0 lv) (bWT ψ W κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U (lv.split B RD hG layer hLayer pstar hk).sb.a) (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk))
    (rA (lv.split B RD hG layer hLayer pstar hk).RS) (rB (lv.split B RD hG layer hLayer pstar hk).RT) b lam (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ') hw
  refine hmerge.trans ((congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region *
    clLocalZeta lv.region * lkRaw lv.region κ0.L κ0.base
      (spatialMul (fun x => bWT ψ W κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U (lv.split B RD hG layer hLayer pstar hk).sb.a (rA (lv.split B RD hG layer hLayer pstar hk).RS x)) Ψ) ![t0, t1, t2] ![e, f, g, h]) hcomm).trans ?_)
  exact congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
    lkRaw lv.region κ0.L κ0.base Ψ ![t0, t1, t2] ![e, f, g, h]) hΨ

open Classical in
/-- **The top-weighted level sum, flat form**: one top-weighted step over V5W-B-WORLD's bond-weighted induction
(`classSumB_flat` for the next level). -/
theorem classSumBT_flat (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C)
    (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW)
    (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G)
    (hlocS : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) x (u u' : GBranch G.tree → ℝ),
      (∀ v ∈ (lv.split B RD hG layer hLayer pstar hk).sb.U, u v = u' v) →
      psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u =
        psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u')
    (hlocPsi : ∀ (m : ℕ) (lv : Lvl B) x t (u u' : GBranch G.tree → ℝ), (∀ v ∈ lv.c.U, u v = u' v) →
      Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u =
        Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u')
    (hAbs : ∀ (m : ℕ) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (t0 t1 t2 : ℝ) (e f g h : Mom d),
      GlueAbsConv (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS
        (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h
        (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
          (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk)))) :
    ∀ (m : ℕ) (lv : Lvl B), Fintype.card lv.ι ≤ m → ∀ (t0 t1 t2 : ℝ) (e f g h : Mom d),
      classSumBT (p := p) (kind := kind) B RD hG layer hLayer lam ψ W lv κ0 t0 t1 t2 e f g h =
        (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
          lkRaw lv.region κ0.L κ0.base
            (spatialMul (lvWT B RD hG layer hLayer ψ W κ0 lv)
              (modPsi b lam (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv)))
            ![t0, t1, t2] ![e, f, g, h] := by
  intro m
  cases m with
  | zero =>
    intro lv hc t0 t1 t2 e f g h
    have hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
      intro j
      have : Fintype.card lv.ι = 0 := Nat.le_zero.mp hc
      exact ((Fintype.card_eq_zero_iff.mp this).false j).elim
    have hnop : ¬ ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j := fun ⟨j, hj⟩ => (hno j).false hj.some
    rw [classSumBT_base (p := p) (kind := kind) B RD hG layer hLayer lam ψ W κ0 hprime lv hno]
    simp only [Lvl.psiFuel, hnop, dite_false]
  | succ m =>
    intro lv hc t0 t1 t2 e f g h
    by_cases hop : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j
    · obtain ⟨hpop, hpmax⟩ := Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)
      set pstar := Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop) with hpstar
      by_cases hk : 1 ≤ (lv.e pstar).1.val
      swap
      · have h0 : (lv.e pstar).1.val = 0 := by omega
        have hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
          intro j hjp
          refine ⟨fun op => hjp ?_⟩
          have h1 := hpmax j ⟨op⟩
          have h2 : (lv.e j).1.val = (lv.e pstar).1.val := by omega
          exact lv.he (Subtype.ext (Fin.ext h2))
        have hstep : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1 + 1) lv =
            WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar := by
          rw [Lvl.psiFuel, dite_eq_left hop]
          exact dite_eq_right hk
        rw [hstep]
        exact classSumBT_bottom (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ W CW hCW hW κ0 hL hF hprime lv
          pstar h0 hup
          t0 t1 t2 e f g h
      have hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
          IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
        intro j hj hjp
        refine ⟨fun op => ?_⟩
        have h1 := hpmax j ⟨op⟩
        have h2 : (lv.e j).1.val = (lv.e pstar).1.val := le_antisymm h1 (not_lt.mp hj)
        exact hjp (lv.he (Subtype.ext (Fin.ext h2)))
      have hcard : Fintype.card (lv.next B RD hG layer hLayer pstar hk).ι ≤ m := by
        have := Lvl.card_next_lt B RD hG layer hLayer lv pstar hk
        omega
      have hIH := fun t0 t1 t2 e f g h => classSumB_flat (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ
        κ0 hL hF hprime hlocS hlocPsi hAbs m (lv.next B RD hG layer hLayer pstar hk) hcard t0 t1 t2 e f g h
      have hstep : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1 + 1) lv =
          Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
            (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) (lv.next B RD hG layer hLayer pstar hk)) := by
        rw [Lvl.psiFuel, dite_eq_left hop]
        exact dite_eq_left hk
      rw [hstep]
      exact classSumBT_flat_step (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ W CW hCW hW κ0 hL hF hprime lv
        pstar hk hA0 _
        hIH (hlocS lv pstar hk) (fun x t' u u' hu => hlocPsi (m + 1) (lv.next B RD hG layer hLayer pstar hk) x t' u u' hu)
        t0 t1 t2 e f g h (hAbs (m + 1) lv pstar hk t0 t1 t2 e f g h)
    · have hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) :=
        fun j => ⟨fun op => hop ⟨j, ⟨op⟩⟩⟩
      rw [classSumBT_base (p := p) (kind := kind) B RD hG layer hLayer lam ψ W κ0 hprime lv hno]
      simp only [Lvl.psiFuel, hop, dite_false]

/-- **Top-weighted FLAT-MOD**: every level's top-weighted class sum is `c ζ lkRaw` of the level's top-weighted bond
weight times the unweighted modulated `psiFuel`. -/
theorem classSumBT_eq_flat (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C)
    (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW)
    (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (hprime : IsPrimeGarden G)
    (lv : Lvl B) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    classSumBT (p := p) (kind := kind) B RD hG layer hLayer lam ψ W lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (spatialMul (lvWT B RD hG layer hLayer ψ W κ0 lv)
            (modPsi b lam (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (Fintype.card lv.ι + 1) lv)))
          ![t0, t1, t2] ![e, f, g, h] :=
  classSumBT_flat (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ W CW hCW hW κ0 hL hF hprime
    (fun lv pstar hk x _u _u' hu => psiSB_congr (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime x hu)
    (fun m lv x t _u _u' hu => Lvl.psiFuel_congr (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t hu)
    (Lvl.hAbs_of_leaves (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hprime
      (Lvl.absLeaves (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hF hprime))
    (Fintype.card lv.ι) lv le_rfl t0 t1 t2 e f g h


end Level

section ExportT
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
variable {kind : Bool}
open TTree Twist LFTwist RegRed Reg.Skeleton MeasureTheory VineEstS2 VineEstS3 VineEstS4
  VineEstS5C VineEstS5C.Cont VineEstS5C.P4.Final VineEstS5C.P4

variable {w d p : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem twistedRecenteredModCX_bondT_eq_flat (hprime : IsPrimeGarden G) (lam : ℝ) (ψ : WD d)
    (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW)
    (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun z : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L z)|)
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    twistedRecenteredModCX G a (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B))
      (fun z => bWT ψ W κ0 z.1 z.2.U z.2.a) κ0.L κ0.γ κ0.δ κ0.F κ0.base lam t0 t1 t2 e f g h =
    Complex.exp (((-(Real.pi * κ0.δ * κ0.L ^ (2 * κ0.γ)) * t0 *
      boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ) * Complex.I) *
      ((coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (Lvl.top B).region * clLocalZeta (Lvl.top B).region *
        lkRaw (Lvl.top B).region κ0.L κ0.base (spatialMul (lvWT B RD hG layer hLayer ψ W κ0 (Lvl.top B))
          (modPsi b lam (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime
            (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B)))) ![t0,t1,t2] ![e,f,g,h]) := by
  exact congrArg (fun z => Complex.exp (((-(Real.pi * κ0.δ * κ0.L ^ (2 * κ0.γ)) * t0 *
    boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ) * Complex.I) * z)
    (classSumBT_eq_flat (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ W CW hCW hW κ0 hL hF hprime
      (Lvl.top B) t0 t1 t2 e f g h)

theorem twistedRecenteredModCX_bondT_eq_flatFn (hprime : IsPrimeGarden G) (lam : ℝ) (ψ : WD d)
    (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (hL : L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun z : Fin d → ℤ => |F k (base + latticePoint L z)|) :
    (fun (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d) =>
      twistedRecenteredModCX G a (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B))
        (fun z => bWT ψ W (kparOf L γ δ F base) z.1 z.2.U z.2.a) L γ δ F base lam
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) =
      flatFnRMX (p := p) (kind := kind) B RD hG layer hLayer
        (lvWT B RD hG layer hLayer ψ W (kparOf L γ δ F base) (Lvl.top B)) lam (G.sign a.toNode)
        (kparOf L γ δ F base) hprime (G.sign a.toNode) := by
  funext tt E
  have hh := twistedRecenteredModCX_bondT_eq_flat (p := p) (kind := kind) B RD hG layer hLayer hprime lam ψ C hC hψ
    W CW hCW hW
    (kparOf L γ δ F base) hL hF (tt 0) (tt 1) (tt 2)
    (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
    (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)
  rw [P3.vec3_eta, P3.vec4_eta'] at hh
  exact hh

end ExportT

section BridgeT
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 Links
open WaveTurbulence.VineSpaceK (ClassMember nodeWeight)
open WaveTurbulence.Flower.V5W (nodeRowIncoh regionWeightFW stateCoreLayer topFilterWeight clLocalKernelFW
  clLocalSummandFW twistedLocalKernelFW twistedRecenteredFW clLocalStarProductFW)
variable {w d : ℕ} {ι : Type*}

variable {rowSelU : Unit} [rowSel : VineEst.RowSel rowSelU]

end BridgeT

end WaveTurbulence.Flower.V5WT
