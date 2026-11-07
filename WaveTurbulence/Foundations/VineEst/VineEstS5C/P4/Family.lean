/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.UnrollR
public import WaveTurbulence.Foundations.VineEst.ZpSurj.Export

/-! # P4: the bundle expansion family, with `ZpSurj`, `ZpLayers` and `hq2` discharged (ZP-SURJ, R51)

At a level `lv` and a member `pstar` the bundle expansion is used by `Lvl.terms` only when `pstar` is operative, i.e. when there is a
`FamilyOperation` at `pstar` (`Lvl.Op`).  Its four preconditions (`canonical`, `eligible`, `treeCoherent`, `coupleCoherent`) are exactly
the hypotheses of ZP-SURJ's `zpSurj_of_state`, `zpLayers_of_state`, `zpQ2_le_of_state`.  So:

* `bundleFamOf hR SFF`: `bundleExpOf` (the pieces of `bundle_decomp` / its mirror) at operative members, with `ZpSurj`, `ZpLayers` from
  ZP-SURJ and `RetParent` from `retParent`; the trivial one-summand expansion `trivialExp` at the others (never read by `Lvl.terms`).
  The only inputs are PL234's `RealityAll` and the separated expansions `SFF` of the approximants (P2 gate data).
* `winOfExt_bundleFamOf`: every window holds under the exterior window of the level (`bundleWin_holds`, with `hq2 = zpQ2_le_of_state`).
* `card_bundleFamOf`: the number of summands (the count of `card_bundleExpCh`, or `1`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}

/-- The trivial expansion (one summand, the bundle itself); used at non-operative members, where `Lvl.terms` never reads it. -/
noncomputable def trivialExp (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) :
    BundleExp (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime lv pstar hk where
  Ch := Unit
  term := fun _ x u => psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u
  Win := fun _ _ => True
  eq := fun x u _ => by simp

variable (p) in
/-- The separated expansions of the approximants at every operative member (from P2's gate data). -/
abbrev SepFamFam (κ0 : KPar d) (hprime : IsPrimeGarden G) : Type 1 :=
  ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar →
    SepFam p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} κ0 (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime

theorem zpSurj_of_op (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (h : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar) :
    ZpSurj p kind pstar {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime :=
  WaveTurbulence.ZpSurj.zpSurj_of_state _ _ hprime h.some.canonical h.some.eligible h.some.treeCoherent h.some.coupleCoherent

theorem zpLayers_of_op (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (h : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar) :
    ZpLayers p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime :=
  WaveTurbulence.ZpSurj.zpLayers_of_state _ _ hprime h.some.canonical h.some.eligible h.some.treeCoherent h.some.coupleCoherent

theorem hq2_of_op (lv : Lvl B) (pstar : lv.ι) (h : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar) :
    zpQ2 (lv.state B RD hG layer hLayer) pstar ≤
      layOf (lv.state B RD hG layer hLayer) (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) :=
  WaveTurbulence.ZpSurj.zpQ2_le_of_state (p := p) (kind := kind) _ h.some.canonical h.some.eligible h.some.treeCoherent h.some.coupleCoherent

open Classical in
/-- **The bundle expansion family** of the unrolling: `bundleExpOf` at operative members, `trivialExp` elsewhere. -/
noncomputable def bundleFamOf (hR : RealityAll) (SFF : SepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime) :
    BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime :=
  fun lv pstar hk =>
    if h : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar then
      bundleExpOf B RD hG layer hLayer hR lv pstar hk (zpSurj_of_op B RD hG layer hLayer lv pstar hk h)
        (zpLayers_of_op B RD hG layer hLayer lv pstar hk h) (retParent _) (SFF lv pstar hk h)
    else trivialExp B RD hG layer hLayer lv pstar hk

open Classical in
/-- **The windows of the family hold under the exterior window** (`WinOfExt`, the input of design R). -/
theorem winOfExt_bundleFamOf (hR : RealityAll) (SFF : SepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime) :
    WinOfExt B RD hG layer hLayer (bundleFamOf B RD hG layer hLayer hR SFF) := by
  intro lv pstar hk x u hu
  unfold bundleFamOf
  split_ifs with h
  · have hsa : (lv.split B RD hG layer hLayer pstar hk).sb.a = lv.c.a := (lv.split B RD hG layer hLayer pstar hk).sa
    exact bundleWin_holds κ0 _ _ hprime (SFF lv pstar hk h) (retParent _) (hq2_of_op B RD hG layer hLayer lv pstar h) x u
      (by rw [hsa]; exact hu)
  · trivial

open Classical in
/-- **The number of summands of the family** at a member: the count of `card_bundleExpCh` when operative, `1` otherwise. -/
theorem card_bundleFamOf (hR : RealityAll) (SFF : SepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime) (lv : Lvl B)
    (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) :
    Fintype.card (bundleFamOf B RD hG layer hLayer hR SFF lv pstar hk).Ch =
      if h : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar then
        3 * ((∑ b ∈ bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
                (lv.split B RD hG layer hLayer pstar hk) hprime, (SFF lv pstar hk h).S.mQ b * (SFF lv pstar hk h).S.mT b) +
              ∑ b ∈ bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
                (lv.split B RD hG layer hLayer pstar hk) hprime, (SFF lv pstar hk h).S.mQ b * (SFF lv pstar hk h).S.mT b) +
          ((∑ b ∈ bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
                (lv.split B RD hG layer hLayer pstar hk) hprime,
                ((SFF lv pstar hk h).S.mQ b + (SFF lv pstar hk h).S.mT b + 1)) +
            ∑ b ∈ bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
                (lv.split B RD hG layer hLayer pstar hk) hprime,
                ((SFF lv pstar hk h).S.mQ b + (SFF lv pstar hk h).S.mT b + 1))
      else 1 := by
  unfold bundleFamOf
  split_ifs with h
  · exact card_bundleExpCh B RD hG layer hLayer hR lv pstar hk _ _ _ _
  · rfl

end WaveTurbulence.VineEstS5C.P4
