/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Index
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Win
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P3.Unroll
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.BundleExp
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P3.Unroll
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.BundleExp` (sha256 effb2e2a306357b6…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4: `BundleExp` per level from `bundle_decomp` / `bundle_decomp_mirror` (V5 Step 4d part C)

`SepFam`: the separated expansions of the approximant families `zpQfam`, `zpTfam` at the two time points of the bundle (to be delivered by P2 from the
gates; `PtOK` is the point domain of the expansions, `dom` says it holds on the frame domain).  `bundleExpOf`: the `BundleExp` of a level, with the
static case split (`CaseA` -> `bundle_decomp`, otherwise the mirror `bundle_decomp_mirror`).  The window `Win` is `bundleFrame = 0 ∨ (window ∧ PtOK)`:
outside the frame domain both `psiSB` and every summand vanish.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.ConjCoh TTree
  WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.GammaLow.Famb.VineEstS5C
open scoped ComplexConjugate

set_option linter.unusedSectionVars false
section
variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} {d : ℕ} [Fintype ι] [DecidableEq ι]

end

section Level
open WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS5B MeasureTheory WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable {kind : Bool}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}

open Classical in
/-- **`BundleExp` of a level** from the separated expansions `SF`, the typing inputs `hZ`, `hL`, `hr` and `hR` (PL234 `reality_all`). -/
noncomputable def bundleExpOfΓ (hR : RealityAll) (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hZ : ZpSurj p kind pstar {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime)
    (hL : ZpLayers p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime)
    (hr : RetParent (pstar := pstar) (lv.state B RD hG layer hLayer))
    (SF : SepFam p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} κ0 (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime) :
    BundleExpΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime lv pstar hk where
  Ch := Ch SF.S
    (if CaseA (pstar := pstar) (lv.state B RD hG layer hLayer) then
      bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
      else bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime)
    (if CaseA (pstar := pstar) (lv.state B RD hG layer hLayer) then
      bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
      else bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime)
    (bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime)
    (bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime)
  term := fun c x u => bundleTerm p kind _ κ0 _ _ hprime SF _ _ c x u
  Win := BundleWin p kind _ κ0 _ _ hprime SF
  eq := fun x u hW => psiSB_eq_sum_terms _ _ hprime hR hZ hL κ0 SF hr _ _
    ⟨fun h => by simp [if_pos h], fun h => by simp [if_neg h]⟩ x u hW

/-- **The number of summands of a level's bundle** (independent of the static case split):
`3 (∑_{bsA} mQ mT + ∑_{bsB} mQ mT) + ∑_{bsA} (mQ + mT + 1) + ∑_{bsB} (mQ + mT + 1)`. -/
theorem card_bundleExpChΓ (hR : RealityAll) (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hZ : ZpSurj p kind pstar {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime)
    (hL : ZpLayers p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime)
    (hr : RetParent (pstar := pstar) (lv.state B RD hG layer hLayer))
    (SF : SepFam p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} κ0 (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime) :
    Fintype.card (bundleExpOfΓ B RD hG layer hLayer hR lv pstar hk hZ hL hr SF).Ch =
      3 * ((∑ b ∈ bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
              (lv.split B RD hG layer hLayer pstar hk) hprime, SF.S.mQ b * SF.S.mT b) +
            ∑ b ∈ bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
              (lv.split B RD hG layer hLayer pstar hk) hprime, SF.S.mQ b * SF.S.mT b) +
        ((∑ b ∈ bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
              (lv.split B RD hG layer hLayer pstar hk) hprime, (SF.S.mQ b + SF.S.mT b + 1)) +
          ∑ b ∈ bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
              (lv.split B RD hG layer hLayer pstar hk) hprime, (SF.S.mQ b + SF.S.mT b + 1)) := by
  classical
  unfold bundleExpOfΓ
  show Fintype.card (Ch _ _ _ _ _) = _
  rw [card_ch]
  split_ifs <;> ring

end Level
end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
