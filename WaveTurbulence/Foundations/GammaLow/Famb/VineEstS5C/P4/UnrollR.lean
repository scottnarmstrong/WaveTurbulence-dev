/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.BundleExp
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Recentered
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Count
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.UnrollR
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P2.Recentered
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.BundleExp
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Count
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.UnrollR` (sha256 03512f0440c98292…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4: the unrolled identity under the exterior window of the top level only (finding F-WINCHAIN, design R)

P3's `Lvl.winOf` asks for the window of every operative level at once.  The window of the next level is the window of the clock
`u (sb.b)` of the lower joint, which is in its layer window only where the frame of the current level is nonzero (`DomF`).  So the
conjunction is not an a.e. property.  Design R: keep P3's multiset `Lvl.terms` (it never reads the windows) and prove the unrolled
identity from the exterior window `ExtOf lv u` of the level alone:

* `ext_next`: `ExtOf lv u` and `psiSB ≠ 0` give `ExtOf (lv.next ..) u` (frame `≠ 0` → `DomF` → windows of all S-branches, among
  them the lower joint `sb.b`, which is the top joint of the next level);
* `Lvl.psiFuel_eq_terms_ext`: if every bundle window `Win` holds under the exterior window (`hW`), then `ExtOf lv u` gives
  `psiFuel = ∑ terms` (if `psiSB = 0` both sides vanish, since `∑ term = psiSB`; otherwise `ext_next` and induction);
* `clsFn_eq_sum_terms_ext`, `unrolled_boundR_ext`: P3's `clsFn_eq_sum_terms` and P2's recentered `unrolled_bound_recentered` with the
  hypothesis `hExt` (the exterior clock `tt 0` strictly inside the layer window of the top joint) in place of `hWin`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
variable {γF : ℝ}
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2
open scoped ENNReal

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The exterior window of a level: the clock of the top joint of its chain region is strictly inside its unit layer window. -/
def ExtOfΓ (lv : LvlΓ B) (u : GBranch G.tree → ℝ) : Prop :=
  (layOf (lv.state B RD hG layer hLayer) lv.c.a : ℝ) < u lv.c.a ∧
    u lv.c.a < layOf (lv.state B RD hG layer hLayer) lv.c.a + 1

/-- The exterior window of a level at the local clock of its region is the window of the exterior clock `t 0`. -/
theorem extOf_clock_iffΓ (lv : LvlΓ B) (t : Fin 3 → ℝ) (τ : CLInternalTime lv.region) :
    ExtOfΓ B RD hG layer hLayer lv (clLocalClock lv.region t τ) ↔
      (layOf (lv.state B RD hG layer hLayer) lv.c.a : ℝ) < t 0 ∧ t 0 < layOf (lv.state B RD hG layer hLayer) lv.c.a + 1 := by
  unfold ExtOfΓ
  rw [show clLocalClock lv.region t τ lv.c.a = t 0 from clLocalClock_upper lv.region t τ]

/-- **The window passes to the next level** where the bundle does not vanish. -/
theorem ext_nextΓ (κ0 : KPar d) (hprime : IsPrimeGarden G) (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) (hu : ExtOfΓ B RD hG layer hLayer lv u)
    (h : psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u ≠ 0) :
    ExtOfΓ B RD hG layer hLayer (lv.next B RD hG layer hLayer pstar hk) u := by
  have hf : bundleFrame κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u ≠ 0 := fun h0 =>
    h (psiSB_eq_zero_of_frame (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u h0)
  have hD := domF_of_frame_ne (pstar := pstar) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u hf
  have hsa : (lv.split B RD hG layer hLayer pstar hk).sb.a = lv.c.a := (lv.split B RD hG layer hLayer pstar hk).sa
  have hw := win_of_domF _ (lv.split B RD hG layer hLayer pstar hk) u hD (by rw [hsa]; exact hu)
  have hb := hw _ (lv.split B RD hG layer hLayer pstar hk).sb.block.2.2.1
  have hj : (lv.next B RD hG layer hLayer pstar hk).c.a = (lv.split B RD hG layer hLayer pstar hk).sb.b :=
    (lv.split B RD hG layer hLayer pstar hk).joint.symm
  unfold ExtOfΓ
  rw [hj]
  exact hb

variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

/-- The windows of the bundle expansions hold under the exterior window of their level. -/
def WinOfExtΓ : Prop :=
  ∀ (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ),
    ExtOfΓ B RD hG layer hLayer lv u → (BE lv pstar hk).Win x u

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
