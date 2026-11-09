/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P3.Bound
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Count
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P3.Bound
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Count` (sha256 14803dff92176c4c…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4: the per-vine term count (V5 Step 4d part C, WP-F)

`Lvl.card_terms_le_prod`: if the bundle expansion of the member `pstar` at every level has at most `wt (e pstar)` summands
(`wt` a weight function on the core indices, `wt ≥ 1`), then the unrolled multiset has at most `∏_{j ∈ members} wt (e j)` terms.
This is the TARGET count `4^b ∏ |Bs_i|` (one factor per operative vine, depending on the vine and not on the level).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C
variable {γF : ℝ}
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

/-- The members of the next level together with `pstar` form a subset of the members of the level. -/
theorem prod_next_mul_leΓ (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (wt : (assemblySourceFamilyΓ B).CoreIndex → ℕ) (hwt : ∀ i, 1 ≤ wt i) :
    wt (lv.e pstar) * ∏ j : (lv.next B RD hG layer hLayer pstar hk).ι, wt ((lv.next B RD hG layer hLayer pstar hk).e j) ≤
      ∏ j : lv.ι, wt (lv.e j) := by
  classical
  change wt (lv.e pstar) * ∏ j : {j : lv.ι // (lv.e j).1.val < (lv.e pstar).1.val}, wt (lv.e j.1) ≤ _
  rw [← Finset.prod_subtype (Finset.univ.filter fun j : lv.ι => (lv.e j).1.val < (lv.e pstar).1.val) (by simp)
    (fun j => wt (lv.e j))]
  have hnot : pstar ∉ Finset.univ.filter fun j : lv.ι => (lv.e j).1.val < (lv.e pstar).1.val := by simp
  rw [← Finset.prod_insert (f := fun j => wt (lv.e j)) hnot]
  exact Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) fun i _ _ => hwt _

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
