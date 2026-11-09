/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelFlat
public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot19
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelRecurse
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelFlat
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelRecurse` (sha256 10ef10ae635168d9…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The induction over the core vines (V5 Step 4d part C, WP-I)

`Lvl.classSum_base`: with no operative member the class sum of a level is the native kernel of its chain region (`lkRaw` of `psiNat`).
`Lvl.psiFuel κ0 hprime m lv`: the summand of a level, by recursion on a fuel: the top operative member (largest piece index) is split off and the
lower level continues (`Lvl.psiStep`).  **`Lvl.classSum_flat`**: under the clock locality of the bundle `psiSB` and of the summands, the absolute convergence
of the glued summands at every level, and the absence of an operative member at the bottom piece (finding F-BOTTOM), the class sum of every level
is `c ζ lkRaw` of `psiFuel`: the flat form of TARGET Step 4 before the splitting of the bundle into its pieces (a)-(d).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C
open WaveTurbulence.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C
variable {γF : ℝ}
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The base summand of a level (no operative member): the native summand of its chain region. -/
noncomputable def LvlΓ.psiBase (κ0 : KPar d) (lv : LvlΓ B) : PsiT G d :=
  psiNat (lv.state B RD hG layer hLayer).data (lv.state B RD hG layer hLayer).plain lv.region κ0.L κ0.γ κ0.δ κ0.F
    (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer)) κ0.base

/-- Member `j` of a level has an LF operation at the state of the level. -/
def LvlΓ.Op (lv : LvlΓ B) (j : lv.ι) : Prop :=
  Nonempty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j)

open Classical in
/-- The top operative member of a level (largest piece index), if there is an operative member. -/
theorem LvlΓ.exists_top (lv : LvlΓ B) (h : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j) :
    ∃ pstar, lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar ∧
      ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val := by
  obtain ⟨j0, hj0⟩ := h
  obtain ⟨pstar, hmem, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun j => lv.Op (p := p) (kind := kind) B RD hG layer hLayer j)
    (fun j => (lv.e j).1.val) ⟨j0, by simpa using hj0⟩
  exact ⟨pstar, by simpa using hmem, fun j hj => hmax j (by simpa using hj)⟩

/-- At a member of piece index `0` the chain region of the level has the lower joint of the member as its bottom joint. -/
theorem LvlΓ.bottom_hb0 (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) :
    lv.c.b = ((lv.state B RD hG layer hLayer).family.placement pstar).lower := by
  have h3 := ((assemblySourceFamilyΓ B).corePlacement_at (lv.e pstar)).1
  have h2 := piece_lower_eq_jointAtΓ B (lv.e pstar).1.val (lv.e pstar).1.2
  have h4 : jointAtΓ B (lv.e pstar).1.val = b := by rw [h0]; exact jointAt_zeroΓ B
  show lv.c.b = ((assemblySourceFamilyΓ B).corePlacement (lv.e pstar)).lower
  rw [h3, lv.hcb]
  exact (h2.trans h4).symm

open Classical in
/-- The summand of a level, defined by recursion on the fuel `m`: at an operative level the top operative member is split off. -/
noncomputable def LvlΓ.psiFuel (κ0 : KPar d) (hprime : IsPrimeGarden G) : ℕ → LvlΓ B → PsiT G d
  | 0, lv => lv.psiBase B RD hG layer hLayer κ0
  | m + 1, lv =>
    if h : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j then
      if hk : 1 ≤ ((lv.e (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h))).1.val) then
        LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk hprime
          (LvlΓ.psiFuel κ0 hprime m (lv.next B RD hG layer hLayer (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk))
      else WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c
        (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h))
    else lv.psiBase B RD hG layer hLayer κ0

theorem LvlΓ.card_next_lt (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) :
    Fintype.card (lv.next B RD hG layer hLayer pstar hk).ι < Fintype.card lv.ι := by
  change Fintype.card {j : lv.ι // (lv.e j).1.val < (lv.e pstar).1.val} < Fintype.card lv.ι
  refine Fintype.card_subtype_lt (x := pstar) (by simp)

end WaveTurbulence.GammaLow.Famb.VineEstS5C
