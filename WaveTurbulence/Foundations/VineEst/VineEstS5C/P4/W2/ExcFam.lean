/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcInd
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Family

/-! # P4-W2 (a): the exceptional factors of P4's bundle family and of BOT-DECOMP's bottom family

`stepX`: the exceptional factor `ν · bundlePt` of a summand `c` of `bundleFamOf` at an operative member (the summand read through the cast
`castCh` to the type of `bundleExpOf`), `botX`: the factor `ν · botPt` of `bundleBotFamOf`.  `frameShapeX_bundleFamOf`,
`botFrameShapeX_bundleBotFamOf`: the frame shapes with these factors; **`rowFormNE_termsB_fam`**: `rowFormNE_termsB` for the actual families.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot

variable {w d : ℕ} {G : Garden w} {kind : Bool}

theorem term_cast {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ}
    {B : CLChainAssembly G R n} {RD : ReconstructionData G} {hG : G.IsPlain}
    {layer : GNode (RD.forest hG) → ℕ} {hLayer : IsLayering (RD.garden hG) layer} {κ0 : KPar d} {hprime : IsPrimeGarden G}
    {lv : Lvl B} {pstar : lv.ι} {hk : 1 ≤ (lv.e pstar).1.val}
    {E E' : BundleExp (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime lv pstar hk} (h : E = E') (c : E.Ch)
    (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) :
    E.term c x u = E'.term (cast (congrArg BundleExp.Ch h) c) x u := by
  subst h
  rfl

section Fam
variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (hR : RealityAll) (SFF : SepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

open Classical in
theorem bundleFamOf_eq_of_op (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar) :
    bundleFamOf B RD hG layer hLayer hR SFF lv pstar hk =
      bundleExpOf B RD hG layer hLayer hR lv pstar hk (zpSurj_of_op B RD hG layer hLayer lv pstar hk hop)
        (zpLayers_of_op B RD hG layer hLayer lv pstar hk hop) (retParent _) (SFF lv pstar hk hop) := by
  unfold bundleFamOf
  rw [dif_pos hop]

open Classical in
/-- The exceptional factor of a summand of the bundle family at an operative member. -/
noncomputable def stepX (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (c : (bundleFamOf B RD hG layer hLayer hR SFF lv pstar hk).Ch) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) : ℂ :=
  if hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar then
    ((nuOf (lv.state B RD hG layer hLayer) pstar : ℤˣ) : ℂ) *
      bundlePt p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} κ0 (lv.state B RD hG layer hLayer)
        (lv.split B RD hG layer hLayer pstar hk) hprime (SFF lv pstar hk hop) _ _
        (bundleVars κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u).1
        (bundleVars κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u).2.1
        (bundleVars κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u).2.2.1
        (bundleVars κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u).2.2.2.1
        (bundleVars κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u).2.2.2.2
        (cast (congrArg BundleExp.Ch (bundleFamOf_eq_of_op B RD hG layer hLayer hR SFF lv pstar hk hop)) c)
  else 0

open Classical in
theorem frameShapeX_bundleFamOf :
    FrameShapeX B RD hG layer hLayer (bundleFamOf B RD hG layer hLayer hR SFF) (stepX B RD hG layer hLayer hR SFF) := by
  intro lv pstar hk hop c x u
  rw [term_cast (bundleFamOf_eq_of_op B RD hG layer hLayer hR SFF lv pstar hk hop) c x u]
  unfold stepX
  rw [dif_pos hop]
  simp only [bundleExpOf, bundleTerm]
  unfold bundleFrame
  ring

variable (hprime' : IsPrimeGarden G) (BSFF : BotSepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0)

open Classical in
/-- The exceptional factor of a summand of the bottom family. -/
noncomputable def botX (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    (c : (bundleBotFamOf B RD hG layer hLayer hprime' hR BSFF lv pstar h0 hop hmax).Ch) (x : GNode G.tree → (Fin d → ℤ))
    (u : GBranch G.tree → ℝ) : ℂ :=
  ((nuOf (lv.state B RD hG layer hLayer) pstar : ℤˣ) : ℂ) *
    botPt p kind pstar (lv.state B RD hG layer hLayer) lv.c κ0 (BSFF lv pstar h0 hop hmax) _ _
      (botVars κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u).1
      (botVars κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u).2.1
      (botVars κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u).2.2.1
      (botVars κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u).2.2.2.1
      (botVars κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u).2.2.2.2 c

open Classical in
theorem botFrameShapeX_bundleBotFamOf :
    BotFrameShapeX B RD hG layer hLayer (bundleBotFamOf B RD hG layer hLayer hprime' hR BSFF)
      (botX B RD hG layer hLayer hR hprime' BSFF) := by
  intro lv pstar h0 hop hmax c x t u
  rw [bundleBotFamOf_term]
  unfold botTerm botX
  ring

theorem rowFormNE_termsB_fam (hL : κ0.L ≠ 0) :
    ∀ (m : ℕ) (lv : Lvl B), ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer
        (bundleFamOf B RD hG layer hLayer hR SFF) (bundleBotFamOf B RD hG layer hLayer hprime' hR BSFF) m lv,
      QNE B RD hG layer hLayer (bundleFamOf B RD hG layer hLayer hR SFF) (bundleBotFamOf B RD hG layer hLayer hprime' hR BSFF)
        (stepX B RD hG layer hLayer hR SFF) (botX B RD hG layer hLayer hR hprime' BSFF) lv ψ :=
  rowFormNE_termsB B RD hG layer hLayer _ _ _ _ hL (frameShapeX_bundleFamOf B RD hG layer hLayer hR SFF)
    (botFrameShapeX_bundleBotFamOf B RD hG layer hLayer hR hprime' BSFF)

end Fam

end WaveTurbulence.VineEstS5C.P4.W2
