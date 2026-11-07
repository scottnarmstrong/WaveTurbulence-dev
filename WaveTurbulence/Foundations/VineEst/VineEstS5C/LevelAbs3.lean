/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.BotAbs4
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelAbs2

/-! # The flat identity of the induction over the core vines, with no named hypothesis (V5 Step 4d part C)

`Lvl.absLeaves`: all leaf obligations of `hAbs` (`sb`, `sbm`, `base`, `basem`, `bot`, `botm`) hold.  **`Lvl.classSum_eq_flat`**: for every level, the class
sum is `c ζ lkRaw` of the recursively defined summand `psiFuel` (the flat form of TARGET Step 4, with the bottom vine handled by 4d-B2).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- **All leaf obligations of `hAbs` hold.** -/
theorem Lvl.absLeaves (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (hprime : IsPrimeGarden G) :
    AbsLeaves (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime where
  sb := fun lv pstar hk => sAbs_psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime hL hF
  sbm := fun lv pstar hk x => measurable_psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer)
    (lv.split B RD hG layer hLayer pstar hk) hprime hF x
  base := fun lv => (Lvl.abs_base B RD hG layer hLayer κ0 hL hF lv).1
  basem := fun lv => (Lvl.abs_base B RD hG layer hLayer κ0 hL hF lv).2
  bot := fun lv pstar h0 hup => uAbs_psiBot (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) lv.c hprime
    (Lvl.bottom_hb0 B RD hG layer hLayer lv pstar h0) hup hL hF
  botm := fun lv pstar h0 hup => measT_psiBot κ0 (lv.state B RD hG layer hLayer) lv.c hF

/-- **The flat identity, unconditional**: every level's class sum is `c ζ lkRaw` of its recursive summand. -/
theorem Lvl.classSum_eq_flat (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (hprime : IsPrimeGarden G)
    (lv : Lvl B) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    lv.classSum (p := p) (kind := kind) B RD hG layer hLayer κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (Fintype.card lv.ι + 1) lv) ![t0, t1, t2] ![e, f, g, h] :=
  Lvl.classSum_flat (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hF hprime
    (fun lv pstar hk x u u' hu => psiSB_congr (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime x hu)
    (fun m lv x t u u' hu => Lvl.psiFuel_congr (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t hu)
    (Lvl.hAbs_of_leaves (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hprime (Lvl.absLeaves (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hF hprime))
    (Fintype.card lv.ι) lv le_rfl t0 t1 t2 e f g h

end WaveTurbulence.VineEstS5C
