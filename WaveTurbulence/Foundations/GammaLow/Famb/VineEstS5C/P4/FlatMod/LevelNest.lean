/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Bundle
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelRec
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.LevelNest
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRec
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Step3AtH
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.LevelNest` (sha256 ff334d86aeb2a3db…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # FLAT-MOD (R60), one level of TARGET Step 4, nested form, for the modulated kernel

`Lvl.classSumM`: the class sum of a level with the modulated member kernels `twistedLocalKernelM`.  **`Lvl.classSumM_nested`**: the class
sum of a level is the S-side with the (unmodulated) bundle `psiSB` and the lower factor the modulated class sum of the next level.
(The modulation sits at the lower joint `b`, which is the lower joint of every level; it is carried by the lower factor.)
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C
open WaveTurbulence.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
  WaveTurbulence.VineEstS5C.FlatMod

namespace FlatMod
variable {w : ℕ} {ι ι' : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι}

section
variable [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

end

section
variable [Fintype ι] [DecidableEq ι]

end

end FlatMod

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The modulated class sum of a level, with the dynamic parameters explicit. -/
noncomputable def LvlΓ.classSumM (lam : ℝ) (lv : LvlΓ B) (κ0 : KPar d) (t0 t1 t2 : ℝ) (e f g h : Mom d) : ℂ :=
  ∑ z ∈ canonFinsetK p kind (lv.state B RD hG layer hLayer) lv.c,
    twistedLocalKernelM lam z.1 z.2 κ0.L κ0.γ κ0.δ κ0.F κ0.base t0 t1 t2 e f g h

/-- **One level of TARGET Step 4, nested form, modulated.** -/
theorem LvlΓ.classSumM_nested (lam : ℝ) (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
      IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    LvlΓ.classSumM (p := p) (kind := kind) B RD hG layer hLayer lam lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (lv.split B RD hG layer hLayer pstar hk).RS *
        clLocalZeta (lv.split B RD hG layer hLayer pstar hk).RS *
        ∑' x : ExtS (lv.split B RD hG layer hLayer pstar hk).RS κ0.L κ0.base e f,
          ∫ σ : CLInternalTime (lv.split B RD hG layer hLayer pstar hk).RS,
            psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x.1
              (clLocalClock (lv.split B RD hG layer hLayer pstar hk).RS ![t0, t1, t2] σ) *
            (lv.next B RD hG layer hLayer pstar hk).classSumM (p := p) (kind := kind) B RD hG layer hLayer lam κ0
              (clLocalClock (lv.split B RD hG layer hLayer pstar hk).RS ![t0, t1, t2] σ
                (lv.split B RD hG layer hLayer pstar hk).sb.b) t1 t2
              (κ0.base + latticePoint κ0.L (x.1 ((lv.state B RD hG layer hLayer).family.placement pstar).lower.toNode))
              (κ0.base + latticePoint κ0.L (x.1 ((lv.state B RD hG layer hLayer).family.placement pstar).retained.toNode))
              g h := by
  classical
  set A' := lv.state B RD hG layer hLayer with hA'
  set sp := lv.split B RD hG layer hLayer pstar hk with hsp
  let κ : KPar d := { κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h }
  have hc : Stage1.OpsCommute p kind w lv.ι := Stage1.opsCommute_all
  have h1 := tildeJ2_canonM (p := p) (kind := kind) κ lam A' sp hprime hA0 hL hF
  have h2 := tildeJ2_bundleM (p := p) (kind := kind) κ lam A' sp hprime hA0 hL hF
  have hKt := KtilM_eq_canon (p := p) (kind := kind) hc (Subtype.val : {j : lv.ι // (lv.e j).1.val < (lv.e pstar).1.val} → lv.ι)
    Subtype.val_injective (fun j => j.2) (fun i hi => ⟨⟨i, hi⟩, rfl⟩) κ lam hprime sp hA0
  have e1 : LvlΓ.classSumM (p := p) (kind := kind) B RD hG layer hLayer lam lv κ0 t0 t1 t2 e f g h =
      ∑ G ∈ zpFinset p kind pstar _ A' sp hprime, sSumAt κ G.1 G.2 (ktildeM (p := p) (kind := kind) κ lam A' sp hprime G) := h1
  rw [e1, h2]
  congr 1
  refine tsum_congr fun x => integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  beta_reduce
  have hp' : IsPrimeGarden A'.skeleton := hprime
  rw [sum_stIntM_eq (p := p) (kind := kind) κ lam A' sp hp' x σ, hKt]
  congr 1

end WaveTurbulence.GammaLow.Famb.VineEstS5C
