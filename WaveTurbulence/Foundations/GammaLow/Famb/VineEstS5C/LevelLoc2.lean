/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelLoc
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelBase
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelRecurse
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelLoc2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRecurse
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelLoc2` (sha256 e8bc8b8c51db0958…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Clock locality of the level summands (V5 Step 4d part C, WP-I)

`ClDom_congr`, `psiNat_congr`: the native summand of a CL region reads the clock only on its region; `Lvl.psiBase_congr`,
**`Lvl.psiFuel_congr`**: `psiFuel` reads the clock only on the chain region of the level (hypothesis `hlocPsi` of `Lvl.classSum_flat`);
`Lvl.op_start`: an operation at a member of a level is an operation at the start state.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C
open WaveTurbulence.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C
variable {γF : ℝ}
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

section Fuel
variable {U : Finset (GBranch G.tree)} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem LvlΓ.psiBase_congr (κ0 : KPar d) (lv : LvlΓ B) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    {u u' : GBranch G.tree → ℝ} (h : ∀ v ∈ lv.c.U, u v = u' v) :
    lv.psiBase B RD hG layer hLayer κ0 x t u = lv.psiBase B RD hG layer hLayer κ0 x t u' :=
  psiNat_congr lv.c.block lv.region _ _ _ _ _ _ _ _ _ x t h

open Classical in
/-- **Clock locality of the summand of a level**: `psiFuel` reads the clock only on the chain region. -/
theorem LvlΓ.psiFuel_congr (κ0 : KPar d) (hprime : IsPrimeGarden G) :
    ∀ (m : ℕ) (lv : LvlΓ B) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) {u u' : GBranch G.tree → ℝ},
      (∀ v ∈ lv.c.U, u v = u' v) →
      LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u =
        LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u' := by
  intro m
  induction m with
  | zero => intro lv x t u u' h; exact LvlΓ.psiBase_congr B RD hG layer hLayer κ0 lv x t h
  | succ m ih =>
    intro lv x t u u' h
    by_cases hop : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j
    · set pstar := Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop) with hpstar
      by_cases hk : 1 ≤ (lv.e pstar).1.val
      · have hstep : LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv =
            LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
              (LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk)) := by
          rw [LvlΓ.psiFuel, dif_pos hop]
          exact dif_pos hk
        rw [hstep]
        set sp := lv.split B RD hG layer hLayer pstar hk with hsp
        have hsub1 : ∀ v ∈ sp.sb.U, u v = u' v := fun v hv =>
          h v (by rw [show lv.c.U = sp.sb.U ∪ sp.tb.U from sp.union]; exact Finset.mem_union_left _ hv)
        have hsub2 : ∀ v ∈ (lv.next B RD hG layer hLayer pstar hk).c.U, u v = u' v := fun v hv =>
          h v (by rw [show lv.c.U = sp.sb.U ∪ sp.tb.U from sp.union]; exact Finset.mem_union_right _ hv)
        have hb : u sp.sb.b = u' sp.sb.b := hsub1 _ sp.sb.block.2.2.1
        unfold LvlΓ.psiStep psiStepSp
        beta_reduce
        congr 1
        · exact psiSB_congr (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) sp hprime _ hsub1
        · have e2 := ih (lv.next B RD hG layer hLayer pstar hk) (rB sp.RT x) ![u sp.sb.b, t 1, t 2] hsub2
          have e3 : (![u sp.sb.b, t 1, t 2] : Fin 3 → ℝ) = ![u' sp.sb.b, t 1, t 2] := by rw [hb]
          exact e2.trans (congrArg (fun tt => LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m
            (lv.next B RD hG layer hLayer pstar hk) (rB sp.RT x) tt u') e3)
      · have hstep : LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv =
            WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar := by
          rw [LvlΓ.psiFuel, dif_pos hop]
          exact dif_neg hk
        rw [hstep]
        exact WaveTurbulence.VineEstS5B2.psiBot_congr κ0 (lv.state B RD hG layer hLayer) lv.c
          (LvlΓ.bottom_hb0 B RD hG layer hLayer lv pstar (by omega)) x t h
    · have hstep : LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv = lv.psiBase B RD hG layer hLayer κ0 := by
        simp only [LvlΓ.psiFuel, hop, dite_false]
      rw [hstep]
      exact LvlΓ.psiBase_congr B RD hG layer hLayer κ0 lv x t h

end Fuel

section Bottom
variable {U : Finset (GBranch G.tree)} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

end Bottom

end WaveTurbulence.GammaLow.Famb.VineEstS5C
