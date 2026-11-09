/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsBase
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelLoc2
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsBase2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelAbs2
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsBase2` (sha256 29cccfc7776dfaf4…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Joint measurability of the native summand `psiNat` in the exterior times and the clock (V5 Step 4d part C) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C
open WaveTurbulence.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4 WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS4

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {D : ReconstructionData G} {hG : G.IsPlain} {L γ δ : ℝ} {F : ℕ → Mom d → ℝ}
  {layer : GNode (D.forest hG) → ℕ} {hLayer : IsLayering (D.garden hG) layer} {base : Mom d}

section Meas
variable (R : CLRegionData G U a b) (layer0 : GBranch G.tree → ℕ)

end Meas

section Lv
variable {R : CLRegionData G U a b} {n : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- **The base leaf obligations of `hAbs`**: the native summand of a level has a uniform `UAbs` bound and is jointly measurable. -/
theorem LvlΓ.abs_base (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (lv : LvlΓ B) :
    (∃ C : ℝ, 0 ≤ C ∧ UAbs lv.region κ0.L κ0.base (lv.psiBase B RD hG layer hLayer κ0) C) ∧
      MeasT (lv.psiBase B RD hG layer hLayer κ0) := by
  have hHF := HF_of_all (lv.state B RD hG layer hLayer).data (lv.state B RD hG layer hLayer).plain κ0.L κ0.F
    (stateLayer (lv.state B RD hG layer hLayer)) κ0.base hF
  have hu := uAbs_psiNat (hLayer := stateLayer_isLayering (lv.state B RD hG layer hLayer)) (γ := κ0.γ) (δ := κ0.δ)
    lv.c.block lv.region hHF hL
  have hm := measT_psiNat (hLayer := stateLayer_isLayering (lv.state B RD hG layer hLayer)) (γ := κ0.γ) (δ := κ0.δ)
    lv.region hHF
  refine ⟨⟨_, ?_, hu⟩, hm⟩
  exact baseConst_nonneg _

end Lv

end WaveTurbulence.GammaLow.Famb.VineEstS5C
