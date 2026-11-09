/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz7
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecRowsBnd
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecEngLit
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecRegion
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Iface
public import WaveTurbulence.Foundations.VineEst.HFree.Inst
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecFinal
public import WaveTurbulence.Foundations.GammaLow.Famb.HFree.Inst
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Final.Iface
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecRowsBnd
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecSz7
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecFinal` (sha256 cd91b9e21a4625c6…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 19, step 5): the uniform certificate of the terms with records (kinds `0`, `1`, `3`)

`NoKind2`: the staging hypothesis (no kind-2 summand in any bundle), to be replaced by the kind-2 packet.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W13
open VineParamContract
open scoped ENNReal

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

theorem rowBoundH_nonnegΓ
    {P : WTParams} {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ} (hB : ProfileBound P h Bh p)
    (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
    (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 0 < P.L)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d) (ρ : (assemblyShapeΓ hM9 B).VIdx ⊕ (assemblyShapeΓ hM9 B).VIdx) :
    0 ≤ rowBoundHΓ hM9 B RD hG layer hLayer P Bh W ρ := by
  unfold rowBoundHΓ
  refine mul_nonneg ?_ (rowCostH_nonnegΓ (hLayer := hLayer) hB hlay W ρ)
  rcases ρ with v | v <;> exact (rowB_pos (P := P) hC1 hδ hL _ _).le

theorem recEng_paramΓ {d : ℕ} (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (recs : List (ExcRec G d))
    (kd : ExcRec G d → ℕ) (zc : ExcRec G d → Prop)
    (addr : ExcRec G d → Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar))
    (centre : Fin 4 → Mom d) (wBar : Mom d) (lam : ℝ) (v : (assemblyShapeΓ hM9 B).TVar) :
    (recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam).param v =
      if v = (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩ : (assemblyShapeΓ hM9 B).TVar) then lam else 0 := rfl

/-- **`maxPar` of the engine datum of a term with records**: `maxPar^{η⁶} ≤ (1+|λ|)^{6η⁶}`. -/
theorem maxPar_rec_leΓ {d : ℕ} (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (recs : List (ExcRec G d))
    (kd : ExcRec G d → ℕ) (zc : ExcRec G d → Prop)
    (addr : ExcRec G d → Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar))
    (centre : Fin 4 → Mom d) (wBar : Mom d) (lam η : ℝ) (hη : 0 < η) :
    maxPar (recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam) ^ (η ^ 6) ≤ (1 + |lam|) ^ (6 * η ^ 6) := by
  have hne : Nonempty (assemblyShapeΓ hM9 B).TVar := ⟨.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩⟩
  have hmp : maxPar (recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam) ≤ 1 + |lam| := by
    rw [maxPar_eq]
    haveI : Nonempty (recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam).S.TVar := hne
    refine ciSup_le fun v => ?_
    refine (le_of_eq (congrArg WaveTurbulence.VineEstS3.Eng.Jb (recEng_paramΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam v))).trans ?_
    split_ifs
    · exact Jb_le_one_add lam
    · have : WaveTurbulence.VineEstS3.Eng.Jb 0 = 1 := by simp [WaveTurbulence.VineEstS3.Eng.Jb]
      rw [this]; linarith [abs_nonneg lam]
  have hmp0 : 0 ≤ maxPar (recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam) := by
    rw [maxPar_eq]
    exact Real.iSup_nonneg fun v => (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le
  have h1 : (1 : ℝ) ≤ 1 + |lam| := by linarith [abs_nonneg lam]
  calc maxPar (recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam) ^ (η ^ 6) ≤ (1 + |lam|) ^ (η ^ 6) :=
        Real.rpow_le_rpow hmp0 hmp (by positivity)
    _ ≤ (1 + |lam|) ^ (6 * η ^ 6) := Real.rpow_le_rpow_of_exponent_le h1 (by nlinarith [pow_pos hη 6])

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
