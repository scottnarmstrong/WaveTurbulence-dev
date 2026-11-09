/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatRows
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.FreeNE
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatFree
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.DomEng
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.NatRows
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatFree` (sha256 abe81580d1ef57af…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 10, step 4.4): the native rows inside the clocked integrand

`allCR_W_eq_natCR3`: at clocks in the row boxes, the weights of the family `Rw` of native rows (`natRows_family`) are those of `natCR3`
(the weights `KQstar`/`KTstar` of the native couples and chains).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS4

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

section
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
  (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4)
  (cons : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ)
  (RD : ReconstructionData G) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (RD.forest hG) → ℕ)
  (hLayer : IsLayering (RD.garden hG) layer)

theorem natCR3_W_eqΓ (ρ : Row (engDatumΓ hM9 B hG W wN wDec bk cons g g')) (cl : Fin 3 → ℝ) (r k : Mom d) :
    (natCR3Γ hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).W ρ cl r k =
      (assemblyClockedSΓ hM9 B RD hG W L γ δ F layer hLayer).W ρ ![cl 0, cl 1] k := by
  rcases ρ with v | v <;> rfl

theorem natCR3_clock_eqΓ (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) (tt : Fin 3 → ℝ) (ρ : Row (engDatumΓ hM9 B hG W wN wDec bk cons g g')) :
    ![(natCR3Γ hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).clock τ tt ρ 0,
      (natCR3Γ hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).clock τ tt ρ 1] =
      (assemblyClockedSΓ hM9 B RD hG W L γ δ F layer hLayer).clock τ tt ρ := by
  funext i
  fin_cases i <;> rcases ρ with v | v <;> rfl

end

section
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
  (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4)
  (cons : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ)
  (RD : ReconstructionData G) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (RD.forest hG) → ℕ)
  (hLayer : IsLayering (RD.garden hG) layer) {θ : ℝ}
  (Rw : ∀ ρ : Row (engDatumΓ hM9 B hG W wN wDec bk cons g g'), RowData (engDatumΓ hM9 B hG W wN wDec bk cons g g') θ ρ)
  (hRW : ∀ ρ (cl : Fin 3 → ℝ), ![cl 0, cl 1] ∈ rowBxΓ hM9 B RD hG layer hLayer W L γ δ F ρ → ∀ r k,
    (Rw ρ).W cl r k = (assemblyClockedSΓ hM9 B RD hG W L γ δ F layer hLayer).W ρ ![cl 0, cl 1] k)
  (hRS : ∀ ρ i, (Rw ρ).slot i = natSlotΓ hM9 B hG ρ i)

end

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
