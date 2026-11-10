/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatRows
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.DomEng

/-! # P4-W2 (session 10, step 4.4): the native rows inside the clocked integrand

`allCR_W_eq_natCR3`: at clocks in the row boxes, the weights of the family `Rw` of native rows (`natRows_family`) are those of `natCR3`
(the weights `KQstar`/`KTstar` of the native couples and chains).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

section
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
  (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
  (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
  (RD : ReconstructionData G) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (RD.forest hG) → ℕ)
  (hLayer : IsLayering (RD.garden hG) layer)

theorem natCR3_W_eq (ρ : Row (engDatum hM9 B hG W wN wDec bk cons g g')) (cl : Fin 3 → ℝ) (r k : Mom d) :
    (natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).W ρ cl r k =
      (assemblyClockedS hM9 B RD hG W L γ δ F layer hLayer).W ρ ![cl 0, cl 1] k := by
  rcases ρ with v | v <;> rfl

theorem natCR3_clock_eq (τ : (assemblyShape hM9 B).TVar → ℝ) (tt : Fin 3 → ℝ) (ρ : Row (engDatum hM9 B hG W wN wDec bk cons g g')) :
    ![(natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).clock τ tt ρ 0,
      (natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).clock τ tt ρ 1] =
      (assemblyClockedS hM9 B RD hG W L γ δ F layer hLayer).clock τ tt ρ := by
  funext i
  fin_cases i <;> rcases ρ with v | v <;> rfl


end

section
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
  (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
  (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
  (RD : ReconstructionData G) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (RD.forest hG) → ℕ)
  (hLayer : IsLayering (RD.garden hG) layer) {θ : ℝ}
  (Rw : ∀ ρ : Row (engDatum hM9 B hG W wN wDec bk cons g g'), RowData (engDatum hM9 B hG W wN wDec bk cons g g') θ ρ)
  (hRW : ∀ ρ (cl : Fin 3 → ℝ), ![cl 0, cl 1] ∈ rowBx hM9 B RD hG layer hLayer W L γ δ F ρ → ∀ r k,
    (Rw ρ).W cl r k = (assemblyClockedS hM9 B RD hG W L γ δ F layer hLayer).W ρ ![cl 0, cl 1] k)
  (hRS : ∀ ρ i, (Rw ρ).slot i = natSlot hM9 B hG ρ i)


end

end WaveTurbulence.VineEstS5C.P4.W2
