/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatRows
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.FreeNE

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

include hRW hRS in
/-- **The weights of the family `Rw` at the clocks of `τ` are the native weights** (clocks in the row boxes). -/
theorem allCR_W_eq_natCR3 (τ : (assemblyShape hM9 B).TVar → ℝ) (tt : Fin 3 → ℝ)
    (hclk : ∀ ρ, (assemblyClockedS hM9 B RD hG W L γ δ F layer hLayer).clock τ tt ρ ∈
      rowBx hM9 B RD hG layer hLayer W L γ δ F ρ) (ρ : Row (engDatum hM9 B hG W wN wDec bk cons g g')) (r k : Mom d) :
    (allCR Rw).W ρ ((allCR Rw).clock τ tt ρ) r k =
      (natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).W ρ
        ((natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).clock τ tt ρ) r k := by
  have hcl : (allCR Rw).clock τ tt ρ =
      (natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).clock τ tt ρ := by
    funext i
    change slotVal (engDatum hM9 B hG W wN wDec bk cons g g') τ tt ((Rw ρ).slot i) =
      slotVal (engDatum hM9 B hG W wN wDec bk cons g g') τ tt (natSlot hM9 B hG ρ i)
    rw [hRS]
  rw [hcl, natCR3_W_eq]
  have hmem := hclk ρ
  rw [← natCR3_clock_eq hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer τ tt ρ] at hmem
  exact hRW ρ _ hmem r k


include hRW hRS in
/-- **The row identity of a term with native rows only**, for the family `Rw` of native rows. -/
theorem hrow_native_allCR (hL : L ≠ 0) (η : ℝ) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ) (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ))
    (τ : (assemblyShape hM9 B).TVar → ℝ) (hbk : ∀ i, bk i ≠ 1 ∧ bk i ≠ 2)
    (hclk : ∀ ρ, (assemblyClockedS hM9 B RD hG W L γ δ F layer hLayer).clock τ tt ρ ∈
      rowBx hM9 B RD hG layer hLayer W L γ δ F ρ) :
    (∏ p ∈ clRegionalPairs hG U, qRow RD hG L γ δ F layer hLayer base (tt 0)
        (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
        (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) p) *
      (∏ v ∈ U.erase a, tRow RD hG L γ δ F layer hLayer base (tt 0)
        (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
        (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) v) =
      ((kind1Pref (D := engDatum hM9 B hG W wN wDec bk cons g g')
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) : ℝ) : ℂ) * k2c bk η τ *
        ∏ ρ, (allCR Rw).W ρ ((allCR Rw).clock τ tt ρ)
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1)
          (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
            (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) ρ) := by
  rw [kind1Pref_eq_one hM9 B hG W wN wDec bk _ g g' (fun i => (hbk i).1),
    k2c_eq_one bk (fun i => (hbk i).2), Complex.ofReal_one, one_mul, one_mul]
  have hnat := allCR_W_eq_natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer Rw hRW hRS τ tt hclk
  have h := hrow_of_rowwise (a := a) hM9 B hG
    (fun p => qRow RD hG L γ δ F layer hLayer base (tt 0)
      (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
      (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) p)
    (fun v => tRow RD hG L γ δ F layer hLayer base (tt 0)
      (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
      (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) v)
    (fun ρ => (allCR Rw).W ρ ((allCR Rw).clock τ tt ρ)
      (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
        sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1)
      (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) ρ))
    (fun _ => 1) (fun _ => 1)
    (fun v => ((qRow_eq_natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer base
        (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) tt τ
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
          sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) v).trans
      (by rw [← pairMom_eq hM9 B hG W wN wDec bk cons g g' hL base β hβ x v]; exact (hnat (Sum.inl v) _ _).symm)).trans (one_mul _).symm)
    (fun v => ((tRow_eq_natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer base
        (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) tt τ
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
          sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) v).trans
      (by rw [← branchMom_eq hM9 B hG W wN wDec bk cons g g' hL base β hβ x v]; exact (hnat (Sum.inr v) _ _).symm)).trans (one_mul _).symm)
  simp only [Finset.prod_const_one, mul_one, one_mul] at h
  exact h

end

end WaveTurbulence.VineEstS5C.P4.W2
