/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatFree
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowAsm
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcRec

/-! # P4-W2 (session 13, step 2d): the row identity of a term with exceptional records

`hrow_exc_allCR`: the generalisation of `hrow_native_allCR`.  The pair rows `Vp` and the tree rows `Vb` of the exceptional records are matched jointly (`hX`: the
product of the exceptional weights is `C` times the product of the engine rows there), every other row is the native row (`hRW`, `hRS` restricted to the
non-exceptional rows).  The constant `C` is `kind1Pref · k2c` of the engine datum.
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
  (hLayer : IsLayering (RD.garden hG) layer) {θ : ℝ}
  (Rw : ∀ ρ : Row (engDatum hM9 B hG W wN wDec bk cons g g'), RowData (engDatum hM9 B hG W wN wDec bk cons g g') θ ρ)
  (Vp Vb : Finset (assemblyShape hM9 B).VIdx)

/-- The rows other than the pair rows `Vp` and the tree rows `Vb`. -/
def NonExc (ρ : Row (engDatum hM9 B hG W wN wDec bk cons g g')) : Prop :=
  (∀ v, ρ = Sum.inl v → v ∉ Vp) ∧ (∀ v, ρ = Sum.inr v → v ∉ Vb)


theorem nonExc_inl (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (Vp Vb : Finset (assemblyShape hM9 B).VIdx) {v : (assemblyShape hM9 B).VIdx} (hv : v ∉ Vp) :
    NonExc hM9 B hG W wN wDec bk cons g g' Vp Vb (Sum.inl v) :=
  ⟨fun _ h => (Sum.inl.inj h) ▸ hv, (fun _ h => nomatch h)⟩

theorem nonExc_inr (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (Vp Vb : Finset (assemblyShape hM9 B).VIdx) {v : (assemblyShape hM9 B).VIdx} (hv : v ∉ Vb) :
    NonExc hM9 B hG W wN wDec bk cons g g' Vp Vb (Sum.inr v) :=
  ⟨(fun _ h => nomatch h), fun _ h => (Sum.inr.inj h) ▸ hv⟩

variable
  (hRW : ∀ ρ (cl : Fin 3 → ℝ), NonExc hM9 B hG W wN wDec bk cons g g' Vp Vb ρ →
    ![cl 0, cl 1] ∈ rowBx hM9 B RD hG layer hLayer W L γ δ F ρ → ∀ r k,
    (Rw ρ).W cl r k = (assemblyClockedS hM9 B RD hG W L γ δ F layer hLayer).W ρ ![cl 0, cl 1] k)
  (hRS : ∀ ρ i, NonExc hM9 B hG W wN wDec bk cons g g' Vp Vb ρ → (Rw ρ).slot i = natSlot hM9 B hG ρ i)

include hRW hRS in
theorem allCR_W_eq_natCR3_exc (τ : (assemblyShape hM9 B).TVar → ℝ) (tt : Fin 3 → ℝ)
    (ρ : Row (engDatum hM9 B hG W wN wDec bk cons g g')) (hρ : NonExc hM9 B hG W wN wDec bk cons g g' Vp Vb ρ)
    (hclk : (assemblyClockedS hM9 B RD hG W L γ δ F layer hLayer).clock τ tt ρ ∈
      rowBx hM9 B RD hG layer hLayer W L γ δ F ρ) (r k : Mom d) :
    (allCR Rw).W ρ ((allCR Rw).clock τ tt ρ) r k =
      (natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).W ρ
        ((natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).clock τ tt ρ) r k := by
  have hcl : (allCR Rw).clock τ tt ρ =
      (natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).clock τ tt ρ := by
    funext i
    change slotVal (engDatum hM9 B hG W wN wDec bk cons g g') τ tt ((Rw ρ).slot i) =
      slotVal (engDatum hM9 B hG W wN wDec bk cons g g') τ tt (natSlot hM9 B hG ρ i)
    rw [hRS ρ i hρ]
  rw [hcl, natCR3_W_eq]
  have hmem := hclk
  rw [← natCR3_clock_eq hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer τ tt ρ] at hmem
  exact hRW ρ _ hρ hmem r k

end

section
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
  (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
  (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
  (RD : ReconstructionData G) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (RD.forest hG) → ℕ)
  (hLayer : IsLayering (RD.garden hG) layer) {θ : ℝ}
  (Rw : ∀ ρ : Row (engDatum hM9 B hG W wN wDec bk cons g g'), RowData (engDatum hM9 B hG W wN wDec bk cons g g') θ ρ)
  (Vp Vb : Finset (assemblyShape hM9 B).VIdx)
  (hRW : ∀ ρ (cl : Fin 3 → ℝ), NonExc hM9 B hG W wN wDec bk cons g g' Vp Vb ρ →
    ![cl 0, cl 1] ∈ rowBx hM9 B RD hG layer hLayer W L γ δ F ρ → ∀ r k,
    (Rw ρ).W cl r k = (assemblyClockedS hM9 B RD hG W L γ δ F layer hLayer).W ρ ![cl 0, cl 1] k)
  (hRS : ∀ ρ i, NonExc hM9 B hG W wN wDec bk cons g g' Vp Vb ρ → (Rw ρ).slot i = natSlot hM9 B hG ρ i)

include hRW hRS in
/-- **The row identity of a term with exceptional records.** -/
theorem hrow_exc_allCR (hL : L ≠ 0) (η : ℝ) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ) (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ))
    (τ : (assemblyShape hM9 B).TVar → ℝ) (Pex : Finset (SourcePair G)) (Bex : Finset (GBranch G.tree))
    (Xq : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ)
    (hVp : ∀ v, v ∈ Vp ↔ (assemblyPairOf hM9 B hG v).1 ∈ Pex)
    (hVb : ∀ v, v ∈ Vb ↔ (assemblyBranchOf hM9 B v).1 ∈ Bex)
    (hclk : ∀ ρ, NonExc hM9 B hG W wN wDec bk cons g g' Vp Vb ρ →
      (assemblyClockedS hM9 B RD hG W L γ δ F layer hLayer).clock τ tt ρ ∈ rowBx hM9 B RD hG layer hLayer W L γ δ F ρ)
    (hX : (∏ v ∈ Vp, Xq (assemblyPairOf hM9 B hG v).1 tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ))
          (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)) =
      ((kind1Pref (D := engDatum hM9 B hG W wN wDec bk cons g g')
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) : ℝ) : ℂ) * k2c bk η τ *
        (∏ v ∈ Vp, (allCR Rw).W (Sum.inl v) ((allCR Rw).clock τ tt (Sum.inl v))
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1)
          (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
            (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) (Sum.inl v))) *
        ∏ v ∈ Vb, (allCR Rw).W (Sum.inr v) ((allCR Rw).clock τ tt (Sum.inr v))
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1)
          (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
            (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) (Sum.inr v))) :
    (∏ p ∈ clRegionalPairs hG U, (if p ∈ Pex then Xq p tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ))
          (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
        else qRow RD hG L γ δ F layer hLayer base (tt 0) (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
          (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) p)) *
      (∏ v ∈ U.erase a, (if v ∈ Bex then 1 else tRow RD hG L γ δ F layer hLayer base (tt 0)
          (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
          (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) v)) =
    ((kind1Pref (D := engDatum hM9 B hG W wN wDec bk cons g g')
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) : ℝ) : ℂ) * k2c bk η τ *
      ∏ ρ, (allCR Rw).W ρ ((allCR Rw).clock τ tt ρ)
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
          sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1)
        (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) ρ) := by
  classical
  have hnat := fun ρ hρ => allCR_W_eq_natCR3_exc hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer Rw Vp Vb hRW hRS τ tt ρ hρ
    (hclk ρ hρ)
  have h := hrow_of_rowwise_exc (a := a) hM9 B hG
    (fun p => if p ∈ Pex then Xq p tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ))
          (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
        else qRow RD hG L γ δ F layer hLayer base (tt 0) (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
          (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) p)
    (fun v => if v ∈ Bex then 1 else tRow RD hG L γ δ F layer hLayer base (tt 0)
          (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
          (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) v)
    (fun ρ => (allCR Rw).W ρ ((allCR Rw).clock τ tt ρ)
      (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
        sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1)
      (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) ρ))
    (fun _ => 1) (fun _ => 1) Vp Vb
    (((kind1Pref (D := engDatum hM9 B hG W wN wDec bk cons g g')
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) : ℝ) : ℂ) * k2c bk η τ)
    (fun v hv => by
      have hnp : (assemblyPairOf hM9 B hG v).1 ∉ Pex := fun h' => hv ((hVp v).mpr h')
      simp only [hnp, if_false]
      refine ((qRow_eq_natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer base
        (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) tt τ
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
          sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) v).trans
        (by rw [← pairMom_eq hM9 B hG W wN wDec bk cons g g' hL base β hβ x v]
            exact (hnat (Sum.inl v) (nonExc_inl hM9 B hG W wN wDec bk cons g g' Vp Vb hv) _ _).symm)).trans (one_mul _).symm)
    (fun v hv => by
      have hnb : (assemblyBranchOf hM9 B v).1 ∉ Bex := fun h' => hv ((hVb v).mpr h')
      simp only [hnb, if_false]
      refine ((tRow_eq_natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer base
        (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) tt τ
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
          sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) v).trans
        (by rw [← branchMom_eq hM9 B hG W wN wDec bk cons g g' hL base β hβ x v]
            exact (hnat (Sum.inr v) (nonExc_inr hM9 B hG W wN wDec bk cons g g' Vp Vb hv) _ _).symm)).trans (one_mul _).symm)
    (by
      have e1 : ∏ v ∈ Vp, (if (assemblyPairOf hM9 B hG v).1 ∈ Pex then Xq (assemblyPairOf hM9 B hG v).1 tt
          (clLocalClock R tt (assemblyClockEquiv hM9 B τ))
          (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) else
          qRow RD hG L γ δ F layer hLayer base (tt 0) (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
            (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) (assemblyPairOf hM9 B hG v).1) =
          ∏ v ∈ Vp, Xq (assemblyPairOf hM9 B hG v).1 tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ))
          (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) :=
        Finset.prod_congr rfl fun v hv => if_pos ((hVp v).mp hv)
      have e2 : ∏ v ∈ Vb, (if (assemblyBranchOf hM9 B v).1 ∈ Bex then (1 : ℂ) else
          tRow RD hG L γ δ F layer hLayer base (tt 0) (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
            (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) (assemblyBranchOf hM9 B v).1) = 1 :=
        Finset.prod_eq_one fun v hv => if_pos ((hVb v).mp hv)
      rw [e1, e2, mul_one, hX]
      rfl)
  simp only [Finset.prod_const_one, mul_one] at h
  convert h using 2
  rfl

end

end WaveTurbulence.VineEstS5C.P4.W2
