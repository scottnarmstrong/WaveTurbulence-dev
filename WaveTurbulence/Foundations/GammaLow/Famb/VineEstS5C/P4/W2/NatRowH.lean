/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatRow
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowMatch
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Step3AtH
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatRowH
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RowMatch
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Step3AtH
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatRowH` (sha256 d310228d56642966…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (step 1, session 7): the native rows as `RowData` with the leaf-cost bound

`natRows_res`: the hypothesis `hres` of `step3AtLeafH` (the gate bound `XNormRestr (6η⁶) (30d) _ (rowBx ρ) univ (assemblyClockedS.W ρ) <
ofReal (2 rowBoundH ρ)`), extracted from `coupleRow_leaf_le`/`treeRow_leaf_le`.  `natRowH`: the row `ρ` of the engine datum
`engDatum ..` (any `W, wN, wDec, bk, cons, g, g'` with `wN + 1 = 30 d`, `wDec = 30 d`) is a `RowData` of any slot triple whose weight is
`(assemblyClockedS ..).W ρ` on the box `rowBx ρ` and whose size is `≤ C · ofReal (2 rowBoundH ρ)`, with `Ae`. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P2 MeasureTheory WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P2
open scoped ENNReal

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **`hres` of `step3AtLeafH`**: the native rows obey the leaf-cost gate bound. -/
theorem natRows_resΓ {P : WTParams} (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2) (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L)
    (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) {p : ℕ} (hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
    (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
    (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d)
    (hel : ∀ v, CoupleEligibleΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v ∧
      TreeEligibleΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v)
    (ρ : VineEstS3.Eng.Row (sourceSumintDatumΓ hM9 B hG W)) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) (VineEstS3.Eng.rowOrder (sourceSumintDatumΓ hM9 B hG W) ρ)
      (rowBxΓ hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ) Set.univ
      ((assemblyClockedSΓ (rowSel := VineEst.RowSel.plain) hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ) <
      ENNReal.ofReal (2 * rowBoundHΓ hM9 B RD hG layer hLayer P Bh W ρ) := by
  have hL0 : 0 < P.L := by linarith
  rcases ρ with v | v
  · have h1 := coupleRow_leaf_leΓ W hgate hinc hd hη6 hη2 hC hδ.le hL hw hp hB hlay v (hel v).1
    have hx : 0 < rowBoundHΓ hM9 B RD hG layer hLayer P Bh W (Sum.inl v) :=
      mul_pos (rowB_pos hC hδ hL0 _ _) (rowCostH_posΓ hBpos hlay W _)
    refine h1.trans_lt ?_
    change ENNReal.ofReal (rowBoundHΓ hM9 B RD hG layer hLayer P Bh W (Sum.inl v)) < _
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  · have h1 := treeRow_leaf_leΓ W hgate hinc hd hη6 hη2 hC hδ.le hL hw hp hB hlay v (hel v).2
    have hx : 0 < rowBoundHΓ hM9 B RD hG layer hLayer P Bh W (Sum.inr v) :=
      mul_pos (rowB_pos hC hδ hL0 _ _) (rowCostH_posΓ hBpos hlay W _)
    refine h1.trans_lt ?_
    change ENNReal.ofReal (rowBoundHΓ hM9 B RD hG layer hLayer P Bh W (Sum.inr v)) < _
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)

/-- **A native row of the engine datum as a `RowData`, with the leaf-cost bound** (`natRowData` specialised to `assemblyClockedS`). -/
theorem natRowHΓ (d : ℕ) (η : ℝ) (hd : 1 ≤ d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (P : WTParams), P.d = d → P.η = η →
      ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ},
      ∀ {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ}
      (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
      (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2) (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L)
      (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) (hp : p < P.D) (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
      (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
      (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d)
      (hel : ∀ v, CoupleEligibleΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v ∧
        TreeEligibleΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v)
      (hqq : ∀ v, (rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 ≤
        (rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1)
      (wN wDec : ℕ) (hwN : wN + 1 = 30 * P.d) (hwDec : wDec = 30 * P.d)
      (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4)
      (cons : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ)
      (ρ : WaveTurbulence.VineEstS3Par.Eng.Row (engDatumΓ hM9 B hG W wN wDec bk cons g g'))
      (slot : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot (engDatumΓ hM9 B hG W wN wDec bk cons g g')),
      ∃ Rr : RowData (engDatumΓ hM9 B hG W wN wDec bk cons g g') (6 * P.η ^ 6) ρ,
        (∀ cl : Fin 3 → ℝ, ![cl 0, cl 1] ∈ rowBxΓ hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ → ∀ r k,
          Rr.W cl r k = (assemblyClockedSΓ (rowSel := VineEst.RowSel.plain) hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ ![cl 0, cl 1] k) ∧
        (∀ i, Rr.slot i = slot i) ∧
        Rr.b ≤ C * ENNReal.ofReal (2 * rowBoundHΓ hM9 B RD hG layer hLayer P Bh W ρ) ∧
        Rr.Ae (assemblyShape_I_posΓ hM9 B) ∧ (∀ cl r k, Rr.W cl r k = ∑' m, Rr.c m r k * WaveTurbulence.VineEstS3.FS.fsPhase m cl) := by
  obtain ⟨C, hC0, hCall⟩ := natRowData d η hd
  refine ⟨C, hC0, fun P hPd hPη {w G U a b R n} {h Bh p} hgate hinc hη6 hη2 hC hδ hL hw hp hB hBpos hM9 B RD hG layer hLayer hlay W hel hqq wN wDec hwN hwDec
    bk cons g g' ρ slot => ?_⟩
  subst hPd hPη
  have hres := natRows_resΓ hgate hinc hd hη6 hη2 hC hδ hL hw hp hB hBpos hM9 B RD hG layer hLayer hlay W hel ρ
  have hord : VineEstS3.Eng.rowOrder (sourceSumintDatumΓ hM9 B hG W) ρ =
      WaveTurbulence.VineEstS3Par.Eng.rowOrder (engDatumΓ hM9 B hG W wN wDec bk cons g g') ρ := by
    rcases ρ with v | v
    · simp [VineEstS3.Eng.rowOrder, WaveTurbulence.VineEstS3Par.Eng.rowOrder, hwDec]
      rfl
    · rfl
  rw [hord] at hres
  exact hCall (engDatumΓ hM9 B hG W wN wDec bk cons g g') (assemblyShape_I_posΓ hM9 B) hwN hwDec ρ slot _ _
    ((assemblyClockedSΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ) _ ENNReal.ofReal_ne_top
    (rowBx_subset_cellΓ hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ)
    (rowBx_closureΓ hM9 B RD hG layer hLayer W P.L P.γ P.δ h hqq ρ)
    (fun k => rows_continuousHΓ hB hd hL hlay W ρ k) hres

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
