/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.TermNat2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.FlatBase
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Step3FinalH

/-! # P4-W2 (session 12, step 5a): the product of the native row sizes

`prod_rowBoundH_le`: `∏_ρ C · 2 rowBoundH ρ ≤ ofReal ((cf · 2 · rowCb · C₁²)^{2M} (2 C₁² δ)^{Sn} L^{-(γ₁-√η) M₁} · regionLeafSize)` with `cf = max C.toReal 1`
(the hypothesis `hrows` of `engine_rhs` for the native rows, with `Kr ≥ cf · 2 · rowCb · C₁²`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
open scoped ENNReal

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem prod_C_le {ι : Type*} [Fintype ι] {C : ℝ≥0∞} (hC : C ≠ ⊤) (cf : ℝ) (hcf : C.toReal ≤ cf) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∏ i, (C * ENNReal.ofReal (x i)) ≤ ENNReal.ofReal (∏ i, (cf * x i)) := by
  have hcf0 : 0 ≤ cf := (ENNReal.toReal_nonneg).trans hcf
  have hC' : C ≤ ENNReal.ofReal cf := by
    rw [← ENNReal.ofReal_toReal hC]; exact ENNReal.ofReal_le_ofReal hcf
  refine (Finset.prod_le_prod' fun i _ => mul_le_mul_left hC' _).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg hcf0 (hx i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_mul hcf0]

theorem prod_rowBoundH_le {P : WTParams} {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ} (hB : ProfileBound P h Bh p)
    (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
    (W : SumintWeightClockData (assemblyShape hM9 B) P.d) (hg : W.g = rowCoupleG hM9 B RD hG layer hLayer)
    (hg' : W.g' = rowTreeG hM9 B RD hG layer hLayer) (hL : 0 < P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (cf : ℝ) (hcf : C.toReal ≤ cf) :
    ∏ ρ : WaveTurbulence.VineEstS3.Eng.Row (sourceSumintDatum hM9 B hG W), (C * ENNReal.ofReal (2 * rowBoundH hM9 B RD hG layer hLayer P Bh W ρ)) ≤
      ENNReal.ofReal ((cf * 2 * (rowCb P * P.C₁ ^ 2)) ^ (2 * clLocalOrder1 R) *
        (2 * P.C₁ ^ 2 * P.δ) ^ ((∑ v : (assemblyShape hM9 B).VIdx, (rowCouple hM9 B RD hG v).size / 2) +
          ∑ v : (assemblyShape hM9 B).VIdx, (rowTree hM9 B RD v).size / 2) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((sourceSumintDatum hM9 B hG W).M₁ : ℝ)) *
        regionLeafSize RD hG R layer hLayer Bh) := by
  classical
  have hrb : ∀ ρ, 0 ≤ rowBound hM9 B RD hG layer hLayer P W ρ := by
    intro ρ
    rcases ρ with v | v <;> exact (rowB_pos (P := P) hC1 hδ hL _ _).le
  have hc := rowCostH_nonneg (hLayer := hLayer) hB hlay W
  have e1 : ∀ ρ : WaveTurbulence.VineEstS3.Eng.Row (sourceSumintDatum hM9 B hG W),
      C * ENNReal.ofReal (2 * rowBoundH hM9 B RD hG layer hLayer P Bh W ρ) =
        (C * ENNReal.ofReal (2 * rowBound hM9 B RD hG layer hLayer P W ρ)) *
          ENNReal.ofReal (rowCostH hM9 B RD hG layer hLayer Bh W ρ) := by
    intro ρ
    unfold rowBoundH
    have h2 : ENNReal.ofReal (2 * (rowBound hM9 B RD hG layer hLayer P W ρ * rowCostH hM9 B RD hG layer hLayer Bh W ρ)) =
        ENNReal.ofReal (2 * rowBound hM9 B RD hG layer hLayer P W ρ) *
          ENNReal.ofReal (rowCostH hM9 B RD hG layer hLayer Bh W ρ) := by
      rw [← ENNReal.ofReal_mul (by have := hrb ρ; linarith)]; congr 1; ring
    rw [h2, mul_assoc]
  rw [Finset.prod_congr rfl (fun ρ _ => e1 ρ), Finset.prod_mul_distrib,
    ← ENNReal.ofReal_prod_of_nonneg (fun ρ _ => hc ρ), prod_rowCostH_eq hM9 B RD hG layer hLayer Bh W]
  have hx : ∀ ρ, 0 ≤ 2 * rowBound hM9 B RD hG layer hLayer P W ρ := fun ρ => by have := hrb ρ; linarith
  have hlf : 0 ≤ regionLeafSize RD hG R layer hLayer Bh := by
    rw [← prod_rowCostH_eq hM9 B RD hG layer hLayer Bh W]
    exact Finset.prod_nonneg fun ρ _ => hc ρ
  refine (mul_le_mul' (prod_C_le hC cf hcf _ hx) le_rfl).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun ρ _ => mul_nonneg ((ENNReal.toReal_nonneg).trans hcf) (hx ρ)),
    prod_rowBound_eq hM9 B RD hG layer hLayer P W hL hg hg' cf]

end WaveTurbulence.VineEstS5C.P4.W2
