/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.Bounds
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.ConjRowsH
public import WaveTurbulence.Foundations.VineEst.VineEstS3.NativeRows
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Data
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.NativeRowsH
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClause
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Final
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.Class
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.NativeRowsH` (sha256 6338321a1518828c…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Native rows of the chain for the layer family `h` with leaf cost (Step 3 port, R45)

Copy-and-edit of `VineEstS3.NativeRows` (`coupleRow_le`, `treeRow_le`) and of `Step3Data.rows_continuous` onto the
H-gates.  `rowBoundH ρ = rowBound ρ * rowCostH ρ`, where `rowCostH ρ = layerCost Bh (native garden of ρ)`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C
open WaveTurbulence.VineEstS5C
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.LGSpine WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3
  VineParamContract TTree Reg Reg.Skeleton RegRed
open scoped ENNReal
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

section
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The leaf cost of a row: `layerCost Bh` of its native garden. -/
noncomputable def rowCostHΓ (Bh : ℕ → ℝ) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) :
    Row (sourceSumintDatumΓ hM9 B hG W) → ℝ
  | Sum.inl v => layerCost Bh (rowCoupleLGΓ hM9 B RD hG layer hLayer v)
  | Sum.inr v => layerCost Bh (rowTreeLGΓ hM9 B RD hG layer hLayer v)

/-- The size bound of a row with its leaf cost. -/
noncomputable def rowBoundHΓ (P : WTParams) (Bh : ℕ → ℝ) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d)
    (ρ : Row (sourceSumintDatumΓ hM9 B hG W)) : ℝ :=
  rowBoundΓ hM9 B RD hG layer hLayer P W ρ * rowCostHΓ hM9 B RD hG layer hLayer Bh W ρ

variable {hM9 B RD hG layer hLayer}
variable {P : WTParams} {p : ℕ}

theorem rowCostH_nonnegΓ {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} (hB : ProfileBound P h Bh p)
    (hlay : ∀ x, layer x ≤ p) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d)
    (ρ : Row (sourceSumintDatumΓ hM9 B hG W)) : 0 ≤ rowCostHΓ hM9 B RD hG layer hLayer Bh W ρ := by
  rcases ρ with v | v
  · exact layerCost_nonneg_of hB _ (rowCouple_layer_leΓ hlay v)
  · exact layerCost_nonneg_of hB _ (rowTree_layer_leΓ hlay v)

/-- **Row bound, couples** (layer family, leaf cost). -/
theorem coupleRow_leaf_leΓ (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    (hp : p < P.D) (hB : ProfileBound P h Bh p)
    (hlay : ∀ x, layer x ≤ p) (v : (assemblyShapeΓ hM9 B).VIdx)
    (hel : CoupleEligibleΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) (30 * P.d)
      (timeBox (rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inl v)).1
        (rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inl v)).2) Set.univ
      (fun ts k => KQstar P.L P.γ P.δ h (rowCoupleLGΓ hM9 B RD hG layer hLayer v) (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P ((rowCoupleΓ hM9 B RD hG v).size / 2) (rowCoupleGΓ hM9 B RD hG layer hLayer v) *
        layerCost Bh (rowCoupleLGΓ hM9 B RD hG layer hLayer v)) := by
  obtain ⟨hq, hq', hn, hr0, hr1, hcoh⟩ := hel
  have hwf : (rowCoupleΓ hM9 B RD hG v).wf = true := RD.couple_wf _
  have hsize : (rowCoupleΓ hM9 B RD hG v).size = 2 * ((rowCoupleΓ hM9 B RD hG v).size / 2) :=
    (Nat.two_mul_div_two_of_even (code_size_even _)).symm
  exact couple_row_leaf_le_both hgate hinc hd hη6 hη2 hC hδ hL hw hp hB hn hq hq' hwf hsize (rowCouple_decodesΓ v)
    (rowCouple_layer_leΓ hlay v) hr0 hr1 hcoh

/-- **Row bound, trees** (layer family, leaf cost). -/
theorem treeRow_leaf_leΓ (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    (hp : p < P.D) (hB : ProfileBound P h Bh p)
    (hlay : ∀ x, layer x ≤ p) (v : (assemblyShapeΓ hM9 B).VIdx)
    (hel : TreeEligibleΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) 0
      (timeBoxGt (rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1
        (rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2) Set.univ
      (fun ts k => KTstar P.L P.γ P.δ h (rowTreeLGΓ hM9 B RD hG layer hLayer v) (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P ((rowTreeΓ hM9 B RD v).size / 2) (rowTreeGΓ hM9 B RD hG layer hLayer v) *
        layerCost Bh (rowTreeLGΓ hM9 B RD hG layer hLayer v)) := by
  obtain ⟨hqq, hqp, hn, hr0, hlone, hcoh⟩ := hel
  have hwf : (rowTreeΓ hM9 B RD v).wf = true := RD.tree_wf _
  have hsize : (rowTreeΓ hM9 B RD v).size = 2 * ((rowTreeΓ hM9 B RD v).size / 2) :=
    (Nat.two_mul_div_two_of_even (chain_size_even _)).symm
  exact tree_row_leaf_le hgate hinc hd hη6 hη2 hC hδ hL hw hp hB hn hqq hqp hwf hsize (rowTree_decodesΓ v)
    (rowTree_layer_leΓ hlay v) hr0 hlone hcoh

/-- **`hcont` of the engine** for the layer family `h`: the starred kernels are continuous in the clock pair. -/
theorem rows_continuousHΓ {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} (hB : ProfileBound P h Bh p) (hd : 1 ≤ P.d)
    (hL : 1 ≤ P.L) (hlay : ∀ x, layer x ≤ p)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d) (ρ : Row (sourceSumintDatumΓ hM9 B hG W)) (k : Mom P.d) :
    Continuous fun t : Fin 2 → ℝ =>
      (assemblyClockedSΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ t k := by
  have hsum : ∀ ℓ : ℕ, ℓ ≤ p → Summable fun n : Fin P.d → ℤ => |h ℓ (k + latticePoint P.L n)| := fun ℓ hℓ =>
    summable_abs_coset_of_SNormR (A := 40 * P.d) (B := 40 * P.d) hL (by omega) (hB ℓ hℓ).1 (h ℓ) (hB ℓ hℓ).2 k
  rcases ρ with v | v
  · have hplain : (rowCoupleLGΓ hM9 B RD hG layer hLayer v).garden.IsPlain := by
      unfold rowCoupleLGΓ
      rw [nativeCoupleLayered_garden]
      exact (decodedCouple_decodes _).1.1
    exact VineEst.continuous_KQsel_time _ _ _ P.L P.γ P.δ h (rowCoupleLGΓ hM9 B RD hG layer hLayer v) hplain k
      (fun ℓ _ => hsum _ (hlay _))
  · have hT : IsPairedTree (rowTreeLGΓ hM9 B RD hG layer hLayer v).garden := by
      unfold rowTreeLGΓ
      exact decodedTree_isPairedTree _ _
    exact VineEst.continuous_KTsel_time _ _ P.L P.γ P.δ h (rowTreeLGΓ hM9 B RD hG layer hLayer v) hT k
      (fun ℓ _ => hsum _ (hlay _))

end

end WaveTurbulence.GammaLow.Famb.VineEstS5C
