/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.ConjRowsH
public import WaveTurbulence.Foundations.VineEst.VineEstS3.NativeRows
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Data

/-! # Native rows of the chain for the layer family `h` with leaf cost (Step 3 port, R45)

Copy-and-edit of `VineEstS3.NativeRows` (`coupleRow_le`, `treeRow_le`) and of `Step3Data.rows_continuous` onto the
H-gates.  `rowBoundH ρ = rowBound ρ * rowCostH ρ`, where `rowCostH ρ = layerCost Bh (native garden of ρ)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.LGSpine
  VineParamContract TTree Reg Reg.Skeleton RegRed
open scoped ENNReal
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

section
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The leaf cost of a row: `layerCost Bh` of its native garden. -/
noncomputable def rowCostH (Bh : ℕ → ℝ) (W : SumintWeightClockData (assemblyShape hM9 B) d) :
    Row (sourceSumintDatum hM9 B hG W) → ℝ
  | Sum.inl v => layerCost Bh (rowCoupleLG hM9 B RD hG layer hLayer v)
  | Sum.inr v => layerCost Bh (rowTreeLG hM9 B RD hG layer hLayer v)

/-- The size bound of a row with its leaf cost. -/
noncomputable def rowBoundH (P : WTParams) (Bh : ℕ → ℝ) (W : SumintWeightClockData (assemblyShape hM9 B) P.d)
    (ρ : Row (sourceSumintDatum hM9 B hG W)) : ℝ :=
  rowBound hM9 B RD hG layer hLayer P W ρ * rowCostH hM9 B RD hG layer hLayer Bh W ρ

variable {hM9 B RD hG layer hLayer}
variable {P : WTParams} {p : ℕ}

theorem rowCostH_nonneg {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} (hB : ProfileBound P h Bh p)
    (hlay : ∀ x, layer x ≤ p) (W : SumintWeightClockData (assemblyShape hM9 B) P.d)
    (ρ : Row (sourceSumintDatum hM9 B hG W)) : 0 ≤ rowCostH hM9 B RD hG layer hLayer Bh W ρ := by
  rcases ρ with v | v
  · exact layerCost_nonneg_of hB _ (rowCouple_layer_le hlay v)
  · exact layerCost_nonneg_of hB _ (rowTree_layer_le hlay v)

/-- **Row bound, couples** (layer family, leaf cost). -/
theorem coupleRow_leaf_le (W : SumintWeightClockData (assemblyShape hM9 B) P.d) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    (hp : p < P.D) (hB : ProfileBound P h Bh p)
    (hlay : ∀ x, layer x ≤ p) (v : (assemblyShape hM9 B).VIdx)
    (hel : CoupleEligible hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) (30 * P.d)
      (timeBox (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inl v)).1
        (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inl v)).2) Set.univ
      (fun ts k => KQstar P.L P.γ P.δ h (rowCoupleLG hM9 B RD hG layer hLayer v) (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P ((rowCouple hM9 B RD hG v).size / 2) (rowCoupleG hM9 B RD hG layer hLayer v) *
        layerCost Bh (rowCoupleLG hM9 B RD hG layer hLayer v)) := by
  obtain ⟨hq, hq', hn, hr0, hr1, hcoh⟩ := hel
  have hwf : (rowCouple hM9 B RD hG v).wf = true := RD.couple_wf _
  have hsize : (rowCouple hM9 B RD hG v).size = 2 * ((rowCouple hM9 B RD hG v).size / 2) :=
    (Nat.two_mul_div_two_of_even (code_size_even _)).symm
  exact couple_row_leaf_le_both hgate hinc hd hη6 hη2 hC hδ hL hw hp hB hn hq hq' hwf hsize (rowCouple_decodes v)
    (rowCouple_layer_le hlay v) hr0 hr1 hcoh

/-- **Row bound, trees** (layer family, leaf cost). -/
theorem treeRow_leaf_le (W : SumintWeightClockData (assemblyShape hM9 B) P.d) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    (hp : p < P.D) (hB : ProfileBound P h Bh p)
    (hlay : ∀ x, layer x ≤ p) (v : (assemblyShape hM9 B).VIdx)
    (hel : TreeEligible hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) 0
      (timeBoxGt (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1
        (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2) Set.univ
      (fun ts k => KTstar P.L P.γ P.δ h (rowTreeLG hM9 B RD hG layer hLayer v) (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P ((rowTree hM9 B RD v).size / 2) (rowTreeG hM9 B RD hG layer hLayer v) *
        layerCost Bh (rowTreeLG hM9 B RD hG layer hLayer v)) := by
  obtain ⟨hqq, hqp, hn, hr0, hlone, hcoh⟩ := hel
  have hwf : (rowTree hM9 B RD v).wf = true := RD.tree_wf _
  have hsize : (rowTree hM9 B RD v).size = 2 * ((rowTree hM9 B RD v).size / 2) :=
    (Nat.two_mul_div_two_of_even (chain_size_even _)).symm
  exact tree_row_leaf_le hgate hinc hd hη6 hη2 hC hδ hL hw hp hB hn hqq hqp hwf hsize (rowTree_decodes v)
    (rowTree_layer_le hlay v) hr0 hlone hcoh

/-- **`hcont` of the engine** for the layer family `h`: the starred kernels are continuous in the clock pair. -/
theorem rows_continuousH {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} (hB : ProfileBound P h Bh p) (hd : 1 ≤ P.d)
    (hL : 1 ≤ P.L) (hlay : ∀ x, layer x ≤ p)
    (W : SumintWeightClockData (assemblyShape hM9 B) P.d) (ρ : Row (sourceSumintDatum hM9 B hG W)) (k : Mom P.d) :
    Continuous fun t : Fin 2 → ℝ =>
      (assemblyClocked hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ t k := by
  have hsum : ∀ ℓ : ℕ, ℓ ≤ p → Summable fun n : Fin P.d → ℤ => |h ℓ (k + latticePoint P.L n)| := fun ℓ hℓ =>
    summable_abs_coset_of_SNormR (A := 40 * P.d) (B := 40 * P.d) hL (by omega) (hB ℓ hℓ).1 (h ℓ) (hB ℓ hℓ).2 k
  rcases ρ with v | v
  · have hplain : (rowCoupleLG hM9 B RD hG layer hLayer v).garden.IsPlain := by
      unfold rowCoupleLG
      rw [nativeCoupleLayered_garden]
      exact (decodedCouple_decodes _).1.1
    exact continuous_KQstar_time P.L P.γ P.δ h (rowCoupleLG hM9 B RD hG layer hLayer v) hplain k
      (fun ℓ _ => hsum _ (hlay _))
  · have hT : IsPairedTree (rowTreeLG hM9 B RD hG layer hLayer v).garden := by
      unfold rowTreeLG
      exact decodedTree_isPairedTree _ _
    exact continuous_KTstar_time P.L P.γ P.δ h (rowTreeLG hM9 B RD hG layer hLayer v) hT k
      (fun ℓ _ => hsum _ (hlay _))

end

end WaveTurbulence.VineEstS5C
