/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WB.W2.RowsS
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatRows

/-! # V5W-B-WORLD B3: all selected rows, and the certificate of a native term

`natRows_familyS` (main `W2.natRows_family`) and `termCertW_natS` (main `W2.termCertW_nat`) for every selector.
Copied by source from main 416902c8 (`W2/NatRows.lean, W2/TermNat4.lean`, see `COPIED-SHA256SUMS`); the edits are exactly: the selector is
bound inside the constants (`∀ {u} [_I : RowSel u]`), the weighted-selector hypothesis `hsel : SelOK P p` follows
`hp`, the clock data of the leaf rows carry `hqW`/`hqoW` (both `rfl` for `termW`/`recW`), the `(rowSel := plain)`
pins are dropped, and the names carry the suffix `S`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Flower.V5WB
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B
open scoped ENNReal
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P2 MeasureTheory
open scoped ENNReal
open WaveTurbulence.VineEstS5C.P4.W2

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **All native rows as `RowData`.** -/
theorem natRows_familyS (d : ℕ) (η : ℝ) (hd : 1 ≤ d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {u : Unit} [_I : VineEst.RowSel u] (P : WTParams), P.d = d → P.η = η →
      ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ},
      ∀ {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ}
      (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
      (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2) (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L)
      (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) (hp : p < P.D) (hsel : SelOK P p) (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
      (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
      (W : SumintWeightClockData (assemblyShape hM9 B) P.d)
      (hqW : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
      (hqoW : W.qOut 0 = layer (RD.coreBranch hG a).toNode)
      (hel : ∀ v, CoupleEligible hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v ∧
        TreeEligible hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v)
      (hqq : ∀ v, (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 ≤
        (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1)
      (wN wDec : ℕ) (hwN : wN + 1 = 30 * P.d) (hwDec : wDec = 30 * P.d)
      (bk : Fin (assemblyShape hM9 B).I → Fin 4)
      (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ),
      ∃ Rw : ∀ ρ : WaveTurbulence.VineEstS3Par.Eng.Row (engDatum hM9 B hG W wN wDec bk cons g g'),
          RowData (engDatum hM9 B hG W wN wDec bk cons g g') (6 * P.η ^ 6) ρ,
        (∀ ρ (cl : Fin 3 → ℝ), ![cl 0, cl 1] ∈ rowBx hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ → ∀ r k,
          (Rw ρ).W cl r k = (assemblyClockedS hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ ![cl 0, cl 1] k) ∧
        (∀ ρ i, (Rw ρ).slot i = natSlot hM9 B hG ρ i) ∧
        (∀ ρ, (Rw ρ).b ≤ C * ENNReal.ofReal (2 * rowBoundH hM9 B RD hG layer hLayer P Bh W ρ)) ∧
        (∀ ρ, (Rw ρ).Ae (assemblyShape_I_pos hM9 B)) ∧
        (∀ ρ cl r k, (Rw ρ).W cl r k = ∑' m, (Rw ρ).c m r k * WaveTurbulence.VineEstS3.FS.fsPhase m cl) := by
  obtain ⟨C, hC0, hCall⟩ := natRowHS d η hd
  refine ⟨C, hC0, fun {u} _I P hPd hPη {w G U a b R n} {h Bh p} hgate hinc hη6 hη2 hC hδ hL hw hp hsel hB hBpos hM9 B RD hG layer hLayer hlay W hqW hqoW hel hqq wN wDec hwN hwDec
    bk cons g g' => ?_⟩
  have := fun ρ => hCall P hPd hPη hgate hinc hη6 hη2 hC hδ hL hw hp hsel hB hBpos hM9 B RD hG layer hLayer hlay W hqW hqoW hel hqq wN wDec hwN hwDec
    bk cons g g' ρ (natSlot hM9 B hG ρ)
  choose Rw hW hS hb hAe hWs using this
  exact ⟨Rw, hW, fun ρ i => hS ρ i, hb, hAe, hWs⟩



end WaveTurbulence.Flower.V5WB
