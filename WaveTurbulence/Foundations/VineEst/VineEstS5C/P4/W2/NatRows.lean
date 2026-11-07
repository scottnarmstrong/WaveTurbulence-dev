/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatRowH
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowMatch

/-! # P4-W2 (session 10, step 4.4): the family of native rows

`natRows_family`: all native rows of the engine datum at once, as a family `Rw ρ : RowData` with the row identification on the row boxes, the
native slots, the leaf-cost bound `b ≤ C · 2 rowBoundH` and the a.e. mode expansion (`natRowH`, `choose`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P2 MeasureTheory
open scoped ENNReal

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **All native rows as `RowData`.** -/
theorem natRows_family (d : ℕ) (η : ℝ) (hd : 1 ≤ d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (P : WTParams), P.d = d → P.η = η →
      ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ},
      ∀ {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ}
      (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
      (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2) (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L)
      (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) (hp : p < P.D) (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
      (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
      (W : SumintWeightClockData (assemblyShape hM9 B) P.d)
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
          (Rw ρ).W cl r k = (assemblyClockedS (rowSel := VineEst.RowSel.plain) hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ ![cl 0, cl 1] k) ∧
        (∀ ρ i, (Rw ρ).slot i = natSlot hM9 B hG ρ i) ∧
        (∀ ρ, (Rw ρ).b ≤ C * ENNReal.ofReal (2 * rowBoundH hM9 B RD hG layer hLayer P Bh W ρ)) ∧
        (∀ ρ, (Rw ρ).Ae (assemblyShape_I_pos hM9 B)) ∧
        (∀ ρ cl r k, (Rw ρ).W cl r k = ∑' m, (Rw ρ).c m r k * WaveTurbulence.VineEstS3.FS.fsPhase m cl) := by
  obtain ⟨C, hC0, hCall⟩ := natRowH d η hd
  refine ⟨C, hC0, fun P hPd hPη {w G U a b R n} {h Bh p} hgate hinc hη6 hη2 hC hδ hL hw hp hB hBpos hM9 B RD hG layer hLayer hlay W hel hqq wN wDec hwN hwDec
    bk cons g g' => ?_⟩
  have := fun ρ => hCall P hPd hPη hgate hinc hη6 hη2 hC hδ hL hw hp hB hBpos hM9 B RD hG layer hLayer hlay W hel hqq wN wDec hwN hwDec
    bk cons g g' ρ (natSlot hM9 B hG ρ)
  choose Rw hW hS hb hAe hWs using this
  exact ⟨Rw, hW, fun ρ i => hS ρ i, hb, hAe, hWs⟩

end WaveTurbulence.VineEstS5C.P4.W2
