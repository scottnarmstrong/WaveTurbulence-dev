/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecScale
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecUnif
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecOrd

/-! # P4-W2 (session 14, step 1d): the unit-absorbed two-row representation of a record summand

`PieceRepU hI vp vb ε f0 X bnd Bx`: rows `RK` (pair row `vp`, 𝒦) and `RL` (branch row `vb`, ℒ) with `RK.b * RL.b ≤ bnd`, their Fourier sums, and the identity
`X τ tt r k = f0 τ r * (RK.W .. r k * RL.W .. r (k + ε r))` a.e. on the time domain for `tt ∈ Bx`; the factor `f0` is the rigid part (`‖r‖` for kind `1`, the
kind-2 factor `|τ_{s} - τ_{t}|^{1-3η}`, or `1`), the units are absorbed in `RK`.  `pieceRepU_of_dispK01`, `pieceRepU_of_dispK2`: the dispatches give `PieceRepU` for `ν · bundlePtG ..` (`ν` unit).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS4c
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 MeasureTheory
open scoped ENNReal ComplexConjugate

universe u
variable {P : WTParams}

/-- **The unit-absorbed representation** (see the module docstring). -/
def PieceRepU {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (vp vb : D.S.VIdx) (ε : ℝ)
    (f0 : (D.S.TVar → ℝ) → Mom P.d → ℂ) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ) (bnd : ℝ≥0∞)
    (Bx : Set (Fin 3 → ℝ)) : Prop :=
  ∃ (RK : RowData D (6 * P.η ^ 6) (Sum.inl vp)) (RL : RowData D (6 * P.η ^ 6) (Sum.inr vb)),
    RK.Ae hI ∧ RL.Ae hI ∧
    (∀ cl r k, RK.W cl r k = ∑' m, RK.c m r k * fsPhase m cl) ∧
    (∀ cl r k, RL.W cl r k = ∑' m, RL.c m r k * fsPhase m cl) ∧ RK.b * RL.b ≤ bnd ∧
    ∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) → ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
      X τ tt r k = f0 τ r * (RK.W (RK.clk τ tt) r k * RL.W (RL.clk τ tt) r (k + ε • r))

theorem PieceRepU.mono {D : SumintPar.SumintDatum P.d} {hI : 0 < D.S.I} {vp vb : D.S.VIdx} {ε : ℝ}
    {f0 : (D.S.TVar → ℝ) → Mom P.d → ℂ} {X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ} {bnd bnd' : ℝ≥0∞}
    {Bx : Set (Fin 3 → ℝ)} (h : PieceRepU hI vp vb ε f0 X bnd Bx) (hb : bnd ≤ bnd') : PieceRepU hI vp vb ε f0 X bnd' Bx := by
  obtain ⟨RK, RL, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨RK, RL, h1, h2, h3, h4, h5.trans hb, h6⟩

/-- **The zero summand** has the zero representation. -/
theorem pieceRepU_zero {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (vp vb : D.S.VIdx) (ε : ℝ)
    (f0 : (D.S.TVar → ℝ) → Mom P.d → ℂ) (X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ) (bnd : ℝ≥0∞)
    (Bx : Set (Fin 3 → ℝ)) (hX : ∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) → ∀ r k : Mom P.d, ‖r‖ ≤ 1 → X τ tt r k = 0) :
    PieceRepU hI vp vb ε f0 X bnd Bx := by
  have hθ : (0 : ℝ) ≤ 6 * P.η ^ 6 := by positivity
  have hfs : ∀ ρ : Row D, coefBound (6 * P.η ^ 6) D.wN (rowOrder D ρ) (fun (_ : Fin 3 → ℤ) (_ _ : Mom P.d) => (0 : ℂ)) ≤ 0 := by
    intro ρ
    unfold coefBound
    refine le_of_eq ?_
    refine ENNReal.tsum_eq_zero.mpr fun m => ?_
    have : (⨆ r : Mom P.d, SNorm D.wN (rowOrder D ρ) (fun _ : Mom P.d => (0 : ℂ))) = 0 := by
      simp only [WaveTurbulence.VineEstS5A.SNorm_zero_fun, iSup_const]
    simp [this]
  let RK : RowData D (6 * P.η ^ 6) (Sum.inl vp) := RowData.ofModes (Sum.inl vp) (fun _ => Sum.inr 0)
    (fun _ _ _ => 0) 0 ENNReal.zero_ne_top (hfs _) (fun v hv => by exact absurd hv (by simp))
  let RL : RowData D (6 * P.η ^ 6) (Sum.inr vb) := RowData.ofModes (Sum.inr vb) (fun _ => Sum.inr 0)
    (fun _ _ _ => 0) 0 ENNReal.zero_ne_top (hfs _) (fun v hv m r r' k => rfl)
  refine ⟨RK, RL, RowData.ofModes_ae hθ hI _ _ _ _ _ _ _, RowData.ofModes_ae hθ hI _ _ _ _ _ _ _, fun _ _ _ => rfl, fun _ _ _ => rfl,
    by simp [RK, RL, RowData.ofModes], fun tt htt => ?_⟩
  filter_upwards [hX tt htt] with τ hτ hd r k hr
  rw [hτ hd r k hr]
  have : RK.W (RK.clk τ tt) r k = 0 := by
    show ∑' m : Fin 3 → ℤ, (0 : ℂ) * fsPhase m (RK.clk τ tt) = 0
    simp
  rw [this]; simp

open Classical in
/-- **A kind-0/1/3 summand** (`kindOf c ≠ 2`) as a `PieceRepU` of `ν · bundlePtG ..`. -/
theorem pieceRepU_of_dispK01 {K0 : ℝ≥0∞} (hd : DispK01.{u} P K0)
    {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
    (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey)
    (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D) (caseA : Prop)
    {β : Type u} [DecidableEq β] (S : SepTerms β P.d) (RQ RT : β → ℝ → ℝ → Mom P.d → ℂ) {q2 q4 qh : ℝ}
    (src : Src P S RQ RT q2 q4 qh) (bs1 bs2 rA rB : Finset β) (hgood : ∀ b, (b ∈ bs1 ∨ b ∈ bs2 ∨ b ∈ rA ∨ b ∈ rB) → src.good b)
    (c : Ch S bs1 bs2 rA rB) (hk : kindOf c ≠ 2) (Bx : Set (Fin 3 → ℝ)) (hBx : Bx ⊆ outBox D)
    (hh : ∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        ExcOrd caseA (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) c ∧
          slotVal D τ tt s1 ∈ Wsel q4 qh (decide caseA) ∧ slotVal D τ tt t1 ∈ Wsel q4 qh (!decide caseA) ∧
          slotVal D τ tt t0 ∈ Set.Ioo q2 (q2 + 1))
    (ν : ℂ) (hν : ‖ν‖ = 1) :
    PieceRepU hI vp vb ε (fun _ r => if kindOf c = 1 then ((‖r‖ : ℝ) : ℂ) else 1)
      (fun τ tt r k => ν * bundlePtG caseA S bs1 bs2 rA rB RQ RT (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1)
        (k + ex • r) (k + ey • r) c)
      (Kall P.d K0 * ENNReal.ofReal (src.sz c)) Bx := by
  unfold DispK01 at hd
  obtain ⟨fac, bK, bL, ⟨s, hs, hfs⟩, hrep, hb⟩ := hd D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 caseA S RQ RT src bs1 bs2 rA rB hgood c hk Bx hh
  obtain ⟨RK, RL, h1, h2, h3, h4, h5, h6, h7⟩ := hrep.sum_unit hBx ν s hν hs (fun _ r => if kindOf c = 1 then ((‖r‖ : ℝ) : ℂ) else 1) hfs
  exact ⟨RK, RL, h1, h2, h3, h4, (mul_le_mul' h5 h6).trans hb, h7⟩


open Classical in
/-- **A kind-2 summand** (`kindOf c = 2`, `TQ`/`TT` and their mirrors; equal windows `qh = q4` or the cross-window gap `q4 + 1 ≤ qh` with the cross fields `xs`)
as a `PieceRepU` of `ν · bundlePtG ..` with the rigid factor `|τ sa - τ ta|^{1-3η}`; the size is `Kall d (K0 · Kx0)`. -/
theorem pieceRepU_of_dispK2 {Rb : ℝ} {K0 : ℝ≥0∞} (hd : DispK2.{u} P Rb K0)
    {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
    (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey)
    (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D) (sa ta : D.S.TVar) (hsa : s1 = Sum.inl sa) (hsb : t1 = Sum.inl ta)
    (hab : sa ≠ ta) (caseA : Prop)
    {β : Type u} [DecidableEq β] (S : SepTerms β P.d) (RQ RT : β → ℝ → ℝ → Mom P.d → ℂ) {q2 q4 qh : ℝ}
    (src : Src P S RQ RT q2 q4 qh) (xs : q4 + 1 ≤ qh → K2.XCross P src) (Kx0 : ℝ) (hKx1 : 1 ≤ Kx0)
    (hKx : ∀ h, (xs h).Kx ≤ Kx0) (hqh : qh = q4 ∨ q4 + 1 ≤ qh) (hq4 : 0 ≤ q4) (hq2 : 0 ≤ q2)
    (hRb : max (qh + 1) (q2 + 1) ≤ Rb)
    (bs1 bs2 rA rB : Finset β) (hgood : ∀ b, (b ∈ bs1 ∨ b ∈ bs2) → src.good b)
    (c : Ch S bs1 bs2 rA rB) (hk : kindOf c = 2) (Bx : Set (Fin 3 → ℝ)) (hBx : Bx ⊆ outBox D)
    (hh : ∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        ExcOrd caseA (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) c ∧
          slotVal D τ tt s1 ∈ Wsel q4 qh (decide caseA) ∧ slotVal D τ tt t1 ∈ Wsel q4 qh (!decide caseA) ∧
          slotVal D τ tt t0 ∈ Set.Ioo q2 (q2 + 1))
    (ν : ℂ) (hν : ‖ν‖ = 1) :
    PieceRepU hI vp vb ε (fun τ _ => ((|τ sa - τ ta| ^ (1 - 3 * P.η) : ℝ) : ℂ))
      (fun τ tt r k => ν * bundlePtG caseA S bs1 bs2 rA rB RQ RT (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1)
        (k + ex • r) (k + ey • r) c)
      (Kall P.d (K0 * ENNReal.ofReal Kx0) * ENNReal.ofReal (src.sz c)) Bx := by
  unfold DispK2 at hd
  obtain ⟨bK, bL, hrep, hb⟩ := hd D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 sa ta hsa hsb hab caseA S RQ RT src xs Kx0 hKx1 hKx hqh hq4 hq2 hRb
    bs1 bs2 rA rB hgood c hk Bx hh
  obtain ⟨RK, RL, h1, h2, h3, h4, h5, h6, h7⟩ := hrep.sum_unit hBx ν 1 hν (by simp)
    (fun τ _ => ((|τ sa - τ ta| ^ (1 - 3 * P.η) : ℝ) : ℂ)) (fun τ r => (one_mul _).symm)
  exact ⟨RK, RL, h1, h2, h3, h4, (mul_le_mul' h5 h6).trans hb, h7⟩

end WaveTurbulence.VineEstS5C.P4.W2
