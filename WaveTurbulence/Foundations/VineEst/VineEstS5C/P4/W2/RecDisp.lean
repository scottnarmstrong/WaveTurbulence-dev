/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcDisp5

/-! # P4-W2 (session 14, step 1b): the dispatch statements as named propositions

`DispK01 P K0` / `DispK2 P Rb K0`: the bodies of `exc_dispatch_k01` / `exc_dispatch_k2` after the constant `K0`, as named `Prop`s, so that the record lemma can take the
constant and its dispatch statement as hypotheses (`exc_dispatch_k01'`, `exc_dispatch_k2'` repackage the two theorems).  These statements read `P` only
through `P.d` and `P.η` (and the structures `Src P`, `CertTerm P`, `RemC P`, `PieceRep`, which read only `P.d`, `P.η`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS4c
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 MeasureTheory
open scoped ENNReal ComplexConjugate
variable {A : ℝ}

open Classical in
def DispK01 (P : WTParams) (K0 : ℝ≥0∞) : Prop :=
  ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey)
      (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D) (caseA : Prop)
      {β : Type*} [DecidableEq β] (S : SepTerms β P.d) (RQ RT : β → ℝ → ℝ → Mom P.d → ℂ) {q2 q4 qh : ℝ}
      (src : Src P S RQ RT q2 q4 qh) (bs1 bs2 rA rB : Finset β) (hgood : ∀ b, (b ∈ bs1 ∨ b ∈ bs2 ∨ b ∈ rA ∨ b ∈ rB) → src.good b)
      (c : Ch S bs1 bs2 rA rB) (hk : kindOf c ≠ 2) (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        ExcOrd caseA (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) c ∧
          slotVal D τ tt s1 ∈ Wsel q4 qh (decide caseA) ∧ slotVal D τ tt t1 ∈ Wsel q4 qh (!decide caseA) ∧
          slotVal D τ tt t0 ∈ Set.Ioo q2 (q2 + 1)) →
      ∃ (fac : (D.S.TVar → ℝ) → Mom P.d → ℂ) (bK bL : ℝ≥0∞), FacOK (kindOf c) fac ∧
        PieceRep (P := P) hI vp vb ε fac
          (fun τ tt r k => bundlePtG caseA S bs1 bs2 rA rB RQ RT (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1)
            (k + ex • r) (k + ey • r) c) bK bL Bx ∧
        bK * bL ≤ Kall P.d K0 * ENNReal.ofReal (src.sz c)

open Classical in
theorem exc_dispatch_k01' {P : WTParams} (G : AmbP A P) :
    ∃ K0 : ℝ≥0∞, K0 ≠ ⊤ ∧ 1 ≤ K0 ∧ DispK01 P K0 :=
  exc_dispatch_k01 G

open Classical in
def DispK2 (P : WTParams) (Rb : ℝ) (K0 : ℝ≥0∞) : Prop :=
  ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey)
      (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D) (sa ta : D.S.TVar) (hsa : s1 = Sum.inl sa) (hsb : t1 = Sum.inl ta)
      (hab : sa ≠ ta) (caseA : Prop)
      {β : Type*} [DecidableEq β] (S : SepTerms β P.d) (RQ RT : β → ℝ → ℝ → Mom P.d → ℂ) {q2 q4 qh : ℝ}
      (src : Src P S RQ RT q2 q4 qh) (xs : q4 + 1 ≤ qh → K2.XCross P src) (Kx0 : ℝ) (hKx1 : 1 ≤ Kx0)
      (hKx : ∀ h, (xs h).Kx ≤ Kx0) (hqh : qh = q4 ∨ q4 + 1 ≤ qh) (hq4 : 0 ≤ q4) (hq2 : 0 ≤ q2)
      (hRb : max (qh + 1) (q2 + 1) ≤ Rb)
      (bs1 bs2 rA rB : Finset β) (hgood : ∀ b, (b ∈ bs1 ∨ b ∈ bs2) → src.good b)
      (c : Ch S bs1 bs2 rA rB) (hk : kindOf c = 2) (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        ExcOrd caseA (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) c ∧
          slotVal D τ tt s1 ∈ Wsel q4 qh (decide caseA) ∧ slotVal D τ tt t1 ∈ Wsel q4 qh (!decide caseA) ∧
          slotVal D τ tt t0 ∈ Set.Ioo q2 (q2 + 1)) →
      ∃ (bK bL : ℝ≥0∞),
        PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ sa - τ ta| ^ (1 - 3 * P.η) : ℝ) : ℂ))
          (fun τ tt r k => bundlePtG caseA S bs1 bs2 rA rB RQ RT (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1)
            (k + ex • r) (k + ey • r) c) bK bL Bx ∧
        bK * bL ≤ Kall P.d (K0 * ENNReal.ofReal Kx0) * ENNReal.ofReal (src.sz c)

open Classical in
theorem exc_dispatch_k2' {P : WTParams} (G : AmbP A P) (Rb : ℝ) :
    ∃ K0 : ℝ≥0∞, K0 ≠ ⊤ ∧ 1 ≤ K0 ∧ DispK2 P Rb K0 :=
  exc_dispatch_k2x G Rb

open Classical in
theorem DispK01.mono {P : WTParams} {K0 K0' : ℝ≥0∞} (h : DispK01.{0} P K0) (hK : K0 ≤ K0') : DispK01.{0} P K0' := by
  unfold DispK01 at h ⊢
  intro D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 caseA β _ S RQ RT q2 q4 qh src bs1 bs2 rA rB hgood c hk Bx hh
  obtain ⟨fac, bK, bL, h1, h2, h3⟩ := h D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 caseA S RQ RT src bs1 bs2 rA rB hgood c hk Bx hh
  exact ⟨fac, bK, bL, h1, h2, h3.trans (mul_le_mul' (Kall_mono P.d hK) le_rfl)⟩

open Classical in
theorem DispK2.mono {P : WTParams} {Rb : ℝ} {K0 K0' : ℝ≥0∞} (h : DispK2.{0} P Rb K0) (hK : K0 ≤ K0') : DispK2.{0} P Rb K0' := by
  unfold DispK2 at h ⊢
  intro D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 sa ta hsa hsb hab caseA β _ S RQ RT q2 q4 qh src xs Kx0 hKx1 hKx hqh hq4 hq2 hRb bs1 bs2 rA rB hgood c hk Bx hh
  obtain ⟨bK, bL, h1, h2⟩ := h D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 sa ta hsa hsb hab caseA S RQ RT src xs Kx0 hKx1 hKx hqh hq4 hq2 hRb bs1 bs2 rA rB hgood c hk Bx hh
  exact ⟨bK, bL, h1, h2.trans (mul_le_mul' (Kall_mono P.d (mul_le_mul' hK le_rfl)) le_rfl)⟩

end WaveTurbulence.VineEstS5C.P4.W2
