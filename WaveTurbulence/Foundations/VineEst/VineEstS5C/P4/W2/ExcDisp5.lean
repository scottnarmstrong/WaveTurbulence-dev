/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcDisp4
public import WaveTurbulence.Foundations.VineEst.K2.CrossDisp

/-! # P4-W2 (session 20, step 6C): the kind-2 dispatch without `hq` (equal windows or the cross-window gap)

`exc_dispatch_k2x`: `exc_dispatch_k2` for `qh = q4` (the old `disp_*`) or `q4 + 1 ≤ qh` (the cross dispatches `disp_*x` of `K2.CrossDisp`, with the cross
fields `xs : XCross P src`).  The windows are `Wsel q4 qh (decide caseA)` for `s₁` and `Wsel q4 qh (!decide caseA)` for `t₁` (as in `exc_dispatch_k01`); the size is
`Kall d (K0 · Kx0)` where `Kx0 ≥ 1` bounds the glue constants of the cross fields (`(xs h).Kx ≤ Kx0`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS4c
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 MeasureTheory
open scoped ENNReal ComplexConjugate
variable {A : ℝ} {P : WTParams}

theorem Kall_mono (d : ℕ) {K K' : ℝ≥0∞} (h : K ≤ K') : Kall d K ≤ Kall d K' := by
  unfold Kall
  exact mul_le_mul' (mul_le_mul' (mul_le_mul' h h) le_rfl) le_rfl

theorem Kall_le_of_ge_one (d : ℕ) (K : ℝ≥0∞) {x : ℝ} (hx : 1 ≤ x) : Kall d K ≤ Kall d (K * ENNReal.ofReal x) :=
  Kall_mono d (by
    calc K = K * 1 := (mul_one K).symm
      _ ≤ K * ENNReal.ofReal x := mul_le_mul' le_rfl (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hx))

theorem Wsel_self (q : ℝ) (s : Bool) : Wsel q q s = Set.Ioo q (q + 1) := by cases s <;> simp [Wsel]

open Classical in
theorem exc_dispatch_k2x (G : AmbP A P) (Rb : ℝ) :
    ∃ K0 : ℝ≥0∞, K0 ≠ ⊤ ∧ 1 ≤ K0 ∧
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
        bK * bL ≤ Kall P.d (K0 * ENNReal.ofReal Kx0) * ENNReal.ofReal (src.sz c) := by
  obtain ⟨C_TQ, C'_TQ, hC_TQ, hC'_TQ, h_TQ⟩ := disp_TQ G Rb
  obtain ⟨C_TQx, C'_TQx, hC_TQx, hC'_TQx, h_TQx⟩ := K2.disp_TQx G Rb
  obtain ⟨C_TT, C'_TT, hC_TT, hC'_TT, h_TT⟩ := disp_TT G Rb
  obtain ⟨C_TTx, C'_TTx, hC_TTx, hC'_TTx, h_TTx⟩ := K2.disp_TTx G Rb
  obtain ⟨C_MTQ, C'_MTQ, hC_MTQ, hC'_MTQ, h_MTQ⟩ := disp_MTQ G Rb
  obtain ⟨C_MTQx, C'_MTQx, hC_MTQx, hC'_MTQx, h_MTQx⟩ := K2.disp_MTQx G Rb
  obtain ⟨C_MTT, C'_MTT, hC_MTT, hC'_MTT, h_MTT⟩ := disp_MTT G Rb
  obtain ⟨C_MTTx, C'_MTTx, hC_MTTx, hC'_MTTx, h_MTTx⟩ := K2.disp_MTTx G Rb
  set tot : ℝ := 1 + (C_TQ.toReal + C'_TQ.toReal + C_TQx.toReal + C'_TQx.toReal + C_TT.toReal + C'_TT.toReal + C_TTx.toReal + C'_TTx.toReal + C_MTQ.toReal + C'_MTQ.toReal + C_MTQx.toReal + C'_MTQx.toReal + C_MTT.toReal + C'_MTT.toReal + C_MTTx.toReal + C'_MTTx.toReal) with htot
  have nn_C_TQ := ENNReal.toReal_nonneg (a := C_TQ)
  have nn_Cp_TQ := ENNReal.toReal_nonneg (a := C'_TQ)
  have nn_C_TQx := ENNReal.toReal_nonneg (a := C_TQx)
  have nn_Cp_TQx := ENNReal.toReal_nonneg (a := C'_TQx)
  have nn_C_TT := ENNReal.toReal_nonneg (a := C_TT)
  have nn_Cp_TT := ENNReal.toReal_nonneg (a := C'_TT)
  have nn_C_TTx := ENNReal.toReal_nonneg (a := C_TTx)
  have nn_Cp_TTx := ENNReal.toReal_nonneg (a := C'_TTx)
  have nn_C_MTQ := ENNReal.toReal_nonneg (a := C_MTQ)
  have nn_Cp_MTQ := ENNReal.toReal_nonneg (a := C'_MTQ)
  have nn_C_MTQx := ENNReal.toReal_nonneg (a := C_MTQx)
  have nn_Cp_MTQx := ENNReal.toReal_nonneg (a := C'_MTQx)
  have nn_C_MTT := ENNReal.toReal_nonneg (a := C_MTT)
  have nn_Cp_MTT := ENNReal.toReal_nonneg (a := C'_MTT)
  have nn_C_MTTx := ENNReal.toReal_nonneg (a := C_MTTx)
  have nn_Cp_MTTx := ENNReal.toReal_nonneg (a := C'_MTTx)
  have hle : ∀ (C : ℝ≥0∞), C ≠ ⊤ → C.toReal ≤ tot - 1 → C ≤ ENNReal.ofReal tot := fun C hC h => by
    rw [← ENNReal.ofReal_toReal hC]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hone : (1 : ℝ) ≤ tot := by simp only [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx]
  refine ⟨ENNReal.ofReal tot, ENNReal.ofReal_ne_top, by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hone, ?_⟩
  intro D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 sa ta hsa hsb hab caseA β _ S RQ RT q2 q4 qh src xs Kx0 hKx1 hKx hqh hq4 hq2 hRb bs1 bs2 rA rB hgood c hk Bx hG
  set K0 : ℝ≥0∞ := ENNReal.ofReal tot with hK0def
  have hK0 : 1 ≤ K0 := by rw [hK0def, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hone
  have hcomm : (fun (τ : D.S.TVar → ℝ) (_ : Mom P.d) => ((|τ ta - τ sa| ^ (1 - 3 * P.η) : ℝ) : ℂ)) =
      (fun (τ : D.S.TVar → ℝ) (_ : Mom P.d) => ((|τ sa - τ ta| ^ (1 - 3 * P.η) : ℝ) : ℂ)) := by
    funext τ _; rw [abs_sub_comm]
  have hmono : ∀ (x : ℝ≥0∞), x ≤ Kall P.d K0 * ENNReal.ofReal (src.sz c) → x ≤ Kall P.d (K0 * ENNReal.ofReal Kx0) * ENNReal.ofReal (src.sz c) :=
    fun x hx => hx.trans (mul_le_mul' (Kall_le_of_ge_one P.d K0 hKx1) le_rfl)
  have hK_C_TQ : C_TQ ≤ K0 := hle _ hC_TQ (by rw [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx])
  have hK_Cp_TQ : C'_TQ ≤ K0 := hle _ hC'_TQ (by rw [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx])
  have hK_C_TQx : C_TQx ≤ K0 := hle _ hC_TQx (by rw [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx])
  have hK_Cp_TQx : C'_TQx ≤ K0 := hle _ hC'_TQx (by rw [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx])
  have hK_C_TT : C_TT ≤ K0 := hle _ hC_TT (by rw [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx])
  have hK_Cp_TT : C'_TT ≤ K0 := hle _ hC'_TT (by rw [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx])
  have hK_C_TTx : C_TTx ≤ K0 := hle _ hC_TTx (by rw [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx])
  have hK_Cp_TTx : C'_TTx ≤ K0 := hle _ hC'_TTx (by rw [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx])
  have hK_C_MTQ : C_MTQ ≤ K0 := hle _ hC_MTQ (by rw [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx])
  have hK_Cp_MTQ : C'_MTQ ≤ K0 := hle _ hC'_MTQ (by rw [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx])
  have hK_C_MTQx : C_MTQx ≤ K0 := hle _ hC_MTQx (by rw [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx])
  have hK_Cp_MTQx : C'_MTQx ≤ K0 := hle _ hC'_MTQx (by rw [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx])
  have hK_C_MTT : C_MTT ≤ K0 := hle _ hC_MTT (by rw [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx])
  have hK_Cp_MTT : C'_MTT ≤ K0 := hle _ hC'_MTT (by rw [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx])
  have hK_C_MTTx : C_MTTx ≤ K0 := hle _ hC_MTTx (by rw [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx])
  have hK_Cp_MTTx : C'_MTTx ≤ K0 := hle _ hC'_MTTx (by rw [htot]; linarith [nn_C_TQ, nn_Cp_TQ, nn_C_TQx, nn_Cp_TQx, nn_C_TT, nn_Cp_TT, nn_C_TTx, nn_Cp_TTx, nn_C_MTQ, nn_Cp_MTQ, nn_C_MTQx, nn_Cp_MTQx, nn_C_MTT, nn_Cp_MTT, nn_C_MTTx, nn_Cp_MTTx])
  have hmonoX : ∀ h : q4 + 1 ≤ qh, ∀ x : ℝ≥0∞, x ≤ Kall P.d (K0 * ENNReal.ofReal (xs h).Kx) * ENNReal.ofReal (src.sz c) →
      x ≤ Kall P.d (K0 * ENNReal.ofReal Kx0) * ENNReal.ofReal (src.sz c) :=
    fun h x hx => hx.trans (mul_le_mul' (Kall_mono P.d (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hKx h)))) le_rfl)
  rcases hqh with hq | hgap
  · have hRb' : max (q4 + 1) (q2 + 1) ≤ Rb := by rw [hq] at hRb; exact hRb
    rcases c with ((⟨⟨b, hbm⟩, i, j⟩ | ⟨⟨b, hbm⟩, i, j⟩ | ⟨⟨b, hbm⟩, i, j⟩ | ⟨⟨b, hbm⟩, i, j⟩ | ⟨⟨b, hbm⟩, i, j⟩ | ⟨⟨b, hbm⟩, i, j⟩) | (⟨⟨b, hbm⟩, i | j | _⟩ | ⟨⟨b, hbm⟩, i | j | _⟩))
    · simp [kindOf] at hk
    · simp [kindOf] at hk
    · rcases Classical.em caseA with hA | hA
      · obtain ⟨bK, bL, hP, hbd⟩ := @h_TQ K0 hK_C_TQ hK_Cp_TQ hK0 D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 sa ta hsa hsb hab caseA hA β _ S RQ RT q2 q4 qh src hq hq4 hq2 hRb' bs1 bs2 rA rB b hbm (hgood b (by simp [hbm])) i j Bx (fun tt htt => by filter_upwards [hG tt htt] with τ hg hd; have hg' := hg hd; simpa [ExcOrd, hA, Wsel, hq] using hg')
        exact ⟨bK, bL, hP, hmono _ hbd⟩
      · obtain ⟨bK, bL, hP, hbd⟩ := @h_MTQ K0 hK_C_MTQ hK_Cp_MTQ hK0 D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 ta sa hsb hsa hab.symm caseA hA β _ S RQ RT q2 q4 qh src hq hq4 hq2 hRb' bs1 bs2 rA rB b hbm (hgood b (by simp [hbm])) i j Bx (fun tt htt => by filter_upwards [hG tt htt] with τ hg hd; have hg' := hg hd; simpa [ExcOrd, hA, Wsel, hq] using hg')
        exact ⟨bK, bL, by rw [hcomm] at hP; exact hP, hmono _ hbd⟩
    · simp [kindOf] at hk
    · simp [kindOf] at hk
    · rcases Classical.em caseA with hA | hA
      · obtain ⟨bK, bL, hP, hbd⟩ := @h_TT K0 hK_C_TT hK_Cp_TT hK0 D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 ta sa hsb hsa hab.symm caseA hA β _ S RQ RT q2 q4 qh src hq hq4 hq2 hRb' bs1 bs2 rA rB b hbm (hgood b (by simp [hbm])) i j Bx (fun tt htt => by filter_upwards [hG tt htt] with τ hg hd; have hg' := hg hd; simpa [ExcOrd, hA, Wsel, hq] using hg')
        exact ⟨bK, bL, by rw [hcomm] at hP; exact hP, hmono _ hbd⟩
      · obtain ⟨bK, bL, hP, hbd⟩ := @h_MTT K0 hK_C_MTT hK_Cp_MTT hK0 D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 sa ta hsa hsb hab caseA hA β _ S RQ RT q2 q4 qh src hq hq4 hq2 hRb' bs1 bs2 rA rB b hbm (hgood b (by simp [hbm])) i j Bx (fun tt htt => by filter_upwards [hG tt htt] with τ hg hd; have hg' := hg hd; simpa [ExcOrd, hA, Wsel, hq] using hg')
        exact ⟨bK, bL, hP, hmono _ hbd⟩
    all_goals simp [kindOf] at hk
  · rcases c with ((⟨⟨b, hbm⟩, i, j⟩ | ⟨⟨b, hbm⟩, i, j⟩ | ⟨⟨b, hbm⟩, i, j⟩ | ⟨⟨b, hbm⟩, i, j⟩ | ⟨⟨b, hbm⟩, i, j⟩ | ⟨⟨b, hbm⟩, i, j⟩) | (⟨⟨b, hbm⟩, i | j | _⟩ | ⟨⟨b, hbm⟩, i | j | _⟩))
    · simp [kindOf] at hk
    · simp [kindOf] at hk
    · rcases Classical.em caseA with hA | hA
      · obtain ⟨bK, bL, hP, hbd⟩ := @h_TQx K0 hK_C_TQx hK_Cp_TQx hK0 D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 sa ta hsa hsb hab caseA hA β _ S RQ RT q2 q4 qh src (xs hgap) hgap hq4 hq2 hRb bs1 bs2 rA rB b hbm (hgood b (by simp [hbm])) i j Bx (fun tt htt => by filter_upwards [hG tt htt] with τ hg hd; have hg' := hg hd; simpa [ExcOrd, hA, Wsel] using hg')
        exact ⟨bK, bL, hP, hmonoX hgap _ hbd⟩
      · obtain ⟨bK, bL, hP, hbd⟩ := @h_MTQx K0 hK_C_MTQx hK_Cp_MTQx hK0 D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 ta sa hsb hsa hab.symm caseA hA β _ S RQ RT q2 q4 qh src (xs hgap) hgap hq4 hq2 hRb bs1 bs2 rA rB b hbm (hgood b (by simp [hbm])) i j Bx (fun tt htt => by filter_upwards [hG tt htt] with τ hg hd; have hg' := hg hd; simpa [ExcOrd, hA, Wsel] using hg')
        exact ⟨bK, bL, by rw [hcomm] at hP; exact hP, hmonoX hgap _ hbd⟩
    · simp [kindOf] at hk
    · simp [kindOf] at hk
    · rcases Classical.em caseA with hA | hA
      · obtain ⟨bK, bL, hP, hbd⟩ := @h_TTx K0 hK_C_TTx hK_Cp_TTx hK0 D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 ta sa hsb hsa hab.symm caseA hA β _ S RQ RT q2 q4 qh src (xs hgap) hgap hq4 hq2 hRb bs1 bs2 rA rB b hbm (hgood b (by simp [hbm])) i j Bx (fun tt htt => by filter_upwards [hG tt htt] with τ hg hd; have hg' := hg hd; simpa [ExcOrd, hA, Wsel] using hg')
        exact ⟨bK, bL, by rw [hcomm] at hP; exact hP, hmonoX hgap _ hbd⟩
      · obtain ⟨bK, bL, hP, hbd⟩ := @h_MTTx K0 hK_C_MTTx hK_Cp_MTTx hK0 D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 sa ta hsa hsb hab caseA hA β _ S RQ RT q2 q4 qh src (xs hgap) hgap hq4 hq2 hRb bs1 bs2 rA rB b hbm (hgood b (by simp [hbm])) i j Bx (fun tt htt => by filter_upwards [hG tt htt] with τ hg hd; have hg' := hg hd; simpa [ExcOrd, hA, Wsel] using hg')
        exact ⟨bK, bL, hP, hmonoX hgap _ hbd⟩
    all_goals simp [kindOf] at hk

end WaveTurbulence.VineEstS5C.P4.W2
