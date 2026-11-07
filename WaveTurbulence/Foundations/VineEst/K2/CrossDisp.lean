/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.CrossAll
public import WaveTurbulence.Foundations.VineEst.K2.XCross

/-! # W2-KIND2 (interface): the cross-window dispatch `disp_TQx`, `disp_TTx`, `disp_MTQx`, `disp_MTTx` for `q4 + 1 ≤ qh`

The statements are those of `disp_TQ`, ... (ExcDisp2) with `hq : qh = q4` replaced by `hgap : q4 + 1 ≤ qh` and the cross fields `xs : XCross ...` of `Src`;
the windows of the clocks are `s₁` high, `t₁` low in case A (TQ, TT) and `s₁` low, `t₁` high in case M (MTQ, MTT), as in `ExcWinGeo`.  The conclusion carries the
glue constant `Kx` absorbed into the uniform constant: `bK * bL ≤ Kall P.d (K0 * ofReal Kx) * ofReal (szQ * szT)`.
The proofs use `pieceAll_*x` (hence `pieceRep_joint2`, Lemma B) with the cross box `crossBoxO`; the bounds on both windows come from `xs`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS4c
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2
  MeasureTheory
open scoped ENNReal ComplexConjugate
variable {A : ℝ} {P : WTParams}

open Classical in
theorem disp_TQx (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧
      ∀ (K0 : ℝ≥0∞), C ≤ K0 → C' ≤ K0 → 1 ≤ K0 →
      ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey)
      (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b' : D.S.TVar) (hsa : s1 = Sum.inl a) (hsb : t1 = Sum.inl b') (hab : a ≠ b')
      (caseA : Prop) (hA : caseA)
      {β : Type*} [DecidableEq β] (S : SepTerms β P.d) (RQ RT : β → ℝ → ℝ → Mom P.d → ℂ) {q2 q4 qh : ℝ}
      (src : Src P S RQ RT q2 q4 qh) (xs : XCross P src) (hgap : q4 + 1 ≤ qh) (hq4 : 0 ≤ q4) (hq2 : 0 ≤ q2)
      (hRb : max (qh + 1) (q2 + 1) ≤ Rb)
      (bs1 bs2 rA rB : Finset β) (b : β) (hbm : b ∈ bs1) (hb : src.good b)
      (i : Fin (S.mQ b)) (j : Fin (S.mT b)) (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t0 < slotVal D τ tt t1 ∧ slotVal D τ tt t0 < slotVal D τ tt s1) ∧ slotVal D τ tt s1 ∈ Set.Ioo qh (qh + 1) ∧ slotVal D τ tt t1 ∈ Set.Ioo q4 (q4 + 1) ∧
          slotVal D τ tt t0 ∈ Set.Ioo q2 (q2 + 1)) →
      ∃ (bK bL : ℝ≥0∞),
        PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b'| ^ (1 - 3 * P.η) : ℝ) : ℂ))
          (fun τ tt r k => bundlePtG caseA S bs1 bs2 rA rB RQ RT (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1)
            (k + ex • r) (k + ey • r) (Sum.inl (Sum.inr (Sum.inr (Sum.inl ⟨⟨b, hbm⟩, i, j⟩))))) bK bL Bx ∧
        bK * bL ≤ Kall P.d (K0 * ENNReal.ofReal xs.Kx) * ENNReal.ofReal (src.szQ b * src.szT b) := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceAll_TQx G Rb
  refine ⟨C, C', hC, hC', fun K0 hCK hCK' hK0 D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 a b' hsa hsb hab caseA hA β _ S RQ RT q2 q4 qh src xs hgap hq4 hq2 hRb bs1 bs2 rA rB b hbm hb i j Bx hG => ?_⟩
  have hd := G.hd1
  have hJq : 0 ≤ src.CJq b := (src.cq false b i).hCJ
  have hMq : 0 ≤ src.CMq b := (src.cq false b i).hCM
  have hJt : 0 ≤ src.CJt b := (src.ct false b j).hCJ
  have hMt : 0 ≤ src.CMt b := (src.ct false b j).hCM
  have hJx : 0 ≤ xs.CJxq b := xs.CJxq_nonneg b hb
  have hWl : Wsel q4 qh false = Set.Ioo q4 (q4 + 1) := by simp [Wsel]
  have hWh : Wsel q4 qh true = Set.Ioo qh (qh + 1) := by simp [Wsel]
  have hwql := src.winq_sel hb i false
  have hwqh := src.winq_sel hb i true
  have hwtl := src.wint_sel hb j false
  have hwth := src.wint_sel hb j true
  rw [hWl] at hwql hwtl
  rw [hWh] at hwqh hwth
  have hRb' : q4 + 1 ≤ Rb := by linarith [le_max_left (qh + 1) (q2 + 1)]
  have hRh : qh + 1 ≤ Rb := le_trans (le_max_left _ _) hRb
  have hR2 : q2 + 1 ≤ Rb := le_trans (le_max_right _ _) hRb
  have hqh0 : 0 ≤ qh := by linarith
  let Bc3 : Set (Fin 3 → ℝ) := crossBoxO qh q4 q2
  have h1 : Bc3 ⊆ cell ![qh, q4, q2] := fun τ hτ => crossBoxG_sub_cell _ _ _ hτ.1
  have h3 : ∀ τ ∈ Bc3, ‖τ‖ ≤ Rb := fun τ hτ => crossBoxG_norm (qa := qh) (qb := q4) hqh0 hq4 hq2 hRh hRb' hR2 τ hτ.1
  have h7 : ∀ τ ∈ Bc3, τ 0 ≠ τ 1 := fun τ hτ => crossBoxG_ne (Or.inr hgap) τ hτ.1
  have hcl : Bc3 ⊆ closure (interior Bc3) := crossBoxO_cl _ _ _
  have h4 : ∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ xs.Bq ∧ ![τ 1, τ 2] ∈ xs.Bq := fun τ hτ =>
    ⟨(xs.xq_win b hb _ (Or.inr hτ.1.1) _ hτ.1.2.2 (fun h => absurd h (by decide))).1, (xs.xq_win b hb _ (Or.inl hτ.1.2.1) _ hτ.1.2.2 (fun h => absurd h (by decide))).1⟩
  have h8 : ∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ xs.Bcq ∧ ![τ 1, τ 2] ∈ xs.Bcq := fun τ hτ =>
    ⟨(xs.xq_win b hb _ (Or.inr hτ.1.1) _ hτ.1.2.2 (fun h => absurd h (by decide))).2, (xs.xq_win b hb _ (Or.inl hτ.1.2.1) _ hτ.1.2.2 (fun h => absurd h (by decide))).2⟩
  have hG' : ∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
      (slotVal D τ tt t0 < slotVal D τ tt t1 ∧ slotVal D τ tt t0 < slotVal D τ tt s1) ∧ ![slotVal D τ tt s1, slotVal D τ tt t1, slotVal D τ tt t0] ∈ Bc3 ∧
        ((![slotVal D τ tt s1, slotVal D τ tt t0] ∈ (src.cq true b i).V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ (src.cq true b i).Bc) ∧
          (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ (src.cq false b i).V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ (src.cq false b i).Bc)) ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ (src.ct false b j).V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ (src.ct false b j).Bc) := by
    intro tt htt
    filter_upwards [hG tt htt] with τ hg hd
    obtain ⟨hord, hs, ht, h0⟩ := hg hd
    exact ⟨hord, ⟨⟨hs, ht, h0⟩, hord.2, hord.1⟩, ⟨hwqh _ hs _ h0 (fun h => absurd h (by decide)), hwql _ ht _ h0 (fun h => absurd h (by decide))⟩, hwtl _ ht _ h0 (fun _ => hord.1)⟩
  have hPR := h D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 a b' hsa hsb S b i j (src.cq false b i) (src.cq true b i) (src.ct false b j)
    (by rw [src.cq_c, src.cq_c]) (xs.xq_M b hb i) (xs.xJq b i) xs.Bq xs.Bcq (xs.CJxq b) (xs.xq_cont b hb i) (xs.xq_norm b hb i) (xs.xq_lo b hb i) (xs.xq_hi b hb i) ![qh, q4, q2] Bc3 Bc3 h1 hcl h3 h4 subset_rfl hcl h7 h8 Bx hG'
  refine ⟨_, _, hPR.congr (fun tt htt => Filter.Eventually.of_forall fun τ hd r k hr => by
    simp only [bundlePtG, ptP, ptR, Sum.elim_inl, Sum.elim_inr, if_pos hA]
    try ring_nf), ?_⟩
  refine (bnd_P hd hwN hwDec _ _ K0 hCK hCK' _ _ _ _ _ hJx hJt hMq hMt).trans ?_
  have hbr : 0 ≤ |src.cc b| * |src.cT b| * src.CMq b * src.CMt b :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hMq) hMt
  have hxle := xs.CJxq_le b hb
  have hmain := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxle hJt) hbr
  refine bnd_x hd K0 xs.Kx _ _ xs.hKx ?_ (mul_nonneg (src.szQ_nonneg hJq hMq) (src.szT_nonneg hJt hMt))
  simp only [CertSrc.szQ, CertSrc.szT, src.cq_c, src.ct_c, abs_mul, abs_neg, abs_one, mul_one]
  exact le_trans (le_of_eq (by ring)) (le_trans hmain (le_of_eq (by ring)))

open Classical in
theorem disp_TTx (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧
      ∀ (K0 : ℝ≥0∞), C ≤ K0 → C' ≤ K0 → 1 ≤ K0 →
      ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey)
      (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b' : D.S.TVar) (hsa : t1 = Sum.inl a) (hsb : s1 = Sum.inl b') (hab : a ≠ b')
      (caseA : Prop) (hA : caseA)
      {β : Type*} [DecidableEq β] (S : SepTerms β P.d) (RQ RT : β → ℝ → ℝ → Mom P.d → ℂ) {q2 q4 qh : ℝ}
      (src : Src P S RQ RT q2 q4 qh) (xs : XCross P src) (hgap : q4 + 1 ≤ qh) (hq4 : 0 ≤ q4) (hq2 : 0 ≤ q2)
      (hRb : max (qh + 1) (q2 + 1) ≤ Rb)
      (bs1 bs2 rA rB : Finset β) (b : β) (hbm : b ∈ bs2) (hb : src.good b)
      (i : Fin (S.mQ b)) (j : Fin (S.mT b)) (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t0 < slotVal D τ tt t1 ∧ slotVal D τ tt t0 < slotVal D τ tt s1) ∧ slotVal D τ tt s1 ∈ Set.Ioo qh (qh + 1) ∧ slotVal D τ tt t1 ∈ Set.Ioo q4 (q4 + 1) ∧
          slotVal D τ tt t0 ∈ Set.Ioo q2 (q2 + 1)) →
      ∃ (bK bL : ℝ≥0∞),
        PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b'| ^ (1 - 3 * P.η) : ℝ) : ℂ))
          (fun τ tt r k => bundlePtG caseA S bs1 bs2 rA rB RQ RT (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1)
            (k + ex • r) (k + ey • r) (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨⟨b, hbm⟩, i, j⟩))))))) bK bL Bx ∧
        bK * bL ≤ Kall P.d (K0 * ENNReal.ofReal xs.Kx) * ENNReal.ofReal (src.szQ b * src.szT b) := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceAll_TTx G Rb
  refine ⟨C, C', hC, hC', fun K0 hCK hCK' hK0 D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 a b' hsa hsb hab caseA hA β _ S RQ RT q2 q4 qh src xs hgap hq4 hq2 hRb bs1 bs2 rA rB b hbm hb i j Bx hG => ?_⟩
  have hd := G.hd1
  have hJq : 0 ≤ src.CJq b := (src.cq false b i).hCJ
  have hMq : 0 ≤ src.CMq b := (src.cq false b i).hCM
  have hJt : 0 ≤ src.CJt b := (src.ct false b j).hCJ
  have hMt : 0 ≤ src.CMt b := (src.ct false b j).hCM
  have hJx : 0 ≤ xs.CJxt b := xs.CJxt_nonneg b hb
  have hWl : Wsel q4 qh false = Set.Ioo q4 (q4 + 1) := by simp [Wsel]
  have hWh : Wsel q4 qh true = Set.Ioo qh (qh + 1) := by simp [Wsel]
  have hwql := src.winq_sel hb i false
  have hwqh := src.winq_sel hb i true
  have hwtl := src.wint_sel hb j false
  have hwth := src.wint_sel hb j true
  rw [hWl] at hwql hwtl
  rw [hWh] at hwqh hwth
  have hRb' : q4 + 1 ≤ Rb := by linarith [le_max_left (qh + 1) (q2 + 1)]
  have hRh : qh + 1 ≤ Rb := le_trans (le_max_left _ _) hRb
  have hR2 : q2 + 1 ≤ Rb := le_trans (le_max_right _ _) hRb
  have hqh0 : 0 ≤ qh := by linarith
  let Bc3 : Set (Fin 3 → ℝ) := crossBoxO q4 qh q2
  have h1 : Bc3 ⊆ cell ![q4, qh, q2] := fun τ hτ => crossBoxG_sub_cell _ _ _ hτ.1
  have h3 : ∀ τ ∈ Bc3, ‖τ‖ ≤ Rb := fun τ hτ => crossBoxG_norm (qa := q4) (qb := qh) hq4 hqh0 hq2 hRb' hRh hR2 τ hτ.1
  have h7 : ∀ τ ∈ Bc3, τ 0 ≠ τ 1 := fun τ hτ => crossBoxG_ne (Or.inl hgap) τ hτ.1
  have hcl : Bc3 ⊆ closure (interior Bc3) := crossBoxO_cl _ _ _
  have h4 : ∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ xs.Bt ∧ ![τ 1, τ 2] ∈ xs.Bt := fun τ hτ =>
    ⟨(xs.xt_win b hb _ (Or.inl hτ.1.1) _ hτ.1.2.2 (fun _ => by linarith [hτ.2.1, hτ.2.2])).1, (xs.xt_win b hb _ (Or.inr hτ.1.2.1) _ hτ.1.2.2 (fun _ => by linarith [hτ.2.1, hτ.2.2])).1⟩
  have h8 : ∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ xs.Bct ∧ ![τ 1, τ 2] ∈ xs.Bct := fun τ hτ =>
    ⟨(xs.xt_win b hb _ (Or.inl hτ.1.1) _ hτ.1.2.2 (fun _ => by linarith [hτ.2.1, hτ.2.2])).2, (xs.xt_win b hb _ (Or.inr hτ.1.2.1) _ hτ.1.2.2 (fun _ => by linarith [hτ.2.1, hτ.2.2])).2⟩
  have hG' : ∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
      (slotVal D τ tt t0 < slotVal D τ tt t1 ∧ slotVal D τ tt t0 < slotVal D τ tt s1) ∧ ![slotVal D τ tt t1, slotVal D τ tt s1, slotVal D τ tt t0] ∈ Bc3 ∧
        ((![slotVal D τ tt t1, slotVal D τ tt t0] ∈ (src.ct false b j).V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ (src.ct false b j).Bc) ∧
          (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ (src.ct true b j).V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ (src.ct true b j).Bc)) ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ (src.cq false b i).V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ (src.cq false b i).Bc) := by
    intro tt htt
    filter_upwards [hG tt htt] with τ hg hd
    obtain ⟨hord, hs, ht, h0⟩ := hg hd
    exact ⟨hord, ⟨⟨ht, hs, h0⟩, hord.1, hord.2⟩, ⟨hwtl _ ht _ h0 (fun _ => hord.1), hwth _ hs _ h0 (fun _ => hord.2)⟩, hwql _ ht _ h0 (fun h => absurd h (by decide))⟩
  have hPR := h D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 a b' hsa hsb S b i j (src.cq false b i) (src.ct false b j) (src.ct true b j)
    (by rw [src.ct_c, src.ct_c]) (xs.xt_M b hb j) (xs.xJt b j) xs.Bt xs.Bct (xs.CJxt b) (xs.xt_cont b hb j) (xs.xt_norm b hb j) (xs.xt_lo b hb j) (xs.xt_hi b hb j) ![q4, qh, q2] Bc3 Bc3 h1 hcl h3 h4 subset_rfl hcl h7 h8 Bx hG'
  refine ⟨_, _, hPR.congr (fun tt htt => Filter.Eventually.of_forall fun τ hd r k hr => by
    simp only [bundlePtG, ptP, ptR, Sum.elim_inl, Sum.elim_inr, if_pos hA]
    try ring_nf), ?_⟩
  refine (bnd_P hd hwN hwDec _ _ K0 hCK hCK' _ _ _ _ _ hJx hJq hMq hMt).trans ?_
  have hbr : 0 ≤ |src.cc b| * |src.cT b| * src.CMq b * src.CMt b :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hMq) hMt
  have hxle := xs.CJxt_le b hb
  have hmain := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxle hJq) hbr
  refine bnd_x hd K0 xs.Kx _ _ xs.hKx ?_ (mul_nonneg (src.szQ_nonneg hJq hMq) (src.szT_nonneg hJt hMt))
  simp only [CertSrc.szQ, CertSrc.szT, src.cq_c, src.ct_c, abs_mul, abs_neg, abs_one, mul_one]
  exact le_trans (le_of_eq (by ring)) (le_trans hmain (le_of_eq (by ring)))

open Classical in
theorem disp_MTQx (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧
      ∀ (K0 : ℝ≥0∞), C ≤ K0 → C' ≤ K0 → 1 ≤ K0 →
      ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey)
      (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b' : D.S.TVar) (hsa : t1 = Sum.inl a) (hsb : s1 = Sum.inl b') (hab : a ≠ b')
      (caseA : Prop) (hA : ¬caseA)
      {β : Type*} [DecidableEq β] (S : SepTerms β P.d) (RQ RT : β → ℝ → ℝ → Mom P.d → ℂ) {q2 q4 qh : ℝ}
      (src : Src P S RQ RT q2 q4 qh) (xs : XCross P src) (hgap : q4 + 1 ≤ qh) (hq4 : 0 ≤ q4) (hq2 : 0 ≤ q2)
      (hRb : max (qh + 1) (q2 + 1) ≤ Rb)
      (bs1 bs2 rA rB : Finset β) (b : β) (hbm : b ∈ bs1) (hb : src.good b)
      (i : Fin (S.mQ b)) (j : Fin (S.mT b)) (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t0 < slotVal D τ tt s1 ∧ slotVal D τ tt t0 < slotVal D τ tt t1) ∧ slotVal D τ tt s1 ∈ Set.Ioo q4 (q4 + 1) ∧ slotVal D τ tt t1 ∈ Set.Ioo qh (qh + 1) ∧
          slotVal D τ tt t0 ∈ Set.Ioo q2 (q2 + 1)) →
      ∃ (bK bL : ℝ≥0∞),
        PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b'| ^ (1 - 3 * P.η) : ℝ) : ℂ))
          (fun τ tt r k => bundlePtG caseA S bs1 bs2 rA rB RQ RT (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1)
            (k + ex • r) (k + ey • r) (Sum.inl (Sum.inr (Sum.inr (Sum.inl ⟨⟨b, hbm⟩, i, j⟩))))) bK bL Bx ∧
        bK * bL ≤ Kall P.d (K0 * ENNReal.ofReal xs.Kx) * ENNReal.ofReal (src.szQ b * src.szT b) := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceAll_MTQx G Rb
  refine ⟨C, C', hC, hC', fun K0 hCK hCK' hK0 D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 a b' hsa hsb hab caseA hA β _ S RQ RT q2 q4 qh src xs hgap hq4 hq2 hRb bs1 bs2 rA rB b hbm hb i j Bx hG => ?_⟩
  have hd := G.hd1
  have hJq : 0 ≤ src.CJq b := (src.cq false b i).hCJ
  have hMq : 0 ≤ src.CMq b := (src.cq false b i).hCM
  have hJt : 0 ≤ src.CJt b := (src.ct false b j).hCJ
  have hMt : 0 ≤ src.CMt b := (src.ct false b j).hCM
  have hJx : 0 ≤ xs.CJxq b := xs.CJxq_nonneg b hb
  have hWl : Wsel q4 qh false = Set.Ioo q4 (q4 + 1) := by simp [Wsel]
  have hWh : Wsel q4 qh true = Set.Ioo qh (qh + 1) := by simp [Wsel]
  have hwql := src.winq_sel hb i false
  have hwqh := src.winq_sel hb i true
  have hwtl := src.wint_sel hb j false
  have hwth := src.wint_sel hb j true
  rw [hWl] at hwql hwtl
  rw [hWh] at hwqh hwth
  have hRb' : q4 + 1 ≤ Rb := by linarith [le_max_left (qh + 1) (q2 + 1)]
  have hRh : qh + 1 ≤ Rb := le_trans (le_max_left _ _) hRb
  have hR2 : q2 + 1 ≤ Rb := le_trans (le_max_right _ _) hRb
  have hqh0 : 0 ≤ qh := by linarith
  let Bc3 : Set (Fin 3 → ℝ) := crossBoxO qh q4 q2
  have h1 : Bc3 ⊆ cell ![qh, q4, q2] := fun τ hτ => crossBoxG_sub_cell _ _ _ hτ.1
  have h3 : ∀ τ ∈ Bc3, ‖τ‖ ≤ Rb := fun τ hτ => crossBoxG_norm (qa := qh) (qb := q4) hqh0 hq4 hq2 hRh hRb' hR2 τ hτ.1
  have h7 : ∀ τ ∈ Bc3, τ 0 ≠ τ 1 := fun τ hτ => crossBoxG_ne (Or.inr hgap) τ hτ.1
  have hcl : Bc3 ⊆ closure (interior Bc3) := crossBoxO_cl _ _ _
  have h4 : ∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ xs.Bq ∧ ![τ 1, τ 2] ∈ xs.Bq := fun τ hτ =>
    ⟨(xs.xq_win b hb _ (Or.inr hτ.1.1) _ hτ.1.2.2 (fun h => absurd h (by decide))).1, (xs.xq_win b hb _ (Or.inl hτ.1.2.1) _ hτ.1.2.2 (fun h => absurd h (by decide))).1⟩
  have h8 : ∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ xs.Bcq ∧ ![τ 1, τ 2] ∈ xs.Bcq := fun τ hτ =>
    ⟨(xs.xq_win b hb _ (Or.inr hτ.1.1) _ hτ.1.2.2 (fun h => absurd h (by decide))).2, (xs.xq_win b hb _ (Or.inl hτ.1.2.1) _ hτ.1.2.2 (fun h => absurd h (by decide))).2⟩
  have hG' : ∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
      (slotVal D τ tt t0 < slotVal D τ tt s1 ∧ slotVal D τ tt t0 < slotVal D τ tt t1) ∧ ![slotVal D τ tt t1, slotVal D τ tt s1, slotVal D τ tt t0] ∈ Bc3 ∧
        ((![slotVal D τ tt t1, slotVal D τ tt t0] ∈ (src.cq true b i).V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ (src.cq true b i).Bc) ∧
          (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ (src.cq false b i).V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ (src.cq false b i).Bc)) ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ (src.ct false b j).V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ (src.ct false b j).Bc) := by
    intro tt htt
    filter_upwards [hG tt htt] with τ hg hd
    obtain ⟨hord, hs, ht, h0⟩ := hg hd
    exact ⟨hord, ⟨⟨ht, hs, h0⟩, hord.2, hord.1⟩, ⟨hwqh _ ht _ h0 (fun h => absurd h (by decide)), hwql _ hs _ h0 (fun h => absurd h (by decide))⟩, hwtl _ hs _ h0 (fun _ => hord.1)⟩
  have hPR := h D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 a b' hsa hsb S b i j (src.cq false b i) (src.cq true b i) (src.ct false b j)
    (by rw [src.cq_c, src.cq_c]) (xs.xq_M b hb i) (xs.xJq b i) xs.Bq xs.Bcq (xs.CJxq b) (xs.xq_cont b hb i) (xs.xq_norm b hb i) (xs.xq_lo b hb i) (xs.xq_hi b hb i) ![qh, q4, q2] Bc3 Bc3 h1 hcl h3 h4 subset_rfl hcl h7 h8 Bx hG'
  refine ⟨_, _, hPR.congr (fun tt htt => Filter.Eventually.of_forall fun τ hd r k hr => by
    simp only [bundlePtG, ptP, ptR, Sum.elim_inl, Sum.elim_inr, if_neg hA]
    try ring_nf), ?_⟩
  refine (bnd_P hd hwN hwDec _ _ K0 hCK hCK' _ _ _ _ _ hJx hJt hMq hMt).trans ?_
  have hbr : 0 ≤ |src.cc b| * |src.cT b| * src.CMq b * src.CMt b :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hMq) hMt
  have hxle := xs.CJxq_le b hb
  have hmain := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxle hJt) hbr
  refine bnd_x hd K0 xs.Kx _ _ xs.hKx ?_ (mul_nonneg (src.szQ_nonneg hJq hMq) (src.szT_nonneg hJt hMt))
  simp only [CertSrc.szQ, CertSrc.szT, src.cq_c, src.ct_c, abs_mul, abs_neg, abs_one, mul_one]
  exact le_trans (le_of_eq (by ring)) (le_trans hmain (le_of_eq (by ring)))

open Classical in
theorem disp_MTTx (G : AmbP A P) (Rb : ℝ) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧
      ∀ (K0 : ℝ≥0∞), C ≤ K0 → C' ≤ K0 → 1 ≤ K0 →
      ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey)
      (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D) (a b' : D.S.TVar) (hsa : s1 = Sum.inl a) (hsb : t1 = Sum.inl b') (hab : a ≠ b')
      (caseA : Prop) (hA : ¬caseA)
      {β : Type*} [DecidableEq β] (S : SepTerms β P.d) (RQ RT : β → ℝ → ℝ → Mom P.d → ℂ) {q2 q4 qh : ℝ}
      (src : Src P S RQ RT q2 q4 qh) (xs : XCross P src) (hgap : q4 + 1 ≤ qh) (hq4 : 0 ≤ q4) (hq2 : 0 ≤ q2)
      (hRb : max (qh + 1) (q2 + 1) ≤ Rb)
      (bs1 bs2 rA rB : Finset β) (b : β) (hbm : b ∈ bs2) (hb : src.good b)
      (i : Fin (S.mQ b)) (j : Fin (S.mT b)) (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        (slotVal D τ tt t0 < slotVal D τ tt s1 ∧ slotVal D τ tt t0 < slotVal D τ tt t1) ∧ slotVal D τ tt s1 ∈ Set.Ioo q4 (q4 + 1) ∧ slotVal D τ tt t1 ∈ Set.Ioo qh (qh + 1) ∧
          slotVal D τ tt t0 ∈ Set.Ioo q2 (q2 + 1)) →
      ∃ (bK bL : ℝ≥0∞),
        PieceRep (P := P) hI vp vb ε (fun τ _ => ((|τ a - τ b'| ^ (1 - 3 * P.η) : ℝ) : ℂ))
          (fun τ tt r k => bundlePtG caseA S bs1 bs2 rA rB RQ RT (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1)
            (k + ex • r) (k + ey • r) (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨⟨b, hbm⟩, i, j⟩))))))) bK bL Bx ∧
        bK * bL ≤ Kall P.d (K0 * ENNReal.ofReal xs.Kx) * ENNReal.ofReal (src.szQ b * src.szT b) := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceAll_MTTx G Rb
  refine ⟨C, C', hC, hC', fun K0 hCK hCK' hK0 D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 a b' hsa hsb hab caseA hA β _ S RQ RT q2 q4 qh src xs hgap hq4 hq2 hRb bs1 bs2 rA rB b hbm hb i j Bx hG => ?_⟩
  have hd := G.hd1
  have hJq : 0 ≤ src.CJq b := (src.cq false b i).hCJ
  have hMq : 0 ≤ src.CMq b := (src.cq false b i).hCM
  have hJt : 0 ≤ src.CJt b := (src.ct false b j).hCJ
  have hMt : 0 ≤ src.CMt b := (src.ct false b j).hCM
  have hJx : 0 ≤ xs.CJxt b := xs.CJxt_nonneg b hb
  have hWl : Wsel q4 qh false = Set.Ioo q4 (q4 + 1) := by simp [Wsel]
  have hWh : Wsel q4 qh true = Set.Ioo qh (qh + 1) := by simp [Wsel]
  have hwql := src.winq_sel hb i false
  have hwqh := src.winq_sel hb i true
  have hwtl := src.wint_sel hb j false
  have hwth := src.wint_sel hb j true
  rw [hWl] at hwql hwtl
  rw [hWh] at hwqh hwth
  have hRb' : q4 + 1 ≤ Rb := by linarith [le_max_left (qh + 1) (q2 + 1)]
  have hRh : qh + 1 ≤ Rb := le_trans (le_max_left _ _) hRb
  have hR2 : q2 + 1 ≤ Rb := le_trans (le_max_right _ _) hRb
  have hqh0 : 0 ≤ qh := by linarith
  let Bc3 : Set (Fin 3 → ℝ) := crossBoxO q4 qh q2
  have h1 : Bc3 ⊆ cell ![q4, qh, q2] := fun τ hτ => crossBoxG_sub_cell _ _ _ hτ.1
  have h3 : ∀ τ ∈ Bc3, ‖τ‖ ≤ Rb := fun τ hτ => crossBoxG_norm (qa := q4) (qb := qh) hq4 hqh0 hq2 hRb' hRh hR2 τ hτ.1
  have h7 : ∀ τ ∈ Bc3, τ 0 ≠ τ 1 := fun τ hτ => crossBoxG_ne (Or.inl hgap) τ hτ.1
  have hcl : Bc3 ⊆ closure (interior Bc3) := crossBoxO_cl _ _ _
  have h4 : ∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ xs.Bt ∧ ![τ 1, τ 2] ∈ xs.Bt := fun τ hτ =>
    ⟨(xs.xt_win b hb _ (Or.inl hτ.1.1) _ hτ.1.2.2 (fun _ => by linarith [hτ.2.1, hτ.2.2])).1, (xs.xt_win b hb _ (Or.inr hτ.1.2.1) _ hτ.1.2.2 (fun _ => by linarith [hτ.2.1, hτ.2.2])).1⟩
  have h8 : ∀ τ ∈ Bc3, ![τ 0, τ 2] ∈ xs.Bct ∧ ![τ 1, τ 2] ∈ xs.Bct := fun τ hτ =>
    ⟨(xs.xt_win b hb _ (Or.inl hτ.1.1) _ hτ.1.2.2 (fun _ => by linarith [hτ.2.1, hτ.2.2])).2, (xs.xt_win b hb _ (Or.inr hτ.1.2.1) _ hτ.1.2.2 (fun _ => by linarith [hτ.2.1, hτ.2.2])).2⟩
  have hG' : ∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
      (slotVal D τ tt t0 < slotVal D τ tt s1 ∧ slotVal D τ tt t0 < slotVal D τ tt t1) ∧ ![slotVal D τ tt s1, slotVal D τ tt t1, slotVal D τ tt t0] ∈ Bc3 ∧
        ((![slotVal D τ tt s1, slotVal D τ tt t0] ∈ (src.ct false b j).V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ (src.ct false b j).Bc) ∧
          (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ (src.ct true b j).V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ (src.ct true b j).Bc)) ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ (src.cq false b i).V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ (src.cq false b i).Bc) := by
    intro tt htt
    filter_upwards [hG tt htt] with τ hg hd
    obtain ⟨hord, hs, ht, h0⟩ := hg hd
    exact ⟨hord, ⟨⟨hs, ht, h0⟩, hord.1, hord.2⟩, ⟨hwtl _ hs _ h0 (fun _ => hord.1), hwth _ ht _ h0 (fun _ => hord.2)⟩, hwql _ hs _ h0 (fun h => absurd h (by decide))⟩
  have hPR := h D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 a b' hsa hsb S b i j (src.cq false b i) (src.ct false b j) (src.ct true b j)
    (by rw [src.ct_c, src.ct_c]) (xs.xt_M b hb j) (xs.xJt b j) xs.Bt xs.Bct (xs.CJxt b) (xs.xt_cont b hb j) (xs.xt_norm b hb j) (xs.xt_lo b hb j) (xs.xt_hi b hb j) ![q4, qh, q2] Bc3 Bc3 h1 hcl h3 h4 subset_rfl hcl h7 h8 Bx hG'
  refine ⟨_, _, hPR.congr (fun tt htt => Filter.Eventually.of_forall fun τ hd r k hr => by
    simp only [bundlePtG, ptP, ptR, Sum.elim_inl, Sum.elim_inr, if_neg hA]
    try ring_nf), ?_⟩
  refine (bnd_P hd hwN hwDec _ _ K0 hCK hCK' _ _ _ _ _ hJx hJq hMq hMt).trans ?_
  have hbr : 0 ≤ |src.cc b| * |src.cT b| * src.CMq b * src.CMt b :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hMq) hMt
  have hxle := xs.CJxt_le b hb
  have hmain := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxle hJq) hbr
  refine bnd_x hd K0 xs.Kx _ _ xs.hKx ?_ (mul_nonneg (src.szQ_nonneg hJq hMq) (src.szT_nonneg hJt hMt))
  simp only [CertSrc.szQ, CertSrc.szT, src.cq_c, src.ct_c, abs_mul, abs_neg, abs_one, mul_one]
  exact le_trans (le_of_eq (by ring)) (le_trans hmain (le_of_eq (by ring)))

end WaveTurbulence.VineEstS5C.P4.W2.K2
