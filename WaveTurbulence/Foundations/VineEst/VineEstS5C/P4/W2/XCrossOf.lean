/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcBnd
public import WaveTurbulence.Foundations.VineEst.K2.XCross
public import WaveTurbulence.Foundations.VineEst.K2.XSel

/-! # P4-W2 (session 20, 6B): the cross fields of a `Src` from the selected-clamp data

`xcrossOfData`: for a `Src` whose certified time factors (low and high window) are, for every good index, one selected clamp
`clampSel fl q Jc` of a continuous gate factor (`Jc` with the `𝔛^{1-η}` bound on the native box `q`, `L₂ ≤ q ≤ Lₕ`, and
`fl ∨ q ≤ L₄ ∨ L₄ + 2 ≤ q`), and for `L₄ + 1 ≤ Lₕ`, the `K2.XCross` with `Kx = KxX η` (depends on `η` only). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS4c
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W13
  MeasureTheory K2
open scoped ENNReal

variable {P : WTParams} {β : Type*} {S : SepTerms β P.d} {RQ RT : β → ℝ → ℝ → Mom P.d → ℂ} {q2 q4 qh : ℝ}

theorem boxC_win (q4 qh q2 : ℝ) : K2.XWin (timeBox qh q2 ∪ timeBox q4 q2) (timeBox qh q2 ∪ timeBox q4 q2) q4 qh q2 false := by
  intro t ht s hs _
  have hmem : ![t, s] ∈ timeBox qh q2 ∪ timeBox q4 q2 := by
    rcases ht with ht | ht
    · right
      simp only [timeBox, Set.mem_setOf_eq, Set.mem_Icc, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨⟨ht.1.le, ht.2.le⟩, ⟨hs.1.le, hs.2.le⟩⟩
    · left
      simp only [timeBox, Set.mem_setOf_eq, Set.mem_Icc, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨⟨ht.1.le, ht.2.le⟩, ⟨hs.1.le, hs.2.le⟩⟩
  exact ⟨hmem, hmem⟩

theorem boxT_win (q4 qh q2 : ℝ) : K2.XWin (timeBoxGt qh q2 ∪ timeBoxGt q4 q2) (timeBoxGt qh q2 ∪ timeBoxGt q4 q2) q4 qh q2 true := by
  intro t ht s hs hst
  have hst' := hst rfl
  have hmem : ![t, s] ∈ timeBoxGt qh q2 ∪ timeBoxGt q4 q2 := by
    rcases ht with ht | ht
    · right
      simp only [timeBoxGt, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨⟨⟨ht.1.le, ht.2.le⟩, ⟨hs.1.le, hs.2.le⟩⟩, hst'⟩
    · left
      simp only [timeBoxGt, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨⟨⟨ht.1.le, ht.2.le⟩, ⟨hs.1.le, hs.2.le⟩⟩, hst'⟩
  exact ⟨hmem, hmem⟩

theorem boxC_range {L4 Lh L2 : ℕ} (hgap : L4 + 1 ≤ Lh) :
    ∀ ts ∈ timeBox (Lh : ℝ) (L2 : ℝ) ∪ timeBox (L4 : ℝ) (L2 : ℝ), (L4 : ℝ) ≤ ts 0 ∧ (ts 0 ≤ L4 + 1 ∨ (Lh : ℝ) ≤ ts 0) := by
  intro ts hts
  have hg : (L4 : ℝ) + 1 ≤ Lh := by exact_mod_cast hgap
  rcases hts with h | h
  · exact ⟨le_trans (by linarith) h.1.1, Or.inr h.1.1⟩
  · exact ⟨h.1.1, Or.inl h.1.2⟩

theorem boxT_range {L4 Lh L2 : ℕ} (hgap : L4 + 1 ≤ Lh) :
    ∀ ts ∈ timeBoxGt (Lh : ℝ) (L2 : ℝ) ∪ timeBoxGt (L4 : ℝ) (L2 : ℝ), (L4 : ℝ) ≤ ts 0 ∧ (ts 0 ≤ L4 + 1 ∨ (Lh : ℝ) ≤ ts 0) := by
  intro ts hts
  have hg : (L4 : ℝ) + 1 ≤ Lh := by exact_mod_cast hgap
  rcases hts with h | h
  · exact ⟨le_trans (by linarith) h.1.1.1, Or.inr h.1.1.1⟩
  · exact ⟨h.1.1.1, Or.inl h.1.1.2⟩

open Classical in
/-- **The cross fields of a `Src`** from the selected-clamp data (see the module docstring). -/
noncomputable def xcrossOfData (src : Src P S RQ RT q2 q4 qh) (hη0 : 0 < P.η) (hη4 : P.η < 1 / 4) {L2 L4 Lh : ℕ}
    (h2 : q2 = L2) (h4 : q4 = L4) (hh : qh = Lh) (hL24 : L2 ≤ L4) (hgap : L4 + 1 ≤ Lh)
    (hCJq : ∀ b, src.good b → 0 ≤ src.CJq b) (hCJt : ∀ b, src.good b → 0 ≤ src.CJt b)
    (hQ : ∀ b, src.good b → ∀ i : Fin (S.mQ b), ∃ (q : ℕ) (fl : Prop) (_ : Decidable fl) (Jc : (Fin 2 → ℝ) → ℂ),
      L2 ≤ q ∧ q ≤ Lh ∧ Continuous Jc ∧
      XNorm00Restr (V := Unit) (1 - P.η) (timeBox (q : ℝ) (L2 : ℝ)) Set.univ (fun ts _ => Jc ts) < ENNReal.ofReal (src.CJq b) ∧
      (src.cq false b i).J = K2.clampSel fl (q : ℝ) Jc ∧ (src.cq true b i).J = (src.cq false b i).J ∧
      (src.cq true b i).M = (src.cq false b i).M ∧ (fl ∨ q ≤ L4 ∨ L4 + 2 ≤ q))
    (hT : ∀ b, src.good b → ∀ j : Fin (S.mT b), ∃ (q : ℕ) (fl : Prop) (_ : Decidable fl) (Jc : (Fin 2 → ℝ) → ℂ),
      L2 ≤ q ∧ q ≤ Lh ∧ Continuous Jc ∧
      XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt (q : ℝ) (L2 : ℝ)) Set.univ (fun ts _ => Jc ts) < ENNReal.ofReal (src.CJt b) ∧
      (src.ct false b j).J = K2.clampSel fl (q : ℝ) Jc ∧ (src.ct true b j).J = (src.ct false b j).J ∧
      (src.ct true b j).M = (src.ct false b j).M ∧ (fl ∨ q ≤ L4 ∨ L4 + 2 ≤ q)) :
    K2.XCross P src where
  Bq := timeBox qh q2 ∪ timeBox q4 q2
  Bcq := timeBox qh q2 ∪ timeBox q4 q2
  Bt := timeBoxGt qh q2 ∪ timeBoxGt q4 q2
  Bct := timeBoxGt qh q2 ∪ timeBoxGt q4 q2
  xJq b i := (src.cq false b i).J
  xJt b j := (src.ct false b j).J
  CJxq b := K2.KxX P.η * src.CJq b
  CJxt b := K2.KxX P.η * src.CJt b
  Kx := K2.KxX P.η
  hKx := (K2.KxX_spec hη0 hη4).1
  CJxq_nonneg b hb := mul_nonneg (le_trans zero_le_one (K2.KxX_spec hη0 hη4).1) (hCJq b hb)
  CJxt_nonneg b hb := mul_nonneg (le_trans zero_le_one (K2.KxX_spec hη0 hη4).1) (hCJt b hb)
  CJxq_le _ _ := le_rfl
  CJxt_le _ _ := le_rfl
  xq_win _ _ := boxC_win q4 qh q2
  xt_win _ _ := boxT_win q4 qh q2
  xq_cont b hb i := by
    subst h2 h4 hh
    obtain ⟨q, fl, _, Jc, hq2, hqh, hJc, -, he, -, -, hok⟩ := hQ b hb i
    rw [he]
    exact K2.xsel_contOn hJc (by rcases hok with h | h | h; exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr ⟨h, hqh⟩)])
      (boxC_range hgap) (by omega)
  xt_cont b hb j := by
    subst h2 h4 hh
    obtain ⟨q, fl, _, Jc, hq2, hqh, hJc, -, he, -, -, hok⟩ := hT b hb j
    rw [he]
    exact K2.xsel_contOn hJc (by rcases hok with h | h | h; exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr ⟨h, hqh⟩)])
      (boxT_range hgap) (by omega)
  xq_norm b hb i := by
    subst h2 h4 hh
    obtain ⟨q, fl, _, Jc, hq2, hqh, hJc, hn, he, -, -, hok⟩ := hQ b hb i
    show XNorm00Restr (V := Unit) (1 - 2 * P.η) _ Set.univ (fun ts _ => (src.cq false b i).J ts) < _
    rw [he]
    exact (K2.KxX_spec hη0 hη4).2.1 fl hq2 hL24 hgap (by rcases hok with h | h | h; exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (by omega))]) hJc hn
  xt_norm b hb j := by
    subst h2 h4 hh
    obtain ⟨q, fl, _, Jc, hq2, hqh, hJc, hn, he, -, -, hok⟩ := hT b hb j
    show XNorm00Restr (V := Unit) (1 - 2 * P.η) _ Set.univ (fun ts _ => (src.ct false b j).J ts) < _
    rw [he]
    exact (K2.KxX_spec hη0 hη4).2.2 fl hq2 hL24 hgap (by rcases hok with h | h | h; exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (by omega))]) hJc hn
  xq_M b hb i := (hQ b hb i).choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.1
  xt_M b hb j := (hT b hb j).choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.1
  xq_lo _ _ _ _ _ := rfl
  xq_hi b hb i ts _ := by rw [(hQ b hb i).choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.2.1]
  xt_lo _ _ _ _ _ := rfl
  xt_hi b hb j ts _ := by rw [(hT b hb j).choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.2.1]

end WaveTurbulence.VineEstS5C.P4.W2
