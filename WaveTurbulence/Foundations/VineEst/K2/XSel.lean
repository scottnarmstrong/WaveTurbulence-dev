/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.Export
public import WaveTurbulence.Foundations.VineEst.K2.OfContW

/-! # W2 session 20 (6B): the cross bound for the selected clamp

`xsel_C`, `xsel_T`: for the certified time factor `clampSel fl q Jc` (the two-sided clamp when the gate level is the root layer, the one-sided
clamp otherwise) the `𝔛^{1-2η}` bound on the union of the two windows `box_{w'} ∪ box_w` (`w + 1 ≤ w'`), with one constant `Kx(η)`, whenever
`fl` holds, or the one-sided clamp agrees with the two-sided one on both windows (`q ≤ w`), or the windows are far apart (`w + 2 ≤ w'`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.Fourier WaveTurbulence.VineEstS5C
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 MeasureTheory Set
open scoped ENNReal

theorem exists_const_lt (C : ℝ≥0∞) (hC : C ≠ ⊤) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {CJ : ℝ}, 0 < CJ → C * ENNReal.ofReal CJ < ENNReal.ofReal (K * CJ) := by
  obtain ⟨k, hk⟩ : ∃ k : ℝ, C = ENNReal.ofReal k ∧ 0 ≤ k :=
    ⟨C.toReal, (ENNReal.ofReal_toReal hC).symm, ENNReal.toReal_nonneg⟩
  refine ⟨2 * max 1 k, ?_, fun {CJ} hCJ => ?_⟩
  · have := le_max_left 1 k; linarith
  · rw [hk.1, ← ENNReal.ofReal_mul hk.2]
    rw [ENNReal.ofReal_lt_ofReal_iff (by have := le_max_left 1 k; positivity)]
    have h2 := le_max_right 1 k
    have h3 := le_max_left 1 k
    nlinarith [mul_pos hCJ (by linarith : (0 : ℝ) < max 1 k)]

section Far
variable {η : ℝ} (hθ : 0 ≤ 1 - η) (hη : η ≤ 1) (hη0 : 0 ≤ η)
include hθ hη hη0

theorem farJ_C {q w w' L2 : ℕ} (hL2q : L2 ≤ q) (hw : w + 2 ≤ w')
    {Jc : (Fin 2 → ℝ) → ℂ} (hJc : Continuous Jc) {X : ℝ} (hX : 0 ≤ X)
    (hJ : XNorm00Restr (V := Unit) (1 - η) (timeBox (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) ≤ ENNReal.ofReal X) :
    XNorm00Restr (V := Unit) (1 - 2 * η) (timeBox (w' : ℝ) L2 ∪ timeBox (w : ℝ) L2) Set.univ (fun ts _ => clampJ q Jc ts) ≤
      (cutoffMultiplierConstant (1 - η) (cutQ (0 : Fin 2 → ℝ)) + 1) *
        (ENNReal.ofReal (TR η * X) + ENNReal.ofReal (TR η * X)) := by
  have h1 := clamp_bound_C hθ hη hL2q (by omega : w' = q ∨ q + 1 ≤ w' ∨ w' + 1 ≤ q) hJc hX hJ
  have h2 := clamp_bound_C hθ hη hL2q (by omega : w = q ∨ q + 1 ≤ w ∨ w + 1 ≤ q) hJc hX hJ
  have hu := XNorm00Restr_union_sep (1 - η) (q := ![(w' : ℝ), L2]) (q' := ![(w : ℝ), L2]) 0
    (Or.inr (by simp; exact_mod_cast hw)) (timeBox_subset_cell _ _) (timeBox_subset_cell _ _) (Set.univ : Set Unit)
    (fun ts _ => clampJ q Jc ts)
  refine le_trans (XNorm00Restr_mono_theta (by linarith) _ _ _) (hu.trans ?_)
  exact mul_le_mul' le_rfl (add_le_add h1 h2)

theorem farJ_T {q w w' L2 : ℕ} (hL2q : L2 ≤ q) (hw : w + 2 ≤ w')
    {Jc : (Fin 2 → ℝ) → ℂ} (hJc : Continuous Jc) {X : ℝ} (hX : 0 ≤ X)
    (hJ : XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) ≤ ENNReal.ofReal X) :
    XNorm00Restr (V := Unit) (1 - 2 * η) (timeBoxGt (w' : ℝ) L2 ∪ timeBoxGt (w : ℝ) L2) Set.univ (fun ts _ => clampJ q Jc ts) ≤
      (cutoffMultiplierConstant (1 - η) (cutQ (0 : Fin 2 → ℝ)) + 1) *
        (ENNReal.ofReal (TR η * X) + ENNReal.ofReal (TR η * X)) := by
  have h1 := clamp_bound_T hθ hη hL2q (by omega : w' = q ∨ q + 1 ≤ w' ∨ w' + 1 ≤ q) hJc hX hJ
  have h2 := clamp_bound_T hθ hη hL2q (by omega : w = q ∨ q + 1 ≤ w ∨ w + 1 ≤ q) hJc hX hJ
  have hu := XNorm00Restr_union_sep (1 - η) (q := ![(w' : ℝ), L2]) (q' := ![(w : ℝ), L2]) 0
    (Or.inr (by simp; exact_mod_cast hw)) (timeBoxGt_subset_cell _ _) (timeBoxGt_subset_cell _ _) (Set.univ : Set Unit)
    (fun ts _ => clampJ q Jc ts)
  refine le_trans (XNorm00Restr_mono_theta (by linarith) _ _ _) (hu.trans ?_)
  exact mul_le_mul' le_rfl (add_le_add h1 h2)

end Far

theorem farConst_ne_top (η : ℝ) :
    (cutoffMultiplierConstant (1 - η) (cutQ (0 : Fin 2 → ℝ)) + 1) * (ENNReal.ofReal (TR η) + ENNReal.ofReal (TR η)) ≠ ⊤ := by
  have hcc : cutoffMultiplierConstant (1 - η) (cutQ (0 : Fin 2 → ℝ)) ≠ ⊤ :=
    (cutoffMultiplierConstant_lt_top (1 - η) (cutQ_hasCompactSupport _) (cutQ_contDiff _)).ne
  exact ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hcc, ENNReal.one_ne_top⟩)
    (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)

theorem far_mul_le (η : ℝ) (hη : η ≤ 1) {CJ : ℝ} (hCJ : 0 ≤ CJ) :
    (cutoffMultiplierConstant (1 - η) (cutQ (0 : Fin 2 → ℝ)) + 1) * (ENNReal.ofReal (TR η * CJ) + ENNReal.ofReal (TR η * CJ)) =
      ((cutoffMultiplierConstant (1 - η) (cutQ (0 : Fin 2 → ℝ)) + 1) * (ENNReal.ofReal (TR η) + ENNReal.ofReal (TR η))) *
        ENNReal.ofReal CJ := by
  have hT : 0 ≤ TR η := by linarith [one_le_TR hη]
  rw [ENNReal.ofReal_mul hT]
  ring

theorem xsel_C {η : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4) :
    ∃ Kx : ℝ, 1 ≤ Kx ∧ ∀ {q w w' L2 : ℕ} (fl : Prop) [Decidable fl], L2 ≤ q → L2 ≤ w → w + 1 ≤ w' →
      (fl ∨ q ≤ w ∨ w + 2 ≤ w') → ∀ {Jc : (Fin 2 → ℝ) → ℂ}, Continuous Jc →
      ∀ {CJ : ℝ}, XNorm00Restr (V := Unit) (1 - η) (timeBox (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) < ENNReal.ofReal CJ →
      XNorm00Restr (V := Unit) (1 - 2 * η) (timeBox (w' : ℝ) L2 ∪ timeBox (w : ℝ) L2) Set.univ
        (fun ts _ => clampSel fl (q : ℝ) Jc ts) < ENNReal.ofReal (Kx * CJ) := by
  obtain ⟨K1, hK1, hA⟩ := crossBound_C_final hη0 hη4
  obtain ⟨K2, hK2, hF⟩ := exists_const_lt _ (farConst_ne_top η)
  refine ⟨max K1 K2, le_trans hK1 (le_max_left _ _), fun {q w w' L2} fl _ hL2q hL2w hw hok {Jc} hJc {CJ} hJ => ?_⟩
  have hCJ : 0 < CJ := by
    by_contra h
    have : ENNReal.ofReal CJ = 0 := ENNReal.ofReal_of_nonpos (not_lt.1 h)
    rw [this] at hJ
    exact absurd hJ (not_lt.2 zero_le)
  by_cases hf : fl
  · rw [show (fun ts (_ : Unit) => clampSel fl (q : ℝ) Jc ts) = fun ts _ => clamp2J q Jc ts from by
      funext ts _; rw [clampSel_of_pos hf]]
    exact lt_of_lt_of_le (hA hL2q hL2w hw hJc hJ) (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hCJ.le))
  · have hok' : q ≤ w ∨ w + 2 ≤ w' := by tauto
    rcases hok' with hqw | hfar
    · have h1 := hA hL2q hL2w hw hJc hJ
      refine lt_of_lt_of_le (lt_of_le_of_lt (le_of_eq ?_) h1) (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hCJ.le))
      refine XNorm00Restr_congr_on _ _ fun ts hts v _ => ?_
      have ht : (q : ℝ) ≤ ts 0 := by
        rcases hts with h | h
        · exact le_trans (by exact_mod_cast (hqw.trans (Nat.le_succ w |>.trans hw))) h.1.1
        · exact le_trans (by exact_mod_cast hqw) h.1.1
      rw [clampSel_of_neg hf]
      exact clamp2J_eq_clampJ ht
    · have h1 := farJ_C (η := η) (by linarith) (by linarith) hη0.le hL2q hfar hJc hCJ.le hJ.le
      rw [show (fun ts (_ : Unit) => clampSel fl (q : ℝ) Jc ts) = fun ts _ => clampJ q Jc ts from by
        funext ts _; rw [clampSel_of_neg hf]]
      refine lt_of_le_of_lt h1 ?_
      rw [far_mul_le η (by linarith) hCJ.le]
      exact lt_of_lt_of_le (hF hCJ) (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) hCJ.le))

theorem xsel_T {η : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4) :
    ∃ Kx : ℝ, 1 ≤ Kx ∧ ∀ {q w w' L2 : ℕ} (fl : Prop) [Decidable fl], L2 ≤ q → L2 ≤ w → w + 1 ≤ w' →
      (fl ∨ q ≤ w ∨ w + 2 ≤ w') → ∀ {Jc : (Fin 2 → ℝ) → ℂ}, Continuous Jc →
      ∀ {CJ : ℝ}, XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) < ENNReal.ofReal CJ →
      XNorm00Restr (V := Unit) (1 - 2 * η) (timeBoxGt (w' : ℝ) L2 ∪ timeBoxGt (w : ℝ) L2) Set.univ
        (fun ts _ => clampSel fl (q : ℝ) Jc ts) < ENNReal.ofReal (Kx * CJ) := by
  obtain ⟨K1, hK1, hA⟩ := crossBound_T_final hη0 hη4
  obtain ⟨K2, hK2, hF⟩ := exists_const_lt _ (farConst_ne_top η)
  refine ⟨max K1 K2, le_trans hK1 (le_max_left _ _), fun {q w w' L2} fl _ hL2q hL2w hw hok {Jc} hJc {CJ} hJ => ?_⟩
  have hCJ : 0 < CJ := by
    by_contra h
    have : ENNReal.ofReal CJ = 0 := ENNReal.ofReal_of_nonpos (not_lt.1 h)
    rw [this] at hJ
    exact absurd hJ (not_lt.2 zero_le)
  by_cases hf : fl
  · rw [show (fun ts (_ : Unit) => clampSel fl (q : ℝ) Jc ts) = fun ts _ => clamp2J q Jc ts from by
      funext ts _; rw [clampSel_of_pos hf]]
    exact lt_of_lt_of_le (hA hL2q hL2w hw hJc hJ) (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hCJ.le))
  · have hok' : q ≤ w ∨ w + 2 ≤ w' := by tauto
    rcases hok' with hqw | hfar
    · have h1 := hA hL2q hL2w hw hJc hJ
      refine lt_of_lt_of_le (lt_of_le_of_lt (le_of_eq ?_) h1) (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hCJ.le))
      refine XNorm00Restr_congr_on _ _ fun ts hts v _ => ?_
      have ht : (q : ℝ) ≤ ts 0 := by
        rcases hts with h | h
        · exact le_trans (by exact_mod_cast (hqw.trans (Nat.le_succ w |>.trans hw))) h.1.1.1
        · exact le_trans (by exact_mod_cast hqw) h.1.1.1
      rw [clampSel_of_neg hf]
      exact clamp2J_eq_clampJ ht
    · have h1 := farJ_T (η := η) (by linarith) (by linarith) hη0.le hL2q hfar hJc hCJ.le hJ.le
      rw [show (fun ts (_ : Unit) => clampSel fl (q : ℝ) Jc ts) = fun ts _ => clampJ q Jc ts from by
        funext ts _; rw [clampSel_of_neg hf]]
      refine lt_of_le_of_lt h1 ?_
      rw [far_mul_le η (by linarith) hCJ.le]
      exact lt_of_lt_of_le (hF hCJ) (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) hCJ.le))


/-- The cross-bound property for couples at the glue constant `Kx`. -/
def XSelC (η Kx : ℝ) : Prop :=
  ∀ {q w w' L2 : ℕ} (fl : Prop) [Decidable fl], L2 ≤ q → L2 ≤ w → w + 1 ≤ w' →
    (fl ∨ q ≤ w ∨ w + 2 ≤ w') → ∀ {Jc : (Fin 2 → ℝ) → ℂ}, Continuous Jc →
    ∀ {CJ : ℝ}, XNorm00Restr (V := Unit) (1 - η) (timeBox (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) < ENNReal.ofReal CJ →
    XNorm00Restr (V := Unit) (1 - 2 * η) (timeBox (w' : ℝ) L2 ∪ timeBox (w : ℝ) L2) Set.univ
      (fun ts _ => clampSel fl (q : ℝ) Jc ts) < ENNReal.ofReal (Kx * CJ)

/-- The cross-bound property for trees at the glue constant `Kx`. -/
def XSelT (η Kx : ℝ) : Prop :=
  ∀ {q w w' L2 : ℕ} (fl : Prop) [Decidable fl], L2 ≤ q → L2 ≤ w → w + 1 ≤ w' →
    (fl ∨ q ≤ w ∨ w + 2 ≤ w') → ∀ {Jc : (Fin 2 → ℝ) → ℂ}, Continuous Jc →
    ∀ {CJ : ℝ}, XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) < ENNReal.ofReal CJ →
    XNorm00Restr (V := Unit) (1 - 2 * η) (timeBoxGt (w' : ℝ) L2 ∪ timeBoxGt (w : ℝ) L2) Set.univ
      (fun ts _ => clampSel fl (q : ℝ) Jc ts) < ENNReal.ofReal (Kx * CJ)

theorem XSelC.mono {η K K' : ℝ} (h : XSelC η K) (hK : K ≤ K') : XSelC η K' := by
  intro q w w' L2 fl _ h1 h2 h3 h4 Jc hJc CJ hJ
  have := h fl h1 h2 h3 h4 hJc hJ
  refine lt_of_lt_of_le this (ENNReal.ofReal_le_ofReal ?_)
  have hCJ : 0 < CJ := by
    by_contra hh
    have : ENNReal.ofReal CJ = 0 := ENNReal.ofReal_of_nonpos (not_lt.1 hh)
    rw [this] at hJ
    exact absurd hJ (not_lt.2 zero_le)
  exact mul_le_mul_of_nonneg_right hK hCJ.le

theorem XSelT.mono {η K K' : ℝ} (h : XSelT η K) (hK : K ≤ K') : XSelT η K' := by
  intro q w w' L2 fl _ h1 h2 h3 h4 Jc hJc CJ hJ
  have := h fl h1 h2 h3 h4 hJc hJ
  refine lt_of_lt_of_le this (ENNReal.ofReal_le_ofReal ?_)
  have hCJ : 0 < CJ := by
    by_contra hh
    have : ENNReal.ofReal CJ = 0 := ENNReal.ofReal_of_nonpos (not_lt.1 hh)
    rw [this] at hJ
    exact absurd hJ (not_lt.2 zero_le)
  exact mul_le_mul_of_nonneg_right hK hCJ.le

theorem exists_xsel {η : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4) : ∃ Kx : ℝ, 1 ≤ Kx ∧ XSelC η Kx ∧ XSelT η Kx := by
  obtain ⟨K1, h1, hC⟩ := xsel_C hη0 hη4
  obtain ⟨K2, h2, hT⟩ := xsel_T hη0 hη4
  exact ⟨max K1 K2, le_trans h1 (le_max_left _ _), XSelC.mono hC (le_max_left _ _), XSelT.mono hT (le_max_right _ _)⟩

/-- The uniform glue constant (depends on `η` only). -/
noncomputable def KxX (η : ℝ) : ℝ :=
  open Classical in if h : 0 < η ∧ η < 1 / 4 then Classical.choose (exists_xsel h.1 h.2) else 1

theorem KxX_spec {η : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4) : 1 ≤ KxX η ∧ XSelC η (KxX η) ∧ XSelT η (KxX η) := by
  unfold KxX
  rw [dif_pos ⟨hη0, hη4⟩]
  exact Classical.choose_spec (exists_xsel hη0 hη4)

/-- **Continuity of the selected clamp on the union of the two windows.** -/
theorem xsel_contOn {fl : Prop} [Decidable fl] {q w w' : ℕ} {Jc : (Fin 2 → ℝ) → ℂ} (hJc : Continuous Jc)
    (hok : fl ∨ q ≤ w ∨ (w + 2 ≤ q ∧ q ≤ w')) {B : Set (Fin 2 → ℝ)}
    (hB : ∀ ts ∈ B, (w : ℝ) ≤ ts 0 ∧ (ts 0 ≤ w + 1 ∨ (w' : ℝ) ≤ ts 0)) (hww : w ≤ w') :
    ContinuousOn (clampSel fl (q : ℝ) Jc) B := by
  by_cases hf : fl
  · rw [clampSel_of_pos hf]; exact (clamp2J_continuous hJc).continuousOn
  · have hok' : q ≤ w ∨ (w + 2 ≤ q ∧ q ≤ w') := by tauto
    rcases hok' with hqw | ⟨hq1, hq2⟩
    · refine (clampSel_continuousOn_ge (fl := fl) hJc).mono fun ts hts => ?_
      exact le_trans (by exact_mod_cast hqw) (hB ts hts).1
    · have hS1 : ContinuousOn (clampSel fl (q : ℝ) Jc) {ts : Fin 2 → ℝ | (q : ℝ) ≤ ts 0} :=
        clampSel_continuousOn_ge (fl := fl) hJc
      have hS2 : ContinuousOn (clampSel fl (q : ℝ) Jc) {ts : Fin 2 → ℝ | ts 0 ≤ (q : ℝ) - 1} := by
        refine (continuousOn_const (c := (0 : ℂ))).congr fun ts hts => ?_
        rw [clampSel_of_neg hf]
        unfold clampJ
        rw [if_pos (by simp only [Set.mem_setOf_eq] at hts; linarith)]
      have hc1 : IsClosed {ts : Fin 2 → ℝ | (q : ℝ) ≤ ts 0} := isClosed_le continuous_const (continuous_apply 0)
      have hc2 : IsClosed {ts : Fin 2 → ℝ | ts 0 ≤ (q : ℝ) - 1} := isClosed_le (continuous_apply 0) continuous_const
      refine (hS1.union_of_isClosed hS2 hc1 hc2).mono fun ts hts => ?_
      rcases (hB ts hts).2 with h | h
      · right
        have : (w : ℝ) + 2 ≤ q := by exact_mod_cast hq1
        simp only [Set.mem_setOf_eq]; linarith
      · left
        have : (q : ℝ) ≤ w' := by exact_mod_cast hq2
        simp only [Set.mem_setOf_eq]; linarith

end WaveTurbulence.VineEstS5C.P4.W2.K2
