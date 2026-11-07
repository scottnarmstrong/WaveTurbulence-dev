/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.Clamp2Bound
public import WaveTurbulence.Foundations.VineEst.K2.SepUnion

/-! # W2-KIND2 (producers): the cross-window `𝔛^{1-2η}` bound of the two-sided clamp, far and adjacent

`ClampGlueC η CA`, `ClampGlueT η CA`: **Lemma A** (TARGET L1917-L1918, "an elementary argument"), the clamp gluing `1-η → 1-2η` on two adjacent windows.
`crossBound_far_C/T`: far case (`w + 2 ≤ w'`), PROVED here (separated union, then monotonicity in `θ`).
`crossBound_C/T`: all `w + 1 ≤ w'`, from the far case and `ClampGlue` (adjacent case `w' = w + 1`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.Fourier WaveTurbulence.LGSpine WaveTurbulence.VineEstS5C
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 MeasureTheory Set
open scoped ENNReal

/-- **Lemma A for couples** (clamp gluing, `𝔛^{1-η} → 𝔛^{1-2η}` on two adjacent unit windows with constant `CA`). -/
def ClampGlueC (η : ℝ) (CA : ℝ≥0∞) : Prop :=
  ∀ (q w L2 : ℕ), L2 ≤ q → L2 ≤ w → ∀ (Jc : (Fin 2 → ℝ) → ℂ), Continuous Jc → ∀ X : ℝ, 0 ≤ X →
    XNorm00Restr (V := Unit) (1 - η) (timeBox (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) ≤ ENNReal.ofReal X →
    XNorm00Restr (V := Unit) (1 - 2 * η) (timeBox (w : ℝ) L2 ∪ timeBox ((w + 1 : ℕ) : ℝ) L2) Set.univ
      (fun ts _ => clamp2J q Jc ts) ≤ CA * ENNReal.ofReal X

/-- **Lemma A for trees.** -/
def ClampGlueT (η : ℝ) (CA : ℝ≥0∞) : Prop :=
  ∀ (q w L2 : ℕ), L2 ≤ q → L2 ≤ w → ∀ (Jc : (Fin 2 → ℝ) → ℂ), Continuous Jc → ∀ X : ℝ, 0 ≤ X →
    XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) ≤ ENNReal.ofReal X →
    XNorm00Restr (V := Unit) (1 - 2 * η) (timeBoxGt (w : ℝ) L2 ∪ timeBoxGt ((w + 1 : ℕ) : ℝ) L2) Set.univ
      (fun ts _ => clamp2J q Jc ts) ≤ CA * ENNReal.ofReal X

section Far
variable {η : ℝ} (hθ : 0 ≤ 1 - η) (hη : η ≤ 1) (hη0 : 0 ≤ η)
include hθ hη hη0

/-- **Far case, couples** (`w + 2 ≤ w'`): the separated union of the two window bounds, then `θ = 1 - η → 1 - 2η`. -/
theorem crossBound_far_C {q w w' L2 : ℕ} (hL2q : L2 ≤ q) (hw : w + 2 ≤ w')
    {Jc : (Fin 2 → ℝ) → ℂ} (hJc : Continuous Jc) {X : ℝ} (hX : 0 ≤ X)
    (hJ : XNorm00Restr (V := Unit) (1 - η) (timeBox (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) ≤ ENNReal.ofReal X) :
    XNorm00Restr (V := Unit) (1 - 2 * η) (timeBox (w' : ℝ) L2 ∪ timeBox (w : ℝ) L2) Set.univ (fun ts _ => clamp2J q Jc ts) ≤
      (cutoffMultiplierConstant (1 - η) (cutQ (0 : Fin 2 → ℝ)) + 1) *
        (ENNReal.ofReal (TR η * X) + ENNReal.ofReal (TR η * X)) := by
  have h1 := clamp2_bound_C hθ hη hL2q (by omega : w' = q ∨ q + 1 ≤ w' ∨ w' + 1 ≤ q) hJc hX hJ
  have h2 := clamp2_bound_C hθ hη hL2q (by omega : w = q ∨ q + 1 ≤ w ∨ w + 1 ≤ q) hJc hX hJ
  have hu := XNorm00Restr_union_sep (1 - η) (q := ![(w' : ℝ), L2]) (q' := ![(w : ℝ), L2]) 0
    (Or.inr (by simp; exact_mod_cast hw)) (timeBox_subset_cell _ _) (timeBox_subset_cell _ _) (Set.univ : Set Unit)
    (fun ts _ => clamp2J q Jc ts)
  refine le_trans (XNorm00Restr_mono_theta (by linarith) _ _ _) (hu.trans ?_)
  exact mul_le_mul' le_rfl (add_le_add h1 h2)

/-- **Far case, trees.** -/
theorem crossBound_far_T {q w w' L2 : ℕ} (hL2q : L2 ≤ q) (hL2w : L2 ≤ w) (hw : w + 2 ≤ w')
    {Jc : (Fin 2 → ℝ) → ℂ} (hJc : Continuous Jc) {X : ℝ} (hX : 0 ≤ X)
    (hJ : XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) ≤ ENNReal.ofReal X) :
    XNorm00Restr (V := Unit) (1 - 2 * η) (timeBoxGt (w' : ℝ) L2 ∪ timeBoxGt (w : ℝ) L2) Set.univ (fun ts _ => clamp2J q Jc ts) ≤
      (cutoffMultiplierConstant (1 - η) (cutQ (0 : Fin 2 → ℝ)) + 1) *
        (ENNReal.ofReal (TR η * X) + ENNReal.ofReal (TR η * X)) := by
  have h1 := clamp2_bound_T hθ hη hL2q (by omega) (by omega : w' = q ∨ q + 1 ≤ w' ∨ w' + 1 ≤ q) hJc hX hJ
  have h2 := clamp2_bound_T hθ hη hL2q hL2w (by omega : w = q ∨ q + 1 ≤ w ∨ w + 1 ≤ q) hJc hX hJ
  have hu := XNorm00Restr_union_sep (1 - η) (q := ![(w' : ℝ), L2]) (q' := ![(w : ℝ), L2]) 0
    (Or.inr (by simp; exact_mod_cast hw)) (timeBoxGt_subset_cell _ _) (timeBoxGt_subset_cell _ _) (Set.univ : Set Unit)
    (fun ts _ => clamp2J q Jc ts)
  refine le_trans (XNorm00Restr_mono_theta (by linarith) _ _ _) (hu.trans ?_)
  exact mul_le_mul' le_rfl (add_le_add h1 h2)

end Far

/-- The uniform glue constant (far + adjacent). -/
noncomputable def glueConst (η : ℝ) (CA : ℝ≥0∞) : ℝ≥0∞ :=
  CA + (cutoffMultiplierConstant (1 - η) (cutQ (0 : Fin 2 → ℝ)) + 1) * (ENNReal.ofReal (TR η) + ENNReal.ofReal (TR η))

theorem glueConst_ne_top (η : ℝ) {CA : ℝ≥0∞} (hCA : CA ≠ ⊤) : glueConst η CA ≠ ⊤ := by
  unfold glueConst
  refine ENNReal.add_ne_top.2 ⟨hCA, ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨?_, ENNReal.one_ne_top⟩)
    (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)⟩
  exact (cutoffMultiplierConstant_lt_top _ (cutQ_hasCompactSupport _) (cutQ_contDiff _)).ne

theorem far_le_glue {η : ℝ} (CA : ℝ≥0∞) {X : ℝ} (hX : 0 ≤ X) (hTR : 0 ≤ TR η) :
    (cutoffMultiplierConstant (1 - η) (cutQ (0 : Fin 2 → ℝ)) + 1) *
        (ENNReal.ofReal (TR η * X) + ENNReal.ofReal (TR η * X)) ≤ glueConst η CA * ENNReal.ofReal X := by
  unfold glueConst
  rw [ENNReal.ofReal_mul hTR]
  calc _ = (cutoffMultiplierConstant (1 - η) (cutQ (0 : Fin 2 → ℝ)) + 1) *
          (ENNReal.ofReal (TR η) + ENNReal.ofReal (TR η)) * ENNReal.ofReal X := by ring
    _ ≤ _ := mul_le_mul' le_add_self le_rfl

/-- **All `w + 1 ≤ w'`, couples** (far case proved, adjacent case from `ClampGlueC`). -/
theorem crossBound_C {η : ℝ} (hθ : 0 ≤ 1 - η) (hη : η ≤ 1) (hη0 : 0 ≤ η) {CA : ℝ≥0∞} (hG : ClampGlueC η CA)
    {q w w' L2 : ℕ} (hL2q : L2 ≤ q) (hL2w : L2 ≤ w) (hw : w + 1 ≤ w')
    {Jc : (Fin 2 → ℝ) → ℂ} (hJc : Continuous Jc) {X : ℝ} (hX : 0 ≤ X)
    (hJ : XNorm00Restr (V := Unit) (1 - η) (timeBox (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) ≤ ENNReal.ofReal X) :
    XNorm00Restr (V := Unit) (1 - 2 * η) (timeBox (w' : ℝ) L2 ∪ timeBox (w : ℝ) L2) Set.univ (fun ts _ => clamp2J q Jc ts) ≤
      glueConst η CA * ENNReal.ofReal X := by
  rcases Nat.lt_or_ge (w + 1) w' with h | h
  · exact (crossBound_far_C hθ hη hη0 hL2q (by omega) hJc hX hJ).trans (far_le_glue CA hX (le_trans zero_le_one (one_le_TR hη)))
  · have hw' : w' = w + 1 := by omega
    subst hw'
    rw [Set.union_comm]
    exact (hG q w L2 hL2q hL2w Jc hJc X hX hJ).trans (mul_le_mul' (by unfold glueConst; exact le_self_add) le_rfl)

/-- **All `w + 1 ≤ w'`, trees.** -/
theorem crossBound_T {η : ℝ} (hθ : 0 ≤ 1 - η) (hη : η ≤ 1) (hη0 : 0 ≤ η) {CA : ℝ≥0∞} (hG : ClampGlueT η CA)
    {q w w' L2 : ℕ} (hL2q : L2 ≤ q) (hL2w : L2 ≤ w) (hw : w + 1 ≤ w')
    {Jc : (Fin 2 → ℝ) → ℂ} (hJc : Continuous Jc) {X : ℝ} (hX : 0 ≤ X)
    (hJ : XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) ≤ ENNReal.ofReal X) :
    XNorm00Restr (V := Unit) (1 - 2 * η) (timeBoxGt (w' : ℝ) L2 ∪ timeBoxGt (w : ℝ) L2) Set.univ (fun ts _ => clamp2J q Jc ts) ≤
      glueConst η CA * ENNReal.ofReal X := by
  rcases Nat.lt_or_ge (w + 1) w' with h | h
  · exact (crossBound_far_T hθ hη hη0 hL2q hL2w (by omega) hJc hX hJ).trans (far_le_glue CA hX (le_trans zero_le_one (one_le_TR hη)))
  · have hw' : w' = w + 1 := by omega
    subst hw'
    rw [Set.union_comm]
    exact (hG q w L2 hL2q hL2w Jc hJc X hX hJ).trans (mul_le_mul' (by unfold glueConst; exact le_self_add) le_rfl)


end WaveTurbulence.VineEstS5C.P4.W2.K2
