/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.Restr
public import WaveTurbulence.Foundations.Flower.ProtPin.Tensor2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxCont
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BoxFacts
public import WaveTurbulence.Foundations.Fourier.SchwartzNorm

/-! # D3 PROT-PIN: the time geometry of the terminal cut

* `rn_lift`: a function of the upper clock alone, on `timeBoxGt p q'`, costs the norm of a fixed cutoff in the port
  clock (`timeFourierNorm_tensor2_le`).
* `triS p s = {s < u < T ≤ p+1}` (inside `timeBox p p`), where the integrand of (cut-term) lives.
* `rn_prod_trace`: `(T,u) ↦ K_pre(T,u) · W(u, s)` on `triS` is bounded by the norms of `K_pre` and `W` on
  `timeBoxGt p p` (product, then the trace `σ = s` of the swapped `W`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPin

/-- The unit cutoff in one time, translated to start at `a`. -/
def cut1 (a : ℝ) (y : Fin 1 → ℝ) : ℂ := coordinateCutoff (r := 1) Layered.chiUnit (fun i => y i - a)

/-- Its norm (independent of `a`). -/
def cutNorm (θ : ℝ) : ℝ≥0∞ := timeFourierNorm θ (coordinateCutoff (r := 1) Layered.chiUnit)

theorem cutNorm_lt_top (θ : ℝ) : cutNorm θ < ⊤ :=
  timeFourierNorm_lt_top_of_smooth_compact θ
    (coordinateCutoff_hasCompactSupport Layered.chiUnit_hasCompactSupport)
    (coordinateCutoff_contDiff Layered.chiUnit_contDiff)

theorem cut1_norm (θ a : ℝ) : timeFourierNorm θ (cut1 a) = cutNorm θ := by
  have := timeFourierNorm_translate θ (coordinateCutoff (r := 1) Layered.chiUnit) (fun _ => -a)
  unfold cut1 cutNorm
  rw [← this]
  congr 1

theorem cut1_eq_one {a : ℝ} {y : Fin 1 → ℝ} (h : y 0 ∈ Icc a (a + 1)) : cut1 a y = 1 := by
  unfold cut1
  refine Layered.coordinateCutoff_chiUnit_eq_one fun i => ?_
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The window of the upper clock. -/
def win (p : ℝ) : Set (Fin 1 → ℝ) := {T | T 0 ∈ Icc p (p + 1)}

/-- **Lift**: a function of the upper clock alone. -/
theorem rn_lift {θ : ℝ} (hθ : 0 ≤ θ) (p q' : ℝ) (f : (Fin 1 → ℝ) → ℂ) :
    rn θ (timeBoxGt p q') (fun ts => f (fun _ => ts 0)) ≤ cutNorm θ * rn θ (win p) f := by
  have key : ∀ g : (Fin 1 → ℝ) → ℂ, (∀ T ∈ win p, g T = f T) →
      rn θ (timeBoxGt p q') (fun ts => f (fun _ => ts 0)) ≤ cutNorm θ * timeFourierNorm θ g := by
    intro g hg
    refine (rn_le θ (g := fun ts => g (fun _ => ts 0) * cut1 q' (fun _ => ts 1)) fun ts hts => ?_).trans ?_
    · rw [cut1_eq_one hts.1.2, mul_one]
      exact hg _ hts.1.1
    · refine (timeFourierNorm_tensor2_le hθ g (cut1 q')).trans ?_
      rw [cut1_norm, mul_comm]
  by_cases h0 : cutNorm θ = 0
  · refine (key f fun _ _ => rfl).trans ?_
    rw [h0, zero_mul]
    exact zero_le
  conv_rhs => rw [rn_eq_iInf]
  rw [ENNReal.mul_iInf_of_ne h0 (cutNorm_lt_top θ).ne]
  refine le_iInf fun g => ?_
  rw [ENNReal.mul_iInf_of_ne h0 (cutNorm_lt_top θ).ne]
  exact le_iInf fun hg => key g hg

/-! ### The triangle of the cut and the swapped interior box -/

/-- `s < u < T`, `(T, u) ∈ [p, p+1]²`. -/
def triS (p s : ℝ) : Set (Fin 2 → ℝ) := timeBox p p ∩ {x | s < x 1 ∧ x 1 < x 0}

theorem isOpen_triCond (s : ℝ) : IsOpen {x : Fin 2 → ℝ | s < x 1 ∧ x 1 < x 0} :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter (isOpen_lt (continuous_apply 1) (continuous_apply 0))

theorem triS_closure (p s : ℝ) : ∀ x ∈ triS p s, x ∈ closure (interior (triS p s)) := fun _ hx =>
  VineEstS5C.P4.W2.inter_open_closure_interior (VineEstS3.timeBox_subset_closure_interior p p)
    (isOpen_triCond s) hx

theorem triS_subset (p s : ℝ) : triS p s ⊆ timeBoxGt p p := fun _ hx => ⟨hx.1, hx.2.2⟩

/-- The interior box with the two clocks swapped: `(σ, u)`, `σ < u`. -/
def boxSw (p : ℝ) : Set (Fin 2 → ℝ) := ConjCoh.permT swap2 ⁻¹' timeBoxGt p p

theorem permT_swap2_apply (y : Fin 2 → ℝ) : ConjCoh.permT swap2 y = ![y 1, y 0] := by
  funext i
  fin_cases i <;> rfl

theorem boxSw_eq (p : ℝ) : boxSw p = timeBox p p ∩ {y | y 0 < y 1} := by
  ext y
  simp only [boxSw, Set.mem_preimage, permT_swap2_apply, timeBoxGt, timeBox, Set.mem_setOf_eq, Set.mem_inter_iff,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  tauto

theorem boxSw_closure (p : ℝ) : ∀ y ∈ boxSw p, y ∈ closure (interior (boxSw p)) := by
  rw [boxSw_eq]
  exact fun _ hy => VineEstS5C.P4.W2.inter_open_closure_interior (VineEstS3.timeBox_subset_closure_interior p p)
    (isOpen_lt (continuous_apply 0) (continuous_apply 1)) hy

theorem rn_boxSw (θ p : ℝ) (W : (Fin 2 → ℝ) → ℂ) :
    rn θ (boxSw p) (fun y => W (ConjCoh.permT swap2 y)) = rn θ (timeBoxGt p p) W := by
  rw [boxSw, rn_swap]
  congr 1

/-- **Product and trace on the cut triangle.** -/
theorem rn_prod_trace {θ : ℝ} (hθ : 0 ≤ θ) {p s : ℝ} (hps : p < s) (hsp : s < p + 1)
    (Kp W : (Fin 2 → ℝ) → ℂ) (hW : Continuous W)
    (hKfin : rn θ (timeBoxGt p p) Kp < ⊤) (hWfin : rn θ (timeBoxGt p p) W < ⊤) :
    rn θ (triS p s) (fun x => Kp x * W ![x 1, s]) ≤
      ENNReal.ofReal (2 ^ θ) * Regref.traceConst (r := 2) θ VineEstS3.chiUnit * rn θ (timeBoxGt p p) Kp *
        rn θ (timeBoxGt p p) W := by
  set Φ : (Fin 2 → ℝ) → ℂ := fun x => W ![x 1, s] with hΦ
  have hΦc : Continuous Φ := hW.comp (by fun_prop)
  -- the trace
  have htr : rn θ (triS p s) Φ ≤ Regref.traceConst (r := 2) θ VineEstS3.chiUnit * rn θ (timeBoxGt p p) W := by
    have h1 := rn_trace hθ (fun _ => p) (B := boxSw p) (Bt := triS p s)
      (fun x hx i => by
        obtain ⟨⟨h0, h1⟩, -⟩ := hx
        fin_cases i
        · exact h0
        · exact h1)
      (fun y => W (ConjCoh.permT swap2 y)) (hW.comp (by
        rw [show (ConjCoh.permT swap2 : (Fin 2 → ℝ) → Fin 2 → ℝ) = fun y => ![y 1, y 0] from
          funext permT_swap2_apply]
        fun_prop)) 0 s
      (fun x hx => boxSw_closure p _ (by
        obtain ⟨⟨-, h1⟩, hs, hu⟩ := hx
        rw [boxSw_eq]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · simp only [Function.update_self]; exact ⟨hps.le, hsp.le⟩
        · simp only [ne_eq, one_ne_zero, not_false_eq_true, Function.update_of_ne]; exact h1
        · simp only [mem_setOf_eq, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true,
            Function.update_of_ne]
          exact hs))
    rw [rn_boxSw] at h1
    refine le_trans (le_of_eq (rn_congr θ fun x _ => ?_)) h1
    simp only [hΦ, permT_swap2_apply, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true,
      Function.update_of_ne]
  have hKfin' : rn θ (triS p s) Kp < ⊤ := (rn_mono_set θ (triS_subset p s) Kp).trans_lt hKfin
  have hΦfin : rn θ (triS p s) Φ < ⊤ :=
    htr.trans_lt (ENNReal.mul_lt_top (traceConst_lt_top θ) hWfin)
  calc rn θ (triS p s) (fun x => Kp x * Φ x)
      ≤ ENNReal.ofReal (2 ^ θ) * rn θ (triS p s) Kp * rn θ (triS p s) Φ :=
        rn_mul_le hθ (triS_closure p s) Kp Φ hΦc hKfin' hΦfin
    _ ≤ ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) Kp *
          (Regref.traceConst (r := 2) θ VineEstS3.chiUnit * rn θ (timeBoxGt p p) W) :=
        mul_le_mul' (mul_le_mul' le_rfl (rn_mono_set θ (triS_subset p s) Kp)) htr
    _ = _ := by ring

end WaveTurbulence.Flower.ProtPin
