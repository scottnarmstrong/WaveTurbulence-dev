/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockedExpr
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockPhase

/-! # Arity-3 clocked weights (V5 Step 4d-A, item 2)

Every weight row has THREE clocks (so that a joint three-clock factor such as the extracted time difference
`H(t₁, s₁, t₀)` is one row); two-clock rows embed with a zero third mode (`A3Modes`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS3Par.Eng Finset MeasureTheory
open scoped ENNReal

variable {d : ℕ} (D : SumintPar.SumintDatum d)

/-- Clock-dependent weights: a function of a clock pair, of the output difference `r = e - f` and of the row
momentum, and the two slots of the clock pair.  The `ℒ` rows do not depend on `r`. -/
structure ClockedRows3 where
  W : Row D → (Fin 3 → ℝ) → Mom d → Mom d → ℂ
  slot : Row D → Fin 3 → Slot D
  W_indep : ∀ (v : D.S.VIdx) (c : Fin 3 → ℝ) (r r' k : Mom d), W (Sum.inr v) c r k = W (Sum.inr v) c r' k


theorem norm_fsPhase3 {r : ℕ} (m : Fin r → ℤ) (t : Fin r → ℝ) : ‖fsPhase m t‖ = 1 := by
  unfold fsPhase; exact Circle.norm_coe _

variable {D}

/-- The clock pair of row `ρ`. -/
def ClockedRows3.clock (cr : ClockedRows3 D) (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) (ρ : Row D) : Fin 3 → ℝ :=
  fun i => slotVal D τ tt (cr.slot ρ i)

/-- The integrand of the clocked `sumint` expression. -/
noncomputable def clockedIntegrand3 (cr : ClockedRows3 D)
    (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (E : Fin 4 → Mom d) (tt : Fin 3 → ℝ)
    (τ : D.S.TVar → ℝ) : ℂ :=
  D.phase L γ δ η x (E 0 - E 1) (tt 0) τ *
    ∏ ρ, cr.W ρ (cr.clock τ tt ρ) (E 0 - E 1) (rowMom D L x E ρ)

variable (D)

/-- The mode total at a slot. -/
noncomputable def slotTotal3 (slot : Row D → Fin 3 → Slot D) (m : Row D → Fin 3 → ℤ) (s : Slot D) : ℝ :=
  ∑ ρ, ∑ i, if slot ρ i = s then (m ρ i : ℝ) else 0

/-- The internal parameter shift of a mode. -/
noncomputable def modeParam3 (slot : Row D → Fin 3 → Slot D) (m : Row D → Fin 3 → ℤ) : D.S.TVar → ℝ :=
  fun v => slotTotal3 D slot m (Sum.inl v)

/-- The external frequency of a mode. -/
noncomputable def modeFreq3 (slot : Row D → Fin 3 → Slot D) (m : Row D → Fin 3 → ℤ) : Fin 3 → ℝ :=
  fun c => slotTotal3 D slot m (Sum.inr c)

theorem sum_slot_identity3 (slot : Row D → Fin 3 → Slot D) (m : Row D → Fin 3 → ℤ) (val : Slot D → ℝ) :
    ∑ ρ, ∑ i, (m ρ i : ℝ) * val (slot ρ i) = ∑ s, slotTotal3 D slot m s * val s := by
  classical
  have h : ∀ s : Slot D, slotTotal3 D slot m s * val s =
      ∑ ρ : Row D, ∑ i : Fin 3, if slot ρ i = s then (m ρ i : ℝ) * val s else 0 := by
    intro s
    unfold slotTotal3
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  calc ∑ ρ, ∑ i, (m ρ i : ℝ) * val (slot ρ i)
      = ∑ ρ : Row D, ∑ i : Fin 3, ∑ s : Slot D, if slot ρ i = s then (m ρ i : ℝ) * val s else 0 := by
        refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ ρ : Row D, ∑ s : Slot D, ∑ i : Fin 3, if slot ρ i = s then (m ρ i : ℝ) * val s else 0 :=
        Finset.sum_congr rfl fun ρ _ => Finset.sum_comm
    _ = ∑ s : Slot D, ∑ ρ : Row D, ∑ i : Fin 3, if slot ρ i = s then (m ρ i : ℝ) * val s else 0 :=
        Finset.sum_comm
    _ = ∑ s, slotTotal3 D slot m s * val s := (Finset.sum_congr rfl fun s _ => (h s).symm)

theorem prod_fsPhase_clock3 (slot : Row D → Fin 3 → Slot D) (m : Row D → Fin 3 → ℤ)
    (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) :
    ∏ ρ, fsPhase (m ρ) (fun i => slotVal D τ tt (slot ρ i)) =
      paramFactor D (modeParam3 D slot m) τ * outFactor (modeFreq3 D slot m) tt := by
  unfold paramFactor outFactor
  simp_rw [fsPhase_eq_exp]
  rw [← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  have hs := sum_slot_identity3 D slot m (slotVal D τ tt)
  have hs' := hs.trans (Fintype.sum_sum_type (fun s : Slot D => slotTotal3 D slot m s * slotVal D τ tt s))
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sum, ← add_mul,
    ← Complex.ofReal_add, ← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
  congr 3


end WaveTurbulence.VineEstS3Par.Eng
