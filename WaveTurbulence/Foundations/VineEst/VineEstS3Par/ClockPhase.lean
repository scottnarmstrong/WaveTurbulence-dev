/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.SignedParam
public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSKernel

/-! # The mode phases of clocked weights (engine step MOD)

A weight row `ρ` depends on two clocks, each either an internal time variable `τ_v` or an output time
`t_c`.  For an integer mode `m_ρ ∈ ℤ²` the product over rows of `e^{πi m_ρ · clock_ρ}` equals
`paramFactor Δ_m τ · e^{πi ν_m · tt}`, with `Δ_m`, `ν_m` the mode totals per slot.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS Finset
open scoped ENNReal

variable {d : ℕ} (D : SumintPar.SumintDatum d)

/-- Weight rows: the `𝒦` rows and the `ℒ` rows. -/
abbrev Row : Type := D.S.VIdx ⊕ D.S.VIdx

/-- Time slots: an internal time variable or one of the three output times. -/
abbrev Slot : Type := D.S.TVar ⊕ Fin 3

/-- The value of a slot. -/
def slotVal (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) : Slot D → ℝ := Sum.elim τ tt

/-- The mode total at a slot. -/
noncomputable def slotTotal (slot : Row D → Fin 2 → Slot D) (m : Row D → Fin 2 → ℤ) (s : Slot D) : ℝ :=
  ∑ ρ, ∑ i, if slot ρ i = s then (m ρ i : ℝ) else 0

/-- The internal parameter shift of a mode. -/
noncomputable def modeParam (slot : Row D → Fin 2 → Slot D) (m : Row D → Fin 2 → ℤ) : D.S.TVar → ℝ :=
  fun v => slotTotal D slot m (Sum.inl v)

/-- The external frequency of a mode. -/
noncomputable def modeFreq (slot : Row D → Fin 2 → Slot D) (m : Row D → Fin 2 → ℤ) : Fin 3 → ℝ :=
  fun c => slotTotal D slot m (Sum.inr c)

/-- The unimodular output factor `e^{πi ν · tt}`. -/
noncomputable def outFactor (ν tt : Fin 3 → ℝ) : ℂ :=
  Complex.exp ((Real.pi * ∑ c, ν c * tt c : ℝ) * Complex.I)

theorem fsPhase_eq_exp {r : ℕ} (m : Fin r → ℤ) (t : Fin r → ℝ) :
    fsPhase m t = Complex.exp ((Real.pi * ∑ i, (m i : ℝ) * t i : ℝ) * Complex.I) := by
  unfold fsPhase
  rw [Real.fourierChar_apply]
  congr 1
  have : timePairing r t (fun i => (m i : ℝ) / 2) = ∑ i, (m i : ℝ) * t i / 2 := by
    show ∑ i, t i * ((m i : ℝ) / 2) = _
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  push_cast
  rw [← Finset.sum_div]
  ring


theorem sum_slot_identity (slot : Row D → Fin 2 → Slot D) (m : Row D → Fin 2 → ℤ) (val : Slot D → ℝ) :
    ∑ ρ, ∑ i, (m ρ i : ℝ) * val (slot ρ i) = ∑ s, slotTotal D slot m s * val s := by
  classical
  have h : ∀ s : Slot D, slotTotal D slot m s * val s =
      ∑ ρ : Row D, ∑ i : Fin 2, if slot ρ i = s then (m ρ i : ℝ) * val s else 0 := by
    intro s
    unfold slotTotal
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  calc ∑ ρ, ∑ i, (m ρ i : ℝ) * val (slot ρ i)
      = ∑ ρ : Row D, ∑ i : Fin 2, ∑ s : Slot D, if slot ρ i = s then (m ρ i : ℝ) * val s else 0 := by
        refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ ρ : Row D, ∑ s : Slot D, ∑ i : Fin 2, if slot ρ i = s then (m ρ i : ℝ) * val s else 0 :=
        Finset.sum_congr rfl fun ρ _ => Finset.sum_comm
    _ = ∑ s : Slot D, ∑ ρ : Row D, ∑ i : Fin 2, if slot ρ i = s then (m ρ i : ℝ) * val s else 0 :=
        Finset.sum_comm
    _ = ∑ s, slotTotal D slot m s * val s := (Finset.sum_congr rfl fun s _ => (h s).symm)

theorem prod_fsPhase_clock (slot : Row D → Fin 2 → Slot D) (m : Row D → Fin 2 → ℤ)
    (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) :
    ∏ ρ, fsPhase (m ρ) (fun i => slotVal D τ tt (slot ρ i)) =
      paramFactor D (modeParam D slot m) τ * outFactor (modeFreq D slot m) tt := by
  unfold paramFactor outFactor
  simp_rw [fsPhase_eq_exp]
  rw [← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  have hs := sum_slot_identity D slot m (slotVal D τ tt)
  have hs' := hs.trans (Fintype.sum_sum_type (fun s : Slot D => slotTotal D slot m s * slotVal D τ tt s))
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sum, ← add_mul,
    ← Complex.ofReal_add, ← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
  congr 3

end WaveTurbulence.VineEstS3Par.Eng
