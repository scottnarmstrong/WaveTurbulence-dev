/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.BlockTraceUniformBudget
public import WaveTurbulence.Foundations.ClassJR.Reindex
public import Mathlib.Data.Fintype.EquivFin

/-! # Separating traced non-special energies from the surviving energies -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR
open scoped ENNReal

/-- Every traced energy is active when the trace set avoids special links. -/
def activeTraceSplit {ι : Type} [DecidableEq ι] (T J : Finset ι) (h : Disjoint T J) :
    {i // i ∉ J} ≃ {i // i ∈ T} ⊕ {i // i ∉ T ∧ i ∉ J} where
  toFun i := if hi : i.val ∈ T then Sum.inl ⟨i.val,hi⟩ else Sum.inr ⟨i.val,hi,i.property⟩
  invFun
    | .inl i => ⟨i.val,fun hj => Finset.disjoint_left.mp h i.property hj⟩
    | .inr i => ⟨i.val,i.property.2⟩
  left_inv i := by
    dsimp only
    by_cases hi : i.val ∈ T
    · simp only [dite_eq_left hi]
    · simp only [dite_eq_right hi]
  right_inv i := by
    rcases i with i | i
    · dsimp only
      rw [dite_eq_left i.property]
    · dsimp only
      rw [dite_eq_right i.property.1]

/-- Enumerate just the frozen block; leave all surviving indices literal. -/
def activeTraceEquiv {ι : Type} [DecidableEq ι] (T J : Finset ι) (h : Disjoint T J) :
    {i // i ∉ J} ≃ Fin T.card ⊕ {i // i ∉ T ∧ i ∉ J} :=
  (activeTraceSplit T J h).trans (Equiv.sumCongr T.equivFin (Equiv.refl _))

/-- The coefficient restricted to zero on all traced energies at once. -/
def energyTraceCoefficient {ι : Type} [DecidableEq ι] (T J : Finset ι)
    (h : Disjoint T J) (C : ({i // i ∉ J} → ℝ) → ℝ × ℝ → ℂ) :
    ({i // i ∉ T ∧ i ∉ J} → ℝ) → ℝ × ℝ → ℂ :=
  blockTraceSymbol (fun α lam => C (fun i => α (activeTraceEquiv T J h i)) lam)

/-- The relabelling and block trace evaluate the original coefficient at
the actual zero energies, without a change of scale or determinant. -/
theorem energyTraceCoefficient_apply {ι : Type} [DecidableEq ι] (T J : Finset ι)
    (h : Disjoint T J) (C : ({i // i ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (β : {i // i ∉ T ∧ i ∉ J} → ℝ) (lam : ℝ × ℝ) :
    energyTraceCoefficient T J h C β lam =
      C (fun i => if hi : i.val ∈ T then 0 else β ⟨i.val,hi,i.property⟩) lam := by
  unfold energyTraceCoefficient blockTraceSymbol
  apply congrArg (fun α => C α lam)
  funext i
  by_cases hi : i.val ∈ T <;>
    simp [activeTraceEquiv,activeTraceSplit,hi]

/-- On a genuine zero-energy configuration the restricted coefficient is
exactly the original coefficient, with all surviving energies untouched. -/
theorem energyTraceCoefficient_eq_of_zero {ι : Type} [DecidableEq ι]
    (T J : Finset ι) (h : Disjoint T J)
    (C : ({i // i ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (α : ι → ℝ) (hα : ∀ i ∈ T, α i = 0) (lam : ℝ × ℝ) :
    energyTraceCoefficient T J h C (fun i => α i.val) lam =
      C (fun i => α i.val) lam := by
  rw [energyTraceCoefficient_apply]
  apply congrArg (fun β => C β lam)
  funext i
  by_cases hi : i.val ∈ T
  · simp only [dite_eq_left hi, hα i.val hi]
  · simp only [dite_eq_right hi]

/-- All smoothness and section integrability needed for NT survive the
literal simultaneous trace. -/
theorem symReg_energyTraceCoefficient {ι : Type} [Fintype ι] [DecidableEq ι]
    (T J : Finset ι) (h : Disjoint T J)
    {C : ({i // i ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : ClassJR.SymReg C) :
    ClassJR.SymReg (energyTraceCoefficient T J h C) :=
  symReg_blockTraceSymbol (hC.reindex (activeTraceEquiv T J h))

/-- The J3 derivative mass is unchanged by the finite relabelling before
the literal zero-energy block trace is taken. -/
theorem energyTraceCoefficient_mass_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (T J : Finset ι) (h : Disjoint T J) (hT : T.Nonempty)
    {C : ({i // i ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C)
    {θ N A : ℝ} (hN : 0 ≤ N) (hA : 0 ≤ A)
    (hmain : ∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N A k) :
    (∫⁻ lam, wL θ lam*derivativeCoefficientEnvelope (energyTraceCoefficient T J h C) lam) ≤
      ENNReal.ofReal ((4*max 1 (4*A))^T.card*(T.card:ℝ)^T.card*((2*T.card).factorial:ℝ))*
        (ENNReal.ofReal N * ∑' k : ℕ,
          ENNReal.ofReal ((4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial)) := by
  have hmain' (k : ℕ) :
      (∫⁻ α, ∫⁻ lam, wL θ lam *
        dnorm k (fun β lam => C (fun i => β (activeTraceEquiv T J h i)) lam) α lam) ≤ gev N A k := by
    simp_rw [dnorm_reindex]
    exact (lintegral_reindex (activeTraceEquiv T J h)
      (F := fun α => ∫⁻ lam, wL θ lam*dnorm k C α lam)).le.trans (hmain k)
  exact derivativeCoefficientEnvelope_blockTrace_mass_uniform_le
    (Finset.card_pos.mpr hT) (hC.reindex (activeTraceEquiv T J h)) hN hA hmain'

end WaveTurbulence.RegAsymp
