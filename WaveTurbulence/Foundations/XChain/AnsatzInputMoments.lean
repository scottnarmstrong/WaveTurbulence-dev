/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.XChain.SysDraft.API
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
/-! Classed source solutions and the internal l1 moment invariant supply every cmattr input hypothesis. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Set
open scoped ENNReal

section
variable {P : WTParams} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : (Fin P.d → ℤ) → Ω → ℂ} {a : Ω → ℝ → (Fin P.d → ℤ) → ℂ} {Fev : ℕ → Set Ω}
    {R : ℕ → Mom P.d → ℝ} {E : ℕ → (Fin P.d → ℤ) → ℝ}
    {Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ} {p : ℕ}

theorem ansatz_input_summable (ha : AnsatzAt P μ g a Fev R E Et p) (hL : 0 < P.L) :
    ∀ᵐ ω ∂μ.restrict (Fev p), Summable (fun n => ‖a ω p n‖) := by
  filter_upwards [ae_restrict_mem ha.1.1] with ω hω
  exact SysAPI.IsASolution.summable_norm hL (ha.1.2.2.2.2.1 ω hω).1 ⟨Nat.cast_nonneg _, le_rfl⟩

theorem ansatz_input_all_memLp (ha : AnsatzAt P μ g a Fev R E Et p) (hL : 0 < P.L)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖a ω p n‖) (q : ℝ≥0∞) (μ.restrict (Fev p))) :
    ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => a ω p n) (q : ℝ≥0∞) (μ.restrict (Fev p)) := by
  intro n q hq
  apply (hM q hq).mono' (ha.1.2.2.2.2.2.1 p ⟨Nat.cast_nonneg _, le_rfl⟩ n).aestronglyMeasurable
  filter_upwards [ansatz_input_summable ha hL] with ω hω
  exact hω.le_tsum n (fun m _ => norm_nonneg _)

end
end WaveTurbulence.Induct
