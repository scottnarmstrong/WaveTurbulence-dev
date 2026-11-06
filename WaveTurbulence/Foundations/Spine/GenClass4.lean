/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GenClass3
import Mathlib.Tactic
/-! The class bound: the sum over patterns of the `gen_core` bounds. -/
@[expose] public section
open MeasureTheory Set Finset Function
open scoped ENNReal
namespace WaveTurbulence.Ladder
open scoped Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Type} [Fintype Q] [DecidableEq Q] {K : Q → ℕ}

theorem class_bound
    (ch : ι → ι → Prop) (dep : ι → ℕ) (hdep : ∀ a b, ch a b → dep b < dep a)
    (huniq : ∀ a b b', ch a b → ch a b' → b = b')
    (ua va : Jr K → ι) (hinj : Function.Injective (Sum.elim ua va))
    (ls cap : ι → ℝ) (D : ℝ) (hD : 0 ≤ D) (hbox : ∀ v, 0 ≤ ls v ∧ ls v + 1 ≤ D)
    (hval : ∀ t ∈ Om0 ch ls cap, ∀ q, NP (fun j : Fin (K q) => max (t (ua ⟨q, j⟩)) (t (va ⟨q, j⟩))))
    (A : Finset ι) (Sy : ι → Set ℝ) (hSy : ∀ b, MeasurableSet (Sy b)) (Kc : ℝ≥0∞)
    (hKc : ∀ b (β : ℝ), ∫⁻ a in Sy b, ENNReal.ofReal (br (a + β))⁻¹ ≤ Kc)
    (ρb : Jr K → ℝ) (W : Set (ι → ℝ))
    (hloc : ∀ θ : Jr K → Bool, ∃ hX : ι → (ι → ℝ) → ℝ, (∀ x, Measurable (hX x)) ∧
      (∀ x (β β' : ι → ℝ), (∀ b, b ∉ Finset.univ.image (xθ ua va θ) → β b = β' b) → hX x β = hX x β') ∧
      ∀ α ∈ W, (∀ b, b ∉ Finset.univ.image (xθ ua va θ) → α b ∈ Sy b) ∧
        ∀ j, |α (xθ ua va θ j) - hX (xθ ua va θ j) α| ≤ ρb j) :
    ∫⁻ α in W, ‖Phi (Om0 ch ls cap) ls A α‖ₑ ≤ 2 ^ Fintype.card (Jr K) *
      ((∏ j, ENNReal.ofReal (2 * ρb j)) *
        ((∏ q, ENNReal.ofReal (2 ^ (K q) * D ^ (K q) / (Nat.factorial (K q) : ℝ))) *
          ENNReal.ofReal (Real.pi ^ Fintype.card ι * 3 ^ (Fintype.card ι - Fintype.card (Jr K))) *
          (2 * Kc) ^ (Fintype.card ι - Fintype.card (Jr K)))) := by
  set σ : Fin (Fintype.card (Jr K)) ≃ Jr K := (Fintype.equivFin (Jr K)).symm with hσ
  set Ωs : (Jr K → Bool) → Set (ι → ℝ) := fun θ =>
    OmegaC ls cap (ltθ ch ua va θ) (leθ ua va θ) (fun i => xθ ua va θ (σ i)) (RvOf σ D) with hΩs
  have hmeas : ∀ θ, MeasurableSet (Ωs θ) := fun θ =>
    measurableSet_OmegaC ls cap _ _ _ _ (measurableSet_RvOf σ D)
  have hpart := fun t => pattern_partition ch ua va ls cap σ D hbox hval
    (fun θ i => xθ ua va θ (σ i)) (fun θ i => rfl) t
  have hsum : ∀ α, Phi (Om0 ch ls cap) ls A α = ∑ θ, Phi (Ωs θ) ls A α :=
    fun α => Phi_eq_sum (Om0 ch ls cap) Ωs hmeas (∑ v, (|ls v| + 1))
      (fun θ => bdd_OmegaC ls cap _ _ _ _) hpart ls A α
  have h1 : ∀ α, ‖Phi (Om0 ch ls cap) ls A α‖ₑ ≤ ∑ θ, ‖Phi (Ωs θ) ls A α‖ₑ := by
    intro α; rw [hsum α]; exact enorm_sum_le _ _
  have hcont : ∀ θ, Measurable (fun α => ‖Phi (Ωs θ) ls A α‖ₑ) := fun θ =>
    (continuous_Phi (Ωs θ) (hmeas θ) _ (bdd_OmegaC ls cap _ _ _ _) ls A).measurable.enorm
  calc ∫⁻ α in W, ‖Phi (Om0 ch ls cap) ls A α‖ₑ ≤ ∫⁻ α in W, ∑ θ, ‖Phi (Ωs θ) ls A α‖ₑ :=
        lintegral_mono h1
    _ = ∑ θ, ∫⁻ α in W, ‖Phi (Ωs θ) ls A α‖ₑ := lintegral_finset_sum _ (fun θ _ => hcont θ)
    _ ≤ ∑ _θ : Jr K → Bool, ((∏ j, ENNReal.ofReal (2 * ρb j)) *
        ((∏ q, ENNReal.ofReal (2 ^ (K q) * D ^ (K q) / (Nat.factorial (K q) : ℝ))) *
          ENNReal.ofReal (Real.pi ^ Fintype.card ι * 3 ^ (Fintype.card ι - Fintype.card (Jr K))) *
          (2 * Kc) ^ (Fintype.card ι - Fintype.card (Jr K)))) := by
        refine Finset.sum_le_sum (fun θ _ => ?_)
        obtain ⟨hX, hXm, hXd, hW'⟩ := hloc θ
        obtain ⟨m, hm, hb⟩ := theta_bound ch dep hdep huniq ua va hinj ls cap D hD σ θ A Sy hSy Kc hKc ρb hX hXm hXd W hW'
        have hm' : m = Fintype.card ι - Fintype.card (Jr K) := by omega
        subst hm'
        rw [← hm] at hb
        exact hb
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul]
        push_cast; ring

end WaveTurbulence.Ladder
