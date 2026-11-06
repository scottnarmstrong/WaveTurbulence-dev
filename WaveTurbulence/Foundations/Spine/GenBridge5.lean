/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GenBridge4
import Mathlib.Tactic
/-! The `α`-integral of `‖Phi‖` over a localized region, from `core1` and the bridge. -/
@[expose] public section
open MeasureTheory Set Finset Function
open scoped ENNReal
namespace WaveTurbulence.Ladder
open scoped Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k m : ℕ}

theorem volume_Rmod_lt_top (ls cap : ι → ℝ) (lt le : ι → ι → Prop) (xv : Fin k → ι)
    (Rv : Set (Fin k → ℝ)) : volume (Rmod ls cap lt le xv Rv) < ⊤ := by
  have hc : IsCompact (Set.pi univ (fun i : Fin k => Icc (ls (xv i)) (ls (xv i) + 1))) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  refine lt_of_le_of_lt (measure_mono ?_) hc.measure_lt_top
  intro tx htx i _
  exact htx.2.1 i

theorem norm_wXf_le (e : ι ≃ Fin k ⊕ Fin m) (ls cap : ι → ℝ) (lt le : ι → ι → Prop)
    (Rv : Set (Fin k → ℝ)) (A : Finset ι) :
    ∀ tx ∈ Rmod ls cap lt le (fun i => e.symm (Sum.inl i)) Rv,
      ‖wXf e ls A tx‖ ≤ Real.pi ^ (k + m) := by
  intro tx htx
  have hπ : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  unfold wXf cYf
  rw [norm_mul, norm_prod, norm_prod, add_comm k m, pow_add]
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · calc ∏ j : Fin m, ‖if e.symm (Sum.inr j) ∈ A then ((Real.pi : ℝ) : ℂ) * Complex.I else 1‖
        ≤ ∏ _j : Fin m, Real.pi := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => ?_)
          split_ifs
          · simp [abs_of_pos Real.pi_pos]
          · simpa using hπ
      _ = Real.pi ^ m := by simp
  · calc ∏ i : Fin k, ‖if e.symm (Sum.inl i) ∈ A then
          ((Real.pi * (tx i - ls (e.symm (Sum.inl i))) : ℝ) : ℂ) * Complex.I else 1‖
        ≤ ∏ _i : Fin k, Real.pi := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => ?_)
          split_ifs
          · have := htx.2.1 i
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
              abs_of_pos Real.pi_pos]
            have h1 : |tx i - ls (e.symm (Sum.inl i))| ≤ 1 := by
              rw [abs_le]; constructor <;> linarith [this.1, this.2]
            nlinarith [Real.pi_pos]
          · simpa using hπ
      _ = Real.pi ^ k := by simp

theorem gen_core (e : ι ≃ Fin k ⊕ Fin m) (ls cap : ι → ℝ) (lt le : ι → ι → Prop)
    (Rv : Set (Fin k → ℝ)) (hRv : MeasurableSet Rv) (par : Par m) (hp : ParOK par)
    (hpar : ∀ j j', par j = some j' ↔ lt (e.symm (Sum.inr j)) (e.symm (Sum.inr j')))
    (hle : ∀ j j', ¬ le (e.symm (Sum.inr j)) (e.symm (Sum.inr j')))
    (A : Finset ι) (S : Fin m → Set ℝ) (hS : ∀ v, MeasurableSet (S v)) (K : ℝ≥0∞)
    (hK : ∀ v (β : ℝ), ∫⁻ a in S v, ENNReal.ofReal (br (a + β))⁻¹ ≤ K)
    (h : (Fin m → ℝ) → (Fin k → ℝ)) (hh : Measurable h) (ρ : Fin k → ℝ) (W : Set (ι → ℝ))
    (hW : ∀ α ∈ W, (Th e α).2 ∈ Set.pi univ S ∧ ∀ i, |(Th e α).1 i - h (Th e α).2 i| ≤ ρ i) :
    ∫⁻ α in W, ‖Phi (OmegaC ls cap lt le (fun i => e.symm (Sum.inl i)) Rv) ls A α‖ₑ ≤
      (∏ i, ENNReal.ofReal (2 * ρ i)) *
        (volume (Rmod ls cap lt le (fun i => e.symm (Sum.inl i)) Rv) *
          ENNReal.ofReal (Real.pi ^ (k + m) * 3 ^ m) * (2 * K) ^ m) := by
  have step1 : ∀ α, ‖Phi (OmegaC ls cap lt le (fun i => e.symm (Sum.inl i)) Rv) ls A α‖ₑ =
      ‖Bprod par (fun j => ls (e.symm (Sum.inr j))) (fun j => decide (e.symm (Sum.inr j) ∈ A))
        (loF (fun j => ls (e.symm (Sum.inr j))) (LBf lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j))))
        (hiF (fun j => ls (e.symm (Sum.inr j))) (fun j => cap (e.symm (Sum.inr j))) (UBf lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j))))
        (Rmod ls cap lt le (fun i => e.symm (Sum.inl i)) Rv) (wXf e ls A) (Th e α)‖ₑ := fun α => by
    rw [Phi_eq_Bprod e ls cap lt le Rv hRv par hpar hle A α]
  simp_rw [step1]
  set F : (Fin k → ℝ) × (Fin m → ℝ) → ℝ≥0∞ := fun p =>
    ‖Bprod par (fun j => ls (e.symm (Sum.inr j))) (fun j => decide (e.symm (Sum.inr j) ∈ A))
        (loF (fun j => ls (e.symm (Sum.inr j))) (LBf lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j))))
        (hiF (fun j => ls (e.symm (Sum.inr j))) (fun j => cap (e.symm (Sum.inr j))) (UBf lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j))))
        (Rmod ls cap lt le (fun i => e.symm (Sum.inl i)) Rv) (wXf e ls A) p‖ₑ with hF
  have hW' : W = (Th e) ⁻¹' ((Th e).symm ⁻¹' W) := by
    ext α; simp
  have hcomp : ∫⁻ α in W, F (Th e α) = ∫⁻ p in (Th e).symm ⁻¹' W, F p := by
    conv_lhs => rw [hW']
    exact (Th_mp e).setLIntegral_comp_preimage_emb (Th e).measurableEmbedding F _
  rw [hcomp]
  have hπ : 0 ≤ Real.pi ^ (k + m) := by positivity
  refine core1 par hp (fun j => ls (e.symm (Sum.inr j))) (fun j => decide (e.symm (Sum.inr j) ∈ A))
    (loF (fun j => ls (e.symm (Sum.inr j))) (LBf lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j))))
    (hiF (fun j => ls (e.symm (Sum.inr j))) (fun j => cap (e.symm (Sum.inr j))) (UBf lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j))))
    (fun tx v => ?_) (fun tx v _ => ?_) (Rmod ls cap lt le (fun i => e.symm (Sum.inl i)) Rv)
    (measurableSet_Rmod ls cap lt le _ Rv hRv) (volume_Rmod_lt_top ls cap lt le _ Rv).ne (wXf e ls A) _ hπ
    (norm_wXf_le e ls cap lt le Rv A) S hS K hK h hh ρ _ ?_
  · have h1 := hiF_le (fun j => ls (e.symm (Sum.inr j))) (fun j => cap (e.symm (Sum.inr j))) (UBf lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j))) tx v
    have h2 := le_loF (fun j => ls (e.symm (Sum.inr j))) (LBf lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j))) tx v
    linarith
  · exact ⟨le_loF (fun j => ls (e.symm (Sum.inr j))) _ tx v, hiF_le (fun j => ls (e.symm (Sum.inr j))) (fun j => cap (e.symm (Sum.inr j))) _ tx v⟩
  · intro p hp'
    have := hW ((Th e).symm p) hp'
    simpa using this

end WaveTurbulence.Ladder
