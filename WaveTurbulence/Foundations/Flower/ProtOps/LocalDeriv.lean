/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOps.Bump
public import WaveTurbulence.Foundations.Fourier.TimeBasic
public import WaveTurbulence.Foundations.Fourier.TimeInterpolation

/-! # PROT-OPS: finite superpositions of bumps (o73 (13.4))

* `timeFourier_finsum`: the time Fourier transform of a finite sum `∑ g j · c j`.
* `norm_word_le`: an iterated-derivative word of `∑ c j · psi_j` is at most `L^N B ∑ ‖c j‖`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence MeasureTheory WaveTurbulence.Fourier
open scoped ContDiff ENNReal

namespace WaveTurbulence.Flower.ProtOps

theorem timeFourier_finsum {r : ℕ} {ι : Type*} [DecidableEq ι] (S : Finset ι) (g : ι → (Fin r → ℝ) → ℂ)
    (hg : ∀ j ∈ S, Integrable (g j)) (c : ι → ℂ) :
    timeFourier (fun t => ∑ j ∈ S, g j t * c j) = fun ξ => ∑ j ∈ S, timeFourier (g j) ξ * c j := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact timeFourier_zero r
  | insert a S ha ih =>
    have hS : ∀ j ∈ S, Integrable (g j) := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have h1 : Integrable (fun t => g a t * c a) := (hg a (Finset.mem_insert_self _ _)).mul_const _
    have h2 : Integrable (fun t => ∑ j ∈ S, g j t * c j) :=
      integrable_finsetSum _ fun j hj => (hS j hj).mul_const _
    simp only [Finset.sum_insert ha]
    rw [timeFourier_add h1 h2, ih hS]
    funext ξ
    have := congrFun (timeFourier_smul (r := r) (c a) (g a)) ξ
    simp only [smul_eq_mul] at this
    rw [show (fun t => g a t * c a) = fun t => c a * g a t from funext fun t => mul_comm _ _, this, mul_comm]

/-- The translate `y ↦ psi (L (y - a))`, as a complex function. -/
def psiT (d : ℕ) (L : ℝ) (a : Mom d) (y : Mom d) : ℂ := ((psi d (L • (y - a)) : ℝ) : ℂ)

theorem psiT_contDiff (d : ℕ) (L : ℝ) (a : Mom d) {n : ℕ∞} : ContDiff ℝ n (psiT d L a) := by
  unfold psiT
  exact Complex.ofRealCLM.contDiff.comp ((psi_contDiff d).comp (by fun_prop))

theorem norm_iteratedFDeriv_psiT_le {d N : ℕ} {B : ℝ}
    (hB : ∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n (psi d) x‖ ≤ B)
    {L : ℝ} (hL : 1 ≤ L) (a : Mom d) {n : ℕ} (hn : n ≤ N) (x : Mom d) :
    ‖iteratedFDeriv ℝ n (psiT d L a) x‖ ≤ L ^ N * B := by
  have hf : ContDiffAt ℝ (n : WithTop ℕ∞) (fun y : Mom d => psi d (L • (y - a))) x :=
    ((psi_contDiff d (n := (n : ℕ∞))).comp (by fun_prop : ContDiff ℝ (n : ℕ∞) fun y : Mom d => L • (y - a))).contDiffAt
  have h := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) hf (i := n) le_rfl
  have h' : iteratedFDeriv ℝ n (psiT d L a) x =
      iteratedFDeriv ℝ n (Complex.ofRealLI ∘ fun y : Mom d => psi d (L • (y - a))) x := rfl
  rw [h', h]
  exact norm_iteratedFDeriv_bump_le hB hL a hn x

end WaveTurbulence.Flower.ProtOps
