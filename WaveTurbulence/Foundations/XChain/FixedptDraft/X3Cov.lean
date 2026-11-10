/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Meas

/-!
# X3: phase covariance of the couple quantities (gauge and translation symmetry)

A *cubic phase* `φ` is a unit phase with `φ(q₁) φ̄(q₂) φ(n − q₁ + q₂) = φ(n)`. The gauge phases `e^{iθ}` and the
translation phases `e^{−2πi⟨n/L, x₀⟩}` of `IsSymmetricEvent` are cubic phases.

For data `φ·b`:
- `𝒥_𝒯`, `𝒥_N`, `a^tr`, `∂_t𝒥_𝒯`, `∂_t a^tr`, `∂_tℒ₀` and `ℒ₀` are multiplied by `φ(n)`;
- hence their moduli are unchanged.

The proof is by induction on the tree through the Duhamel recursion `treeTerm_node` (SysDraft, O-TR1). The
cubic step is `aNonlin_mul_phase3`; INDUCT's `aNonlin_mul_phase` (`../induct/SolutionPhase.lean`) is its case
`f = g = h`.
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.Fixedpt

open MeasureTheory Set SysAPI

variable (L γ δ : ℝ) {d : ℕ}

/-- A unit phase with the cubic momentum character. -/
structure IsCubicPhase (φ : (Fin d → ℤ) → ℂ) : Prop where
  norm_eq : ∀ n, ‖φ n‖ = 1
  rel : ∀ n q₁ q₂, φ q₁ * (starRingEnd ℂ) (φ q₂) * φ (n - q₁ + q₂) = φ n

/-! ## The two families of `IsSymmetricEvent` -/

theorem conj_exp_ofReal_mul_I (y : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((y : ℂ) * Complex.I)) = Complex.exp (((-y : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem isCubicPhase_gauge (θ : ℝ) :
    IsCubicPhase (fun _ : Fin d → ℤ => Complex.exp ((θ : ℂ) * Complex.I)) := by
  refine ⟨fun _ => Complex.norm_exp_ofReal_mul_I θ, fun n q₁ q₂ => ?_⟩
  have hn := Complex.norm_exp_ofReal_mul_I θ
  rw [Complex.mul_conj', hn]
  simp

theorem latticePoint_sub_add' (n q₁ q₂ : Fin d → ℤ) :
    latticePoint L (n - q₁ + q₂) = latticePoint L n - latticePoint L q₁ + latticePoint L q₂ := by
  ext j
  simp [latticePoint]
  ring

/-- The translation phase, written as in `IsSymmetricEvent`. -/
theorem isCubicPhase_translation (x₀ : Mom d) :
    IsCubicPhase (fun n : Fin d → ℤ =>
      Complex.exp (-(2 * Real.pi * inner ℝ (latticePoint L n) x₀ : ℝ) * Complex.I)) := by
  have hform : ∀ n : Fin d → ℤ, Complex.exp (-(2 * Real.pi * inner ℝ (latticePoint L n) x₀ : ℝ) * Complex.I) =
      Complex.exp (((-(2 * Real.pi * inner ℝ (latticePoint L n) x₀)) : ℝ) * Complex.I) := fun n => by
    push_cast; ring_nf
  refine ⟨fun n => by rw [hform]; exact Complex.norm_exp_ofReal_mul_I _, fun n q₁ q₂ => ?_⟩
  simp only [hform]
  rw [conj_exp_ofReal_mul_I, ← Complex.exp_add, ← Complex.exp_add, latticePoint_sub_add', inner_add_left,
    inner_sub_left]
  congr 1
  push_cast
  ring

/-! ## The cubic step -/

theorem aNonlin_mul_phase3 {φ : (Fin d → ℤ) → ℂ} (hφ : IsCubicPhase φ) (t : ℝ) (f g h : (Fin d → ℤ) → ℂ)
    (n : Fin d → ℤ) :
    aNonlin L γ δ 1 t (fun k => φ k * f k) (fun k => (starRingEnd ℂ) (φ k * g k)) (fun k => φ k * h k) n =
      φ n * aNonlin L γ δ 1 t f (fun k => (starRingEnd ℂ) (g k)) h n := by
  rw [aNonlin_eq_tsum_pairs, aNonlin_eq_tsum_pairs]
  have he (q : (Fin d → ℤ) × (Fin d → ℤ)) (E : ℂ) :
      E * (φ q.1 * f q.1) * (starRingEnd ℂ) (φ q.2 * g q.2) * (φ (n - q.1 + q.2) * h (n - q.1 + q.2)) =
      φ n * (E * f q.1 * (starRingEnd ℂ) (g q.2) * h (n - q.1 + q.2)) := by
    rw [map_mul]
    calc _ = (φ q.1 * (starRingEnd ℂ) (φ q.2) * φ (n - q.1 + q.2)) *
          (E * f q.1 * (starRingEnd ℂ) (g q.2) * h (n - q.1 + q.2)) := by ring
      _ = _ := by rw [hφ.rel]
  simp_rw [he]
  rw [tsum_mul_left]
  ring

/-! ## Tree terms -/

section Trees

variable {φ : (Fin d → ℤ) → ℂ} (hφ : IsCubicPhase φ) (p : ℕ) {b : (Fin d → ℤ) → ℂ}
  (hb : Summable fun k => ‖b k‖)

include hφ in
theorem summable_mul_phase : (Summable fun k => ‖φ k * b k‖) ↔ Summable fun k => ‖b k‖ := by
  simp only [norm_mul, hφ.norm_eq, one_mul]

include hφ hb in
theorem treeTerm_mul_phase :
    ∀ (S : TTree) (t : ℝ) (n : Fin d → ℤ),
      treeTerm L γ δ p S (fun k => φ k * b k) t n = φ n * treeTerm L γ δ p S b t n
  | .leaf, t, n => by rw [treeTerm_leaf, treeTerm_leaf]
  | .node l m r, t, n => by
    have hb' : Summable fun k => ‖φ k * b k‖ := (summable_mul_phase hφ).2 hb
    rcases le_or_gt (p : ℝ) t with ht | ht
    · rw [treeTerm_node l m r L γ δ p hb' ht, treeTerm_node l m r L γ δ p hb ht,
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      have el : treeTerm L γ δ p l (fun k => φ k * b k) s = fun k => φ k * treeTerm L γ δ p l b s k :=
        funext fun k => treeTerm_mul_phase l s k
      have em : treeTerm L γ δ p m (fun k => φ k * b k) s = fun k => φ k * treeTerm L γ δ p m b s k :=
        funext fun k => treeTerm_mul_phase m s k
      have er : treeTerm L γ δ p r (fun k => φ k * b k) s = fun k => φ k * treeTerm L γ δ p r b s k :=
        funext fun k => treeTerm_mul_phase r s k
      simp only [el, em, er]
      exact aNonlin_mul_phase3 L γ δ hφ s _ _ _ n
    · rw [treeTerm_of_le L γ δ p (by simp) _ ht.le, treeTerm_of_le L γ δ p (by simp) _ ht.le, mul_zero]

include hφ hb in
theorem treeTermN_mul_phase (N : ℕ) (t : ℝ) (n : Fin d → ℤ) :
    treeTermN L γ δ p N (fun k => φ k * b k) t n = φ n * treeTermN L γ δ p N b t n := by
  rw [treeTermN_eq_sum, treeTermN_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => treeTerm_mul_phase L γ δ hφ p hb S t n

include hφ hb in
theorem aTr_mul_phase (Ntr : ℕ) (t : ℝ) (n : Fin d → ℤ) :
    aTr L γ δ p Ntr (fun k => φ k * b k) t n = φ n * aTr L γ δ p Ntr b t n := by
  unfold aTr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun N _ => treeTermN_mul_phase L γ δ hφ p hb N t n

include hφ hb in
theorem slotValAt_mul_phase (Ntr : ℕ) (o : Slot Ntr) (t : ℝ) :
    slotValAt L γ δ p Ntr (fun k => φ k * b k) o t = fun k => φ k * slotValAt L γ δ p Ntr b o t k := by
  funext k
  cases o with
  | none => simp [slotValAt]
  | some N => exact treeTermN_mul_phase L γ δ hφ p hb N t k

include hφ hb in
theorem L0Dt_mul_phase (Ntr : ℕ) (t : ℝ) (n : Fin d → ℤ) :
    L0Dt L γ δ p Ntr (fun k => φ k * b k) t n = φ n * L0Dt L γ δ p Ntr b t n := by
  unfold L0Dt
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [slotValAt_mul_phase L γ δ hφ p hb]
  exact aNonlin_mul_phase3 L γ δ hφ t _ _ _ n

include hφ hb in
theorem Lop0_mul_phase (hL : 0 < L) (Ntr : ℕ) (b₀ b₀' : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) (t : ℝ)
    (n : Fin d → ℤ) :
    Lop L γ δ p Ntr (fun k => φ k * b k) 0 b₀ t n = φ n * Lop L γ δ p Ntr b 0 b₀' t n := by
  rw [L0_eq L γ δ hL p Ntr ((summable_mul_phase hφ).2 hb) b₀ t n, L0_eq L γ δ hL p Ntr hb b₀' t n,
    ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun s _ => L0Dt_mul_phase L γ δ hφ p hb Ntr s n

end Trees

end WaveTurbulence.Fixedpt
