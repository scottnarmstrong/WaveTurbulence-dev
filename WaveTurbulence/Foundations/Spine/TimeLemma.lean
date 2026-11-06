/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
/-! # Forest-ordered oscillatory time integrals (DH21 Lemma 10.2, L2432–L2451; DH19 Prop 2.3)
Pointwise bound `‖∫_{Ω} ∏ e^{iβ_v t_v}‖ ≤ 3^n B(β)` for a forest-ordered domain, where `B` is defined by
the leaf-absorption recursion (equivalent to `∑_d ∏ ⟨q_v⟩⁻¹`). Vertices `Fin n`, parents have larger
index. Orders are strict. -/
@[expose] public section
open MeasureTheory Set Finset
namespace WaveTurbulence.Ladder

/-- The Japanese bracket `⟨x⟩ = √(1+x²)`. -/
noncomputable def br (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2)

theorem br_pos (x : ℝ) : 0 < br x := Real.sqrt_pos.mpr (by positivity)
theorem one_le_br (x : ℝ) : 1 ≤ br x := by
  unfold br
  calc (1:ℝ) = Real.sqrt 1 := by simp
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
theorem br_le_of_abs_lt_one {x : ℝ} (h : |x| < 1) : br x ≤ 2 := by
  unfold br; rw [Real.sqrt_le_left (by norm_num)]; nlinarith [sq_abs x, abs_nonneg x]
theorem br_le_mul_abs {x : ℝ} (h : 1 ≤ |x|) : br x ≤ 2 * |x| := by
  unfold br; rw [Real.sqrt_le_left (by positivity)]; nlinarith [sq_abs x]

abbrev Par (n : ℕ) := Fin n → Option (Fin n)
def ParOK {n : ℕ} (par : Par n) : Prop := ∀ v w, par v = some w → v < w

/-- Parent function of the forest with vertex `0` removed. -/
def parTail {n : ℕ} (par : Par (n + 1)) : Par n := fun v =>
  (par v.succ).bind (fun w => if h : w = 0 then none else some (w.pred h))

/-- Frequencies of the forest with the leaf `0` absorbed into its parent (`d = true`) or dropped. -/
def absorb {n : ℕ} (par : Par (n + 1)) (β : Fin (n + 1) → ℝ) (d : Bool) : Fin n → ℝ :=
  fun v => β v.succ + if d = true ∧ par 0 = some v.succ then β 0 else 0

/-- The bound `∑_d ∏ ⟨q_v⟩⁻¹`, by leaf absorption. -/
noncomputable def Bd : (n : ℕ) → Par n → (Fin n → ℝ) → ℝ
  | 0, _, _ => 1
  | n + 1, par, β => (br (β 0))⁻¹ *
      (Bd n (parTail par) (absorb par β false) + Bd n (parTail par) (absorb par β true))

theorem Bd_nonneg : ∀ (n : ℕ) (par : Par n) (β : Fin n → ℝ), 0 ≤ Bd n par β
  | 0, _, _ => by simp [Bd]
  | n + 1, par, β => by
      simp only [Bd]
      have := Bd_nonneg n (parTail par) (absorb par β false)
      have := Bd_nonneg n (parTail par) (absorb par β true)
      have := br_pos (β 0)
      positivity

/-- One factor of the integrand. -/
noncomputable def Gf {n : ℕ} (par : Par n) (l u β : Fin n → ℝ) (v : Fin n) (t : Fin n → ℝ) : ℂ :=
  (if t v ∈ Ioc (l v) (u v) then (1 : ℂ) else 0) *
  (match par v with | none => (1 : ℂ) | some w => if t v < t w then 1 else 0) *
  Complex.exp (((β v * t v : ℝ) : ℂ) * Complex.I)

noncomputable def Fd {n : ℕ} (par : Par n) (l u β : Fin n → ℝ) (t : Fin n → ℝ) : ℂ :=
  ∏ v, Gf par l u β v t

noncomputable def Uint {n : ℕ} (par : Par n) (l u β : Fin n → ℝ) : ℂ :=
  ∫ t : Fin n → ℝ, Fd par l u β t

theorem norm_Gf_le {n : ℕ} (par : Par n) (l u β : Fin n → ℝ) (v : Fin n) (t : Fin n → ℝ) :
    ‖Gf par l u β v t‖ ≤ 1 := by
  unfold Gf
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have h1 : ‖(if t v ∈ Ioc (l v) (u v) then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
  have h2 : ‖(match par v with | none => (1 : ℂ) | some w => if t v < t w then 1 else 0)‖ ≤ 1 := by
    rcases par v with _ | w
    · simp
    · simp only; split_ifs <;> simp
  nlinarith [norm_nonneg (if t v ∈ Ioc (l v) (u v) then (1 : ℂ) else 0),
    norm_nonneg (match par v with | none => (1 : ℂ) | some w => if t v < t w then 1 else 0)]

theorem measurable_Gf {n : ℕ} (par : Par n) (l u β : Fin n → ℝ) (v : Fin n) :
    Measurable (Gf par l u β v) := by
  unfold Gf
  refine (Measurable.mul (Measurable.mul ?_ ?_) ?_)
  · exact Measurable.ite (measurableSet_Ioc.preimage (measurable_pi_apply v)) measurable_const measurable_const
  · rcases hp : par v with _ | w
    · simp only; exact measurable_const
    · simp only
      exact Measurable.ite (measurableSet_lt (measurable_pi_apply v) (measurable_pi_apply w))
        measurable_const measurable_const
  · fun_prop

theorem measurable_Fd {n : ℕ} (par : Par n) (l u β : Fin n → ℝ) : Measurable (Fd par l u β) := by
  unfold Fd
  exact Finset.measurable_prod _ (fun v _ => measurable_Gf par l u β v)

end WaveTurbulence.Ladder
