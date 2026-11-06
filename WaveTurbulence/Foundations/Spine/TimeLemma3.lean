/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.TimeLemma2
import Mathlib.Tactic
/-! Head/tail splitting, local modifications and one-variable oscillatory integrals. -/
@[expose] public section
open MeasureTheory Set Finset Function
namespace WaveTurbulence.Ladder

/-- The unimodular phase `e^{iβx}`. -/
noncomputable def ee (β x : ℝ) : ℂ := Complex.exp (((β * x : ℝ) : ℂ) * Complex.I)

theorem norm_ee (β x : ℝ) : ‖ee β x‖ = 1 := by unfold ee; exact Complex.norm_exp_ofReal_mul_I _

theorem ee_mul (a b x : ℝ) : ee a x * ee b x = ee (a + b) x := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem Fd_cons {n : ℕ} (par : Par (n + 1)) (hpar : ParOK par) (l u β : Fin (n + 1) → ℝ)
    (s : ℝ) (t' : Fin n → ℝ) :
    Fd par l u β (Fin.cons s t' : Fin (n + 1) → ℝ) =
      Gf par l u β 0 (Fin.cons s t' : Fin (n + 1) → ℝ) *
        Fd (parTail par) (fun v => l v.succ) (fun v => u v.succ) (fun v => β v.succ) t' := by
  unfold Fd
  rw [Fin.prod_univ_succ]
  congr 1
  refine Finset.prod_congr rfl (fun v _ => ?_)
  unfold Gf
  simp only [Fin.cons_succ]
  rcases hp : par v.succ with _ | w
  · simp [parTail, hp]
  · have hlt := hpar _ _ hp
    have hw : w ≠ 0 := fun h => by subst h; exact absurd hlt (not_lt.mpr (Fin.zero_le _))
    obtain ⟨w', rfl⟩ := Fin.exists_succ_eq.mpr hw
    simp [parTail, hp, Fin.cons_succ]

theorem Fd_mod {n : ℕ} (par : Par n) (l u β : Fin n → ℝ) (p : Fin n) (lo hi b : ℝ)
    (t : Fin n → ℝ) :
    Fd par l u β t * ((if t p ∈ Ioc lo hi then (1 : ℂ) else 0) * ee b (t p)) =
      Fd par (update l p (max (l p) lo)) (update u p (min (u p) hi)) (update β p (β p + b)) t := by
  unfold Fd
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ p),
    ← Finset.mul_prod_erase univ (fun v => Gf par (update l p (max (l p) lo)) (update u p (min (u p) hi))
      (update β p (β p + b)) v t) (Finset.mem_univ p)]
  have hrest : ∏ v ∈ univ.erase p, Gf par (update l p (max (l p) lo)) (update u p (min (u p) hi))
      (update β p (β p + b)) v t = ∏ v ∈ univ.erase p, Gf par l u β v t := by
    refine Finset.prod_congr rfl (fun v hv => ?_)
    have : v ≠ p := Finset.ne_of_mem_erase hv
    simp [Gf, update_of_ne this]
  rw [hrest]
  have hp : Gf par l u β p t * ((if t p ∈ Ioc lo hi then (1 : ℂ) else 0) * ee b (t p)) =
      Gf par (update l p (max (l p) lo)) (update u p (min (u p) hi)) (update β p (β p + b)) p t := by
    unfold Gf
    simp only [update_self]
    have hee : Complex.exp (((β p * t p : ℝ) : ℂ) * Complex.I) * ee b (t p) =
        Complex.exp ((((β p + b) * t p : ℝ) : ℂ) * Complex.I) := ee_mul (β p) b (t p)
    have hmem : (t p ∈ Ioc (max (l p) lo) (min (u p) hi)) ↔
        (t p ∈ Ioc (l p) (u p) ∧ t p ∈ Ioc lo hi) := by
      simp only [Set.mem_Ioc, max_lt_iff, le_min_iff]; tauto
    rw [← hee]
    by_cases h1 : t p ∈ Ioc (l p) (u p) <;> by_cases h2 : t p ∈ Ioc lo hi <;>
      simp [hmem, h1, h2]; ring
  rw [← hp]; ring

/-- `E(x) = e^{iβx}/(iβ)` primitive. -/
theorem integral_ee_Ioc {β : ℝ} (hβ : β ≠ 0) {l m : ℝ} (hlm : l ≤ m) :
    ∫ s : ℝ, (if s ∈ Ioc l m then (1 : ℂ) else 0) * ee β s =
      (ee β m - ee β l) / ((β : ℂ) * Complex.I) := by
  have h1 : ∀ s : ℝ, (if s ∈ Ioc l m then (1 : ℂ) else 0) * ee β s =
      (Ioc l m).indicator (fun s => ee β s) s := by
    intro s; by_cases h : s ∈ Ioc l m <;> simp [h]
  simp_rw [h1]
  rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hlm]
  have hc : ((β : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by exact_mod_cast hβ) Complex.I_ne_zero
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => ee β x / ((β : ℂ) * Complex.I)) (ee β x) x := by
    intro x
    have h0 : HasDerivAt (fun x : ℝ => β * x) β x := by
      simpa using HasDerivAt.const_mul β (hasDerivAt_id x)
    have h1 := HasDerivAt.cexp (HasDerivAt.mul_const (HasDerivAt.ofReal_comp h0) Complex.I)
    have h2 := HasDerivAt.div_const h1 ((β : ℂ) * Complex.I)
    have h3 : (fun x : ℝ => ee β x / ((β : ℂ) * Complex.I)) =
        fun x : ℝ => Complex.exp (((β * x : ℝ) : ℂ) * Complex.I) / ((β : ℂ) * Complex.I) := rfl
    rw [h3]
    convert h2 using 1
    unfold ee
    rw [mul_div_assoc, div_self hc, mul_one]
  have hcont : Continuous (ee β) := by unfold ee; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hcont.intervalIntegrable _ _)]
  ring

theorem norm_integral_ee_Ioc_le {β l u : ℝ} (hlu : u - l ≤ 1) :
    ‖∫ s : ℝ, (if s ∈ Ioc l u then (1 : ℂ) else 0) * ee β s‖ ≤ 3 / br β := by
  have hb := br_pos β
  by_cases hβ : |β| < 1
  · have h1 : ‖∫ s : ℝ, (if s ∈ Ioc l u then (1 : ℂ) else 0) * ee β s‖ ≤ 1 := by
      have h1 : ∀ s : ℝ, (if s ∈ Ioc l u then (1 : ℂ) else 0) * ee β s =
          (Ioc l u).indicator (fun s => ee β s) s := by
        intro s; by_cases h : s ∈ Ioc l u <;> simp [h]
      simp_rw [h1]
      rw [integral_indicator measurableSet_Ioc]
      calc _ ≤ ∫ s in Ioc l u, ‖ee β s‖ := norm_integral_le_integral_norm _
        _ = ∫ s in Ioc l u, (1 : ℝ) := by simp_rw [norm_ee]
        _ ≤ 1 := by
          rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Ioc]
          rcases le_or_gt l u with h | h
          · rw [ENNReal.toReal_ofReal (by linarith)]; linarith
          · rw [ENNReal.ofReal_of_nonpos (by linarith)]; simp
    have := br_le_of_abs_lt_one hβ
    rw [le_div_iff₀ hb]; nlinarith
  · push Not at hβ
    rcases le_or_gt l u with hle | hlt
    · have hβ0 : β ≠ 0 := by intro h; subst h; simp at hβ; linarith
      rw [integral_ee_Ioc hβ0 hle]
      have hn : ‖(ee β u - ee β l) / ((β : ℂ) * Complex.I)‖ ≤ 2 / |β| := by
        rw [norm_div]
        have : ‖(β : ℂ) * Complex.I‖ = |β| := by simp
        rw [this]
        gcongr
        calc ‖ee β u - ee β l‖ ≤ ‖ee β u‖ + ‖ee β l‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_ee, norm_ee]; norm_num
      refine hn.trans ?_
      have hsq : br β ^ 2 ≤ 2 * β ^ 2 := by
        unfold br; rw [Real.sq_sqrt (by positivity)]; nlinarith [sq_abs β]
      rw [div_le_div_iff₀ (by linarith) hb]
      nlinarith [sq_abs β, abs_nonneg β]
    · have : (∫ s : ℝ, (if s ∈ Ioc l u then (1 : ℂ) else 0) * ee β s) = 0 := by
        have : ∀ s : ℝ, (if s ∈ Ioc l u then (1 : ℂ) else 0) * ee β s = 0 := by
          intro s
          have : s ∉ Ioc l u := by
            rw [Set.mem_Ioc]; rintro ⟨h1, h2⟩; linarith
          simp [this]
        simp only [this, integral_zero]
      rw [this]; simp; positivity

end WaveTurbulence.Ladder
