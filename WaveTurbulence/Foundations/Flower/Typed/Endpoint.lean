/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Typed.Core3
public import WaveTurbulence.Foundations.Flower.Typed.Defs
public import WaveTurbulence.Foundations.Flower.Typed.Radial
/-! # FL-TYPED: each endpoint factor is `u + z v` with the jets required by the profile estimate. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.Typed
open WaveTurbulence.NormBridgeScratch Finset

variable {d : ℕ}

/-- The unit jet constants: `1` at order `0` and `0` above. -/
def γ1 (k : ℕ) : ℝ := if k = 0 then 1 else 0

/-- The `v`-jet constants. -/
def Γvf (γ : ℕ → ℝ) (k : ℕ) : ℝ := mulγ γ (fun k => γ1 k + γ k) k + 2 * γ k + γ1 k

theorem γ1_nonneg (k : ℕ) : 0 ≤ γ1 k := by unfold γ1; split_ifs <;> norm_num

theorem Γvf_nonneg {γ : ℕ → ℝ} (h : ∀ k, 0 ≤ γ k) (k : ℕ) : 0 ≤ Γvf γ k := by
  unfold Γvf
  have := mulγ_nonneg h (fun k => add_nonneg (γ1_nonneg k) (h k)) k
  have := γ1_nonneg k
  have := h k
  linarith

/-- The data of one endpoint factor. -/
theorem endpoint_data (m : ℕ) {γ : ℕ → ℝ} (hγ : ∀ k, 0 ≤ γ k) (hγ0 : γ 0 = 1)
    (hj : ∀ s : ℝ, 0 < s → JetW m (fun k _ => γ k * (s⁻¹) ^ k)
      (fun x : Mom d => ((Rc s x : ℝ) : ℂ)))
    (p q : ℕ) (tail : Bool) {A M : ℝ} (hA : 1 ≤ A) (h2A : 2 * A ≤ M) :
    ∃ u v : Mom d → ℂ, ContDiff ℝ (m : WithTop ℕ∞) u ∧ ContDiff ℝ (m : WithTop ℕ∞) v ∧
      JetW m (fun k _ => γ k * (2 / M) ^ k) u ∧ JetW m (fun k _ => Γvf γ k * (1 / A) ^ k) v ∧
      (∀ y, ‖y‖ < A / 2 → v y = 0) ∧
      ∀ (z : ℝ) (y : Mom d), ((FC23.endpointFactor p q tail M A z ‖y‖ : ℝ) : ℂ) = u y + (z : ℂ) * v y := by
  have hA0 : 0 < A := by linarith
  have hM0 : 0 < M := by linarith
  have hM2 : 0 < M / 2 := by positivity
  have hτ01 : 2 / M ≤ 1 / A := by rw [div_le_div_iff₀ hM0 hA0]; linarith
  have hτ0 : 0 ≤ 2 / M := by positivity
  have hτM : 1 / M ≤ 1 / A := by rw [div_le_div_iff₀ hM0 hA0]; linarith
  have hτM0 : 0 ≤ 1 / M := by positivity
  have hτ1 : 0 ≤ 1 / A := by positivity
  -- the radial pieces
  have cA : ContDiff ℝ (m : WithTop ℕ∞) (fun x : Mom d => ((Rc A x : ℝ) : ℂ)) :=
    (Rc_contDiff hA0).of_le (by exact_mod_cast le_top)
  have cM : ContDiff ℝ (m : WithTop ℕ∞) (fun x : Mom d => ((Rc M x : ℝ) : ℂ)) :=
    (Rc_contDiff hM0).of_le (by exact_mod_cast le_top)
  have ca : ContDiff ℝ (m : WithTop ℕ∞) (fun x : Mom d => ((Rc (M / 2) x : ℝ) : ℂ)) :=
    (Rc_contDiff hM2).of_le (by exact_mod_cast le_top)
  have jA : JetW m (fun k _ => γ k * (1 / A) ^ k) (fun x : Mom d => ((Rc A x : ℝ) : ℂ)) := by
    simpa [one_div] using hj A hA0
  have ja : JetW m (fun k _ => γ k * (2 / M) ^ k) (fun x : Mom d => ((Rc (M / 2) x : ℝ) : ℂ)) := by
    simpa [inv_div] using hj (M / 2) hM2
  have ja1 : JetW m (fun k _ => γ k * (1 / A) ^ k) (fun x : Mom d => ((Rc (M / 2) x : ℝ) : ℂ)) :=
    ja.tau_mono hγ hτ0 hτ01
  have jM : JetW m (fun k _ => γ k * (1 / M) ^ k) (fun x : Mom d => ((Rc M x : ℝ) : ℂ)) := by
    simpa [one_div] using hj M hM0
  have jM1 : JetW m (fun k _ => γ k * (1 / A) ^ k) (fun x : Mom d => ((Rc M x : ℝ) : ℂ)) :=
    jM.tau_mono hγ hτM0 hτM
  -- the constant one
  have c1 : ContDiff ℝ (m : WithTop ℕ∞) (fun _ : Mom d => (1 : ℂ)) := contDiff_const
  have j1 : JetW m (fun k _ => γ k * (2 / M) ^ k) (fun _ : Mom d => (1 : ℂ)) := by
    refine (JetW.const m (1 : ℂ)).mono fun k x => ?_
    by_cases h : k = 0
    · subst h; simp [hγ0]
    · simp only [h, ite_false]; exact mul_nonneg (hγ k) (pow_nonneg hτ0 _)
  -- one minus b
  have j1b : JetW m (fun k _ => (γ1 k + γ k) * (1 / A) ^ k)
      (fun y : Mom d => (1 : ℂ) + (-1 : ℂ) * ((Rc A y : ℝ) : ℂ)) := by
    refine (JetW.add c1 (contDiff_const.mul cA) (JetW.const m (1 : ℂ))
      (JetW.const_mul (-1 : ℂ) cA jA)).mono fun k x => ?_
    simp only [γ1, norm_neg, norm_one, one_mul]
    by_cases h : k = 0
    · subst h; simp [hγ0]
    · simp only [h, ite_false]; nlinarith [hγ k, pow_nonneg hτ1 k]
  have c1b : ContDiff ℝ (m : WithTop ℕ∞) (fun y : Mom d => (1 : ℂ) + (-1 : ℂ) * ((Rc A y : ℝ) : ℂ)) :=
    c1.add (contDiff_const.mul cA)
  have van1b : ∀ y : Mom d, ‖y‖ < A / 2 → (1 : ℂ) + (-1 : ℂ) * ((Rc A y : ℝ) : ℂ) = 0 := by
    intro y hy
    rw [Rc_eq_one hA0 hy.le]; simp
  have hmn : ∀ k, mulγ γ (fun k => γ1 k + γ k) k ≥ 0 :=
    fun k => mulγ_nonneg hγ (fun k => add_nonneg (γ1_nonneg k) (hγ k)) k
  have hΓ1 : ∀ k, γ1 k + γ k ≤ Γvf γ k := fun k => by
    unfold Γvf; have := hmn k; have := hγ k; have := γ1_nonneg k; linarith
  have hΓ2 : ∀ k, mulγ γ (fun k => γ1 k + γ k) k ≤ Γvf γ k := fun k => by
    unfold Γvf; have := hγ k; have := γ1_nonneg k; linarith
  have hΓ3 : ∀ k, 2 * γ k ≤ Γvf γ k := fun k => by
    unfold Γvf; have := hmn k; have := γ1_nonneg k; linarith
  have hp1 : ∀ k, 0 ≤ (1 / A) ^ k := fun k => pow_nonneg hτ1 k
  have hvan_a : ∀ y : Mom d, ‖y‖ < A / 2 → ((Rc (M / 2) y : ℝ) : ℂ) = 1 := by
    intro y hy; rw [Rc_eq_one hM2 (by linarith)]; simp
  have hvan_c : ∀ y : Mom d, ‖y‖ < A / 2 → ((Rc M y : ℝ) : ℂ) = 1 := by
    intro y hy; rw [Rc_eq_one hM0 (by linarith)]; simp
  cases tail
  · by_cases hq : q = p
    · refine ⟨fun y => ((Rc (M / 2) y : ℝ) : ℂ), fun y => ((Rc M y : ℝ) : ℂ) + (-1 : ℂ) * ((Rc (M / 2) y : ℝ) : ℂ),
        ca, cM.add (contDiff_const.mul ca), ja, ?_, ?_, ?_⟩
      · refine (JetW.add cM (contDiff_const.mul ca) jM1 (JetW.const_mul (-1 : ℂ) ca ja1)).mono
          fun k x => ?_
        simp only [norm_neg, norm_one, one_mul]
        nlinarith [hΓ3 k, hp1 k]
      · intro y hy; beta_reduce; rw [hvan_c y hy, hvan_a y hy]; simp
      · intro z y
        simp only [FC23.endpointFactor, hq, if_true, Bool.false_eq_true, if_false]
        simp only [Rc]
        push_cast; ring
    · refine ⟨fun _ => (1 : ℂ), fun _ => (0 : ℂ), c1, contDiff_const, j1, ?_, fun _ _ => rfl, ?_⟩
      · exact (JetW.zero m).mono fun k x => mul_nonneg (Γvf_nonneg hγ k) (hp1 k) |> fun h => by simpa using h
      · intro z y
        simp [FC23.endpointFactor, hq]
  · by_cases hq : q = p
    · refine ⟨fun y => ((Rc (M / 2) y : ℝ) : ℂ),
        fun y => ((Rc (M / 2) y : ℝ) : ℂ) * ((1 : ℂ) + (-1 : ℂ) * ((Rc A y : ℝ) : ℂ)),
        ca, ca.mul c1b, ja, ?_, ?_, ?_⟩
      · exact (jetMulγ ca c1b ja1 j1b).mono fun k x => by
          exact mul_le_mul_of_nonneg_right (hΓ2 k) (hp1 k)
      · intro y hy; beta_reduce; rw [van1b y hy, mul_zero]
      · intro z y
        simp only [FC23.endpointFactor, hq, if_true]
        simp only [Rc]
        push_cast; ring
    · refine ⟨fun _ => (1 : ℂ), fun y => (1 : ℂ) + (-1 : ℂ) * ((Rc A y : ℝ) : ℂ), c1, c1b, j1, ?_,
        van1b, ?_⟩
      · exact j1b.mono fun k x => mul_le_mul_of_nonneg_right (hΓ1 k) (hp1 k)
      · intro z y
        simp only [FC23.endpointFactor, hq, if_false]
        simp only [Rc]
        push_cast; ring


end WaveTurbulence.Flower.Typed
