/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Bridge
public import WaveTurbulence.Foundations.Layered.Telescope

/-!
# Telescoping with derivatives (PL23-30D)

The derivative analogs of `Layered.restr_step`, `Layered.restr_top`, `Layered.restr_trace_transport`, for the norms
`rN θ Λ Λ₂ ℬ F = 𝔛^{θ,Λ,Λ₂}(ℬ)` (all momenta), with the Leibniz constant `cLeib d Λ`:

* `rN_trace_transport`: a trace at `u_j = c` of the unit box, carried to a target box by translations;
* `restr_mul_s_le`: a momentum multiplier `c(k)`, bounded in `𝔖^{Λ,0}`;
* `restr_step30`: one factor constant in time: `W(cK − aA) = (c−a)(K−A) + (c−a)A + a(K−A)`;
* `restr_top30`: a time-dependent factor, by the product estimate;
* `rN_const_param_le`: a `k`-independent time function.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace WaveTurbulence.PL2330

open WaveTurbulence.Fourier WaveTurbulence.Regref

variable {r d : ℕ}

theorem contDiff_of_spatialNorm_lt_top {Λ Λ₂ : ℕ} (hΛ : Λ ≠ 0) {c : Mom d → ℂ}
    (h : spatialNorm Λ Λ₂ c < ⊤) : ContDiff ℝ Λ c := by
  by_contra hc
  unfold spatialNorm at h
  simp [hΛ, hc] at h

/-- **A trace at `u_j = c` of the unit box, carried to a target box.** -/
theorem rN_trace_transport {θ : ℝ} {Λ Λ₂ : ℕ} (hΛ : Λ ≠ 0) (hθ : 0 ≤ θ) {B T' : Set (Fin r → ℝ)}
    (h : (Fin r → ℝ) → Mom d → ℂ) (hh : ∀ k, Continuous fun t => h t k) (a b : Fin r → ℝ)
    (j : Fin r) (c : ℝ) (hT' : ∀ t ∈ T', t + b ∈ (Layered.unitBox : Set (Fin r → ℝ)))
    (hline : ∀ u ∈ (Layered.unitBox : Set (Fin r → ℝ)), Function.update u j c + a ∈ closure (interior B)) :
    rN θ Λ Λ₂ T' (fun t k => h (Function.update (t + b) j c + a) k) ≤
      traceConst (r := r) θ Layered.chiUnit * rN θ Λ Λ₂ B h := by
  set B₀ : Set (Fin r → ℝ) := (fun t => t + a) ⁻¹' B with hB₀
  have h1 := rN_translate_le (θ := θ) (Λ := Λ) (Λ₂ := Λ₂) (B := T') (B' := Layered.unitBox)
    (fun u k => h (Function.update u j c + a) k) b hT'
  have hcl : ∀ u ∈ (Layered.unitBox : Set (Fin r → ℝ)), Function.update u j c ∈ closure (interior B₀) := by
    intro u hu
    have e : closure (interior B₀) = (fun t => t + a) ⁻¹' closure (interior B) := by
      show closure (interior ((Homeomorph.addRight a) ⁻¹' B)) =
        (Homeomorph.addRight a) ⁻¹' closure (interior B)
      rw [← Homeomorph.preimage_interior, ← Homeomorph.preimage_closure]
    rw [e]
    exact hline u hu
  have hc' : ∀ k, Continuous fun t => h (t + a) k := fun k =>
    (hh k).comp (continuous_id.add continuous_const)
  have h2 := rN_trace_le_w (Λ₂ := Λ₂) hΛ hθ Layered.chiUnit_contDiff Layered.chiUnit_hasCompactSupport
    (B := B₀) (T := Layered.unitBox) (fun t k => h (t + a) k) hc' j c hcl
    (fun u hu => Layered.coordinateCutoff_chiUnit_eq_one hu)
  have h3 := rN_translate_le (θ := θ) (Λ := Λ) (Λ₂ := Λ₂) (B := B₀) (B' := B) h a (fun t ht => ht)
  exact h1.trans (h2.trans (mul_le_mul_right h3 _))

/-- A momentum multiplier bounded in `𝔖^{Λ,0}`. -/
theorem restr_mul_s_le {Λ : ℕ} (hΛ : Λ ≠ 0) (hd : 1 ≤ d) {θ : ℝ} (b : ℕ) (B : Set (Fin r → ℝ))
    {c : Mom d → ℂ} (F : (Fin r → ℝ) → Mom d → ℂ) {S e : ℝ} (hS0 : 0 ≤ S)
    (hS : spatialNorm Λ 0 c ≤ ENNReal.ofReal S)
    (hF : rN θ Λ b B F ≤ ENNReal.ofReal e) :
    rN θ Λ b B (fun t k => c k * F t k) ≤ ENNReal.ofReal (cLeib d Λ * S * e) := by
  have hc := contDiff_of_spatialNorm_lt_top hΛ (hS.trans_lt ENNReal.ofReal_lt_top)
  have := restr_mul_momentum_le (θ := θ) hΛ hd 0 b B Set.univ hc F hS0 hS hF
  rwa [zero_add] at this

/-- A momentum multiplier with a weight, bounded in `𝔖^{Λ,a}`, times a function with no weight. -/
theorem restr_mul_w_le {Λ : ℕ} (hΛ : Λ ≠ 0) (hd : 1 ≤ d) {θ : ℝ} (a : ℕ) (B : Set (Fin r → ℝ))
    {c : Mom d → ℂ} (F : (Fin r → ℝ) → Mom d → ℂ) {S e : ℝ} (hS0 : 0 ≤ S)
    (hS : spatialNorm Λ a c ≤ ENNReal.ofReal S)
    (hF : rN θ Λ 0 B F ≤ ENNReal.ofReal e) :
    rN θ Λ a B (fun t k => c k * F t k) ≤ ENNReal.ofReal (cLeib d Λ * S * e) := by
  have hc := contDiff_of_spatialNorm_lt_top hΛ (hS.trans_lt ENNReal.ofReal_lt_top)
  have := restr_mul_momentum_le (θ := θ) hΛ hd a 0 B Set.univ hc F hS0 hS hF
  rwa [add_zero] at this

section Step

variable {θ : ℝ} {Λ : ℕ}

/-- **One constant-in-time factor.** -/
theorem restr_step30 (hΛ : Λ ≠ 0) (hd : 1 ≤ d) (a₀ : ℕ) (B : Set (Fin r → ℝ)) (c a : Mom d → ℂ)
    (K₂ A₂ : (Fin r → ℝ) → Mom d → ℂ) {ε α E α₂ : ℝ} (hε : 0 ≤ ε) (hα : 0 ≤ α) (hE : 0 ≤ E)
    (hα₂ : 0 ≤ α₂) (hca : spatialNorm Λ 0 (fun k => c k - a k) ≤ ENNReal.ofReal ε)
    (ha : spatialNorm Λ 0 a ≤ ENNReal.ofReal α)
    (hE₂ : rN θ Λ a₀ B (fun t k => K₂ t k - A₂ t k) ≤ ENNReal.ofReal E)
    (hA₂ : rN θ Λ a₀ B A₂ ≤ ENNReal.ofReal α₂) :
    rN θ Λ a₀ B (fun t k => c k * K₂ t k - a k * A₂ t k) ≤
        ENNReal.ofReal (cLeib d Λ * (ε * (E + α₂) + α * E)) ∧
      rN θ Λ a₀ B (fun t k => a k * A₂ t k) ≤ ENNReal.ofReal (cLeib d Λ * (α * α₂)) := by
  have hL := cLeib_nonneg d Λ
  constructor
  · have e : ∀ t ∈ B, ∀ k ∈ (Set.univ : Set (Mom d)), c k * K₂ t k - a k * A₂ t k =
        (c k - a k) * (K₂ t k - A₂ t k) + (c k - a k) * A₂ t k + a k * (K₂ t k - A₂ t k) :=
      fun _ _ _ _ => by ring
    refine (restr_congr B Set.univ e).trans_le ((restr_add₃_le hΛ B Set.univ
      (fun t k => (c k - a k) * (K₂ t k - A₂ t k)) (fun t k => (c k - a k) * A₂ t k)
      (fun t k => a k * (K₂ t k - A₂ t k))).trans ?_)
    have h1 := restr_mul_s_le hΛ hd (θ := θ) a₀ B (c := fun k => c k - a k)
      (fun t k => K₂ t k - A₂ t k) hε hca hE₂
    have h2 := restr_mul_s_le hΛ hd (θ := θ) a₀ B (c := fun k => c k - a k) A₂ hε hca hA₂
    have h3 := restr_mul_s_le hΛ hd (θ := θ) a₀ B (c := a) (fun t k => K₂ t k - A₂ t k) hα ha hE₂
    refine (add_le_add (add_le_add h1 h2) h3).trans_eq ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  · exact (restr_mul_s_le hΛ hd (θ := θ) a₀ B (c := a) A₂ hα ha hA₂).trans_eq (by rw [mul_assoc])

/-- **The time-dependent top factor**, by the product estimate. -/
theorem restr_top30 (hΛ : Λ ≠ 0) (hd : 1 ≤ d) (hθ : 0 ≤ θ) (a₀ : ℕ) (B : Set (Fin r → ℝ))
    (hB : ∀ t ∈ B, t ∈ closure (interior B)) (x y K₂ A₂ : (Fin r → ℝ) → Mom d → ℂ)
    (hc₁ : ∀ k, Continuous fun t => K₂ t k - A₂ t k) (hc₂ : ∀ k, Continuous fun t => A₂ t k)
    {e α E α₂ : ℝ} (he : 0 ≤ e) (hα : 0 ≤ α) (hE : 0 ≤ E) (hα₂ : 0 ≤ α₂)
    (hx : rN θ Λ 0 B (fun t k => x t k - y t k) ≤ ENNReal.ofReal e)
    (hy : rN θ Λ 0 B y ≤ ENNReal.ofReal α)
    (hE₂ : rN θ Λ a₀ B (fun t k => K₂ t k - A₂ t k) ≤ ENNReal.ofReal E)
    (hA₂ : rN θ Λ a₀ B A₂ ≤ ENNReal.ofReal α₂) :
    rN θ Λ a₀ B (fun t k => x t k * K₂ t k - y t k * A₂ t k) ≤
        ENNReal.ofReal (2 ^ θ * cLeib d Λ * (e * (E + α₂) + α * E)) ∧
      rN θ Λ a₀ B (fun t k => y t k * A₂ t k) ≤ ENNReal.ofReal (2 ^ θ * cLeib d Λ * (α * α₂)) := by
  have h2θ : (0 : ℝ) ≤ 2 ^ θ := Real.rpow_nonneg (by norm_num) θ
  have hL := cLeib_nonneg d Λ
  have prod : ∀ {u z : ℝ} (F G : (Fin r → ℝ) → Mom d → ℂ), (∀ k, Continuous fun t => G t k) →
      0 ≤ u → 0 ≤ z → rN θ Λ 0 B F ≤ ENNReal.ofReal u → rN θ Λ a₀ B G ≤ ENNReal.ofReal z →
      rN θ Λ a₀ B (fun t k => F t k * G t k) ≤ ENNReal.ofReal (2 ^ θ * cLeib d Λ * u * z) := by
    intro u z F G hG hu hz hF hGz
    have := restr_mul_le_real hΛ hd hθ 0 a₀ hB F G hG hu hz hF hGz
    rwa [zero_add] at this
  constructor
  · have eq : ∀ t ∈ B, ∀ k ∈ (Set.univ : Set (Mom d)), x t k * K₂ t k - y t k * A₂ t k =
        (x t k - y t k) * (K₂ t k - A₂ t k) + (x t k - y t k) * A₂ t k + y t k * (K₂ t k - A₂ t k) :=
      fun _ _ _ _ => by ring
    refine (restr_congr B Set.univ eq).trans_le ((restr_add₃_le hΛ B Set.univ
      (fun t k => (x t k - y t k) * (K₂ t k - A₂ t k)) (fun t k => (x t k - y t k) * A₂ t k)
      (fun t k => y t k * (K₂ t k - A₂ t k))).trans ?_)
    have h1 := prod (fun t k => x t k - y t k) (fun t k => K₂ t k - A₂ t k) hc₁ he hE hx hE₂
    have h2 := prod (fun t k => x t k - y t k) A₂ hc₂ he hα₂ hx hA₂
    have h3 := prod y (fun t k => K₂ t k - A₂ t k) hc₁ hα hE hy hE₂
    refine (add_le_add (add_le_add h1 h2) h3).trans_eq ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  · exact (prod y A₂ hc₂ hα hα₂ hy hA₂).trans_eq (by congr 1; ring)

/-- A `k`-independent time function costs its order-zero norm. -/
theorem rN_const_param_le (B : Set (Fin r → ℝ)) (J : (Fin r → ℝ) → ℂ) :
    rN θ Λ 0 B (fun t (_ : Mom d) => J t) ≤
      mixedRestrictionNorm00 (V := Unit) θ B Set.univ (fun t _ => J t) := by
  rw [mixedRestrictionNorm00_eq_agreement (V := Unit) θ B Set.univ (fun t _ => J t)]
  refine le_iInf₂ fun G hG => ?_
  refine (rN_le_extension B (fun t _ => J t) (fun t _ => G t ()) (fun t ht => ?_)).trans ?_
  · funext k
    exact hG t ht () (mem_univ _)
  by_cases hi : ∀ v : Unit, Integrable fun t => G t v
  · have hiG : Integrable fun t => G t () := hi ()
    have hFT : ∀ ξ, mixedTimeFourier (fun t (_ : Mom d) => G t ()) ξ = fun _ => timeFourier (fun t => G t ()) ξ :=
      fun ξ => rfl
    have hadm : MixedFourierAdmissible Λ (fun t (_ : Mom d) => G t ()) :=
      ⟨fun _ => hiG, Or.inr (ae_of_all _ fun ξ => by rw [hFT ξ]; exact contDiff_const)⟩
    rw [mixedFourierNorm_eq_iSup hadm, mixedFourierNorm00_eq_lintegral hi]
    refine iSup₂_le fun n hn => iSup_le fun ρ => ?_
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      refine lintegral_mono fun ξ => mul_le_mul_right ?_ _
      simp only [momentumDerivative_zero, hFT]
      unfold momentumSupNorm mixedFourierEnvelope00
      refine iSup_le fun k => ?_
      simp only [pow_zero, ENNReal.ofReal_one, one_mul]
      exact le_iSup (fun v : Unit => ‖timeFourier (fun t => G t v) ξ‖ₑ) ()
    · have h0 : ∀ ξ, momentumDerivative ρ (mixedTimeFourier (fun t (_ : Mom d) => G t ()) ξ) = fun _ => 0 := by
        intro ξ
        rw [hFT ξ]
        funext k
        unfold momentumDerivative
        rw [iteratedFDeriv_const_of_ne hn0.ne']
        rfl
      have hz : momentumSupNorm 0 (fun _ : Mom d => (0 : ℂ)) = 0 := by simp [momentumSupNorm]
      simp [h0, hz]
  · rw [mixedFourierNorm00_of_not_integrable hi]
    exact le_top

end Step

end WaveTurbulence.PL2330
