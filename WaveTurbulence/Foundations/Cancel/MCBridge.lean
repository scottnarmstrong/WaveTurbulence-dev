/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.RegType2
public import WaveTurbulence.Foundations.ClassJR.MCSRep

/-!
# `𝒥B̃_{Q,Z}` for any expansion of DH21 Prop 5.1

wt-wke states DH21 Prop 5.1 as `ClassJR.MCExp θ a b A N ζ S B̃_Q`: there exist components
`G Z = B̃_{Q,Z}` with coefficient representations `MCRep … (S ∖ Z) (G Z)`, and on the square
`B̃_Q = Σ_{Z⊆S} ∏_{z∈Z} Φ(ζ_zα_z) · G Z` (DH21 (maincoef3)). DH21 (defintcal) sets
`𝒥B̃_{Q,Z}(t, s) = ∫ B̃_{Q,Z}(t, s, α) dα[S∖Z]`.

* `mcRep_dependsOn`, `mcRep_mInt`: a component depends only on its variables and is integrable over
  them.
* `mint_eq_of_MCExp`: **for every such expansion, `𝒥B̃_{Q,Z}` is the regularized limit `J` of `B̃_Q`**.
  The components are not unique, but their integrals are.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral Function
open scoped Real Topology ENNReal

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR

variable {V : Type} [DecidableEq V]

theorem norm_e2_eq (lam : ℝ × ℝ) (t s : ℝ) : ‖e2 lam t s‖ = 1 := by
  unfold e2
  rw [show cexp (π * I * (lam.1 * t + lam.2 * s)) = cexp (π * I * ((lam.1 * t + lam.2 * s : ℝ) : ℂ))
    by push_cast; ring_nf]
  exact norm_cexp_piI _

omit [DecidableEq V] in
theorem mcRep_dependsOn {θ a b A N : ℝ} {W : Finset V} {G : (V → ℝ) → ℝ → ℝ → ℂ}
    (h : MCRep θ a b A N (↑W) G) {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    DependsOn (fun α => G α t s) ↑W := by
  obtain ⟨ι, _, f, C, -, hr, -, -, -, -, he⟩ := h
  intro α α' h'
  simp only
  rw [he α t s ht hs, he α' t s ht hs]
  have : α ∘ f = α' ∘ f := funext fun i => h' (f i) (hr ▸ ⟨i, rfl⟩)
  rw [this]

theorem mcRep_mInt {θ a b A N : ℝ} (hθ : 0 ≤ θ) {W : Finset V} {G : (V → ℝ) → ℝ → ℝ → ℂ}
    (h : MCRep θ a b A N (↑W) G) {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (α₀ : V → ℝ) : MInt W (fun α => G α t s) α₀ := by
  obtain ⟨ι, _, f, C, hf, hr, hN, hC, hk, -, he⟩ := h
  set H : (ι → ℝ) → ℂ := fun β => ∫ lam, C β lam * e2 lam t s with hH
  have hHm : StronglyMeasurable H := by
    have h1 : StronglyMeasurable fun p : (ι → ℝ) × (ℝ × ℝ) => C p.1 p.2 * e2 p.2 t s :=
      hC.meas.mul ((by unfold e2; fun_prop : Continuous fun lam : ℝ × ℝ => e2 lam t s).stronglyMeasurable.comp_measurable
        measurable_snd)
    exact h1.integral_prod_right'
  have hHi : Integrable H := by
    refine ⟨hHm.aestronglyMeasurable, ?_⟩
    have h0 := hk 0
    unfold HasFiniteIntegral
    calc ∫⁻ β, ‖H β‖ₑ ≤ ∫⁻ β, ∫⁻ lam, wL θ lam * dnorm 0 C β lam := by
          refine lintegral_mono fun β => (enorm_integral_le_lintegral_enorm _).trans ?_
          refine lintegral_mono fun lam => ?_
          rw [enorm_mul, dnorm_zero, show ‖e2 lam t s‖ₑ = 1 by
            rw [← ofReal_norm, norm_e2_eq, ENNReal.ofReal_one], mul_one]
          exact le_mul_of_one_le_left bot_le (one_le_wL hθ lam)
      _ ≤ gev N A 0 := h0
      _ < ⊤ := ENNReal.ofReal_lt_top
  have h2 := mInt_of_integrable_comp hf hr hHi α₀
  unfold MInt at h2 ⊢
  refine h2.congr (Eventually.of_forall fun y => ?_)
  simp only [hH]
  exact (he _ t s ht hs).symm

/-- **`𝒥B̃_{Q,Z}` is the regularized limit, for every expansion of DH21 Prop 5.1.** Let `F` have the
regularized limit `J`, let `Z ⊆ S`, and let `G` be the components of any expansion of `F` as in DH21
(maincoef3) (`MCExp`'s data). Then `∫ G_Z(α, t, s) dα[S∖Z] = J(t, s)` on the square. -/
theorem mint_eq_of_MCExp {θ a b A N : ℝ} (hθ : 0 ≤ θ) {ζ : V → ℤ} (hζ : ∀ v, ζ v = 1 ∨ ζ v = -1)
    {Z S : Finset V} (hZ : Z ⊆ S) {F : (V → ℝ) → ℝ → ℝ → ℂ} {J : ℝ → ℝ → ℂ}
    (hR : RegCoef ζ Z S F J) {G : Finset V → (V → ℝ) → ℝ → ℝ → ℂ}
    (hG : ∀ Z' ⊆ S, MCRep θ a b A N (↑(S \ Z')) (G Z'))
    (hF : ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      F α t s = ∑ Z' ∈ S.powerset, (∏ z ∈ Z', PhiZ ζ z (α z)) * G Z' α t s)
    {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) (α₀ : V → ℝ) :
    mint (S \ Z) (fun α => G Z α t s) α₀ = J t s :=
  mint_eq_of_regCoef hζ hZ hR (fun Z' hZ' _ ht _ hs => mcRep_dependsOn (hG Z' hZ') ht hs)
    (fun Z' hZ' _ ht _ hs => mcRep_mInt hθ (hG Z' hZ') ht hs 0) (fun α t ht s hs => hF α t s ht hs) ht hs α₀

end WaveTurbulence.Cancel
