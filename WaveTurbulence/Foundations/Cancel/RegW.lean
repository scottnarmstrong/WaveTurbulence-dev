/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.Cores
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Gaussian weights on finitely many variables (DH21 (gausspv))

DH21 (gausspv) regularizes an integral over `α[W]` by the weight `∏_{j∈W} e^{-πθ²α_j²}`. To extract the
component `𝒥B̃_{Q,Z}` of DH21 (maincoef3), a variable `z ∈ Z` also gets the factor `θζ_zπiα_z`, which
cancels the denominator of `Φ(ζ_zα_z) = χ_∞(α_z)/(ζ_zπiα_z)`.

* `omg θ z b x = e^{-πθ²x²} · (θzπix if b)`, and `wgt θ ζ Z S α = ∏_{w∈S} omg θ (ζ w) (w ∈ Z) (α w)`.
* `mint_mul_of_dependsOn`: the integral over a disjoint union of a product of functions of the two
  groups of variables is the product of the integrals.
* `mint_intervalIntegral`: Fubini between the variables and a time integral.
* `integral_phase_omg`: `∫ e^{πiεxu} omg θ z b x dx` is `gk θ u` (`b` false) or `zε hk θ u` (`b` true).
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral Function
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR

/-! ### One variable -/

/-- The one-variable weight `e^{-πθ²x²}`, times `θzπix` if `b`. -/
@[expose] noncomputable def omg (θ : ℝ) (z : ℤ) (b : Bool) (x : ℝ) : ℂ :=
  (gw θ x : ℂ) * (if b then θ * z * π * I * x else 1)

@[fun_prop] theorem continuous_omg (θ : ℝ) (z : ℤ) (b : Bool) : Continuous (omg θ z b) := by
  unfold omg; have := continuous_gw θ; split_ifs <;> fun_prop

theorem integrable_omg {θ : ℝ} (hθ : 0 < θ) (z : ℤ) (b : Bool) : Integrable (omg θ z b) := by
  unfold omg
  cases b
  · simpa using (integrable_gw hθ).ofReal (𝕜 := ℂ)
  · have h' : Integrable (fun x : ℝ => (x : ℂ) * (gw θ x : ℂ)) := by
      simpa using (integrable_mul_gw hθ).ofReal (𝕜 := ℂ)
    refine (h'.const_mul ((θ : ℂ) * z * π * I)).congr (Eventually.of_forall fun x => ?_)
    simp only [ite_true]
    ring

/-- `∫ e^{πiεxu} omg θ z b x dx`. -/
theorem integral_phase_omg {θ : ℝ} (hθ : 0 < θ) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (z : ℤ) (b : Bool)
    (u : ℝ) : ∫ x : ℝ, cexp (π * I * (ε * x * u)) * omg θ z b x =
      if b then (z * ε : ℂ) * hk θ u else gk θ u := by
  have e1 : ∀ x : ℝ, cexp (π * I * (ε * x * u)) = cexp (π * I * ((ε * u : ℝ) * x)) := fun x => by
    push_cast; ring_nf
  cases b
  · simp only [omg, Bool.false_eq_true, ite_false, mul_one]
    simp_rw [e1]
    rw [ft_gw hθ]
    unfold gk; rcases hε with rfl | rfl <;> simp
  · simp only [omg, ite_true]
    have h := ft_xgw hθ (ε * u)
    have e2 : (fun x : ℝ => cexp (π * I * (ε * x * u)) * ((gw θ x : ℂ) * (θ * z * π * I * x))) =
        fun x : ℝ => (z : ℂ) * ((θ * π * I * x) * (cexp (π * I * ((ε * u : ℝ) * x)) * (gw θ x : ℂ))) := by
      funext x; rw [e1]; ring
    rw [e2, MeasureTheory.integral_const_mul, h]
    have hodd : hk θ (ε * u) = ε * hk θ u := by
      unfold hk; rcases hε with rfl | rfl <;> simp; ring
    rw [hodd]; push_cast; ring

/-! ### Many variables -/

variable {V : Type*} [DecidableEq V]

/-- **The weight** `∏_{w∈S} e^{-πθ²α_w²} · ∏_{z∈Z∩S} θζ_zπiα_z`. -/
@[expose] noncomputable def wgt (θ : ℝ) (ζ : V → ℤ) (Z S : Finset V) (α : V → ℝ) : ℂ :=
  ∏ w ∈ S, omg θ (ζ w) (decide (w ∈ Z)) (α w)

theorem continuous_updateFinset (α₀ : V → ℝ) (S : Finset V) :
    Continuous fun y : ↥S → ℝ => updateFinset α₀ S y := by
  refine continuous_pi fun v => ?_
  simp only [updateFinset]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_wgt (θ : ℝ) (ζ : V → ℤ) (Z S : Finset V) : Continuous (wgt θ ζ Z S) := by
  unfold wgt
  exact continuous_finsetProd _ fun w _ => (continuous_omg _ _ _).comp (continuous_apply w)

theorem wgt_updateFinset (θ : ℝ) (ζ : V → ℤ) (Z S : Finset V) (α₀ : V → ℝ) (y : ↥S → ℝ) :
    wgt θ ζ Z S (updateFinset α₀ S y) = ∏ i : ↥S, omg θ (ζ i) (decide ((i : V) ∈ Z)) (y i) := by
  unfold wgt
  rw [← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [updateFinset, i.2]

theorem dependsOn_wgt (θ : ℝ) (ζ : V → ℤ) (Z S : Finset V) : DependsOn (wgt θ ζ Z S) ↑S := by
  intro α α' h
  unfold wgt
  exact Finset.prod_congr rfl fun w hw => by rw [h w hw]

theorem mInt_wgt {θ : ℝ} (hθ : 0 < θ) (ζ : V → ℤ) (Z S : Finset V) (α₀ : V → ℝ) :
    MInt S (wgt θ ζ Z S) α₀ := by
  unfold MInt
  simp_rw [wgt_updateFinset]
  rw [volume_pi]
  exact Integrable.fintype_prod fun i => integrable_omg hθ _ _

/-- A bounded continuous function times the weight is integrable. -/
theorem mInt_mul_wgt {θ : ℝ} (hθ : 0 < θ) (ζ : V → ℤ) (Z S : Finset V) (α₀ : V → ℝ)
    {f : (V → ℝ) → ℂ} (hf : Continuous f) {B : ℝ} (hB : ∀ α, ‖f α‖ ≤ B) :
    MInt S (fun α => f α * wgt θ ζ Z S α) α₀ := by
  unfold MInt
  have h := mInt_wgt hθ ζ Z S α₀
  unfold MInt at h
  refine h.bdd_mul (c := B) (hf.comp (continuous_updateFinset α₀ S)).aestronglyMeasurable
    (Eventually.of_forall fun y => hB _)

/-- **Fubini over two disjoint groups of variables.** -/
theorem mint_mul_of_dependsOn {A B : Finset V} (hAB : Disjoint A B) {f g : (V → ℝ) → ℂ}
    {α₀ : V → ℝ} (hf : DependsOn f ↑A) (hg : DependsOn g ↑B) (hfi : MInt A f α₀)
    (hgi : MInt B g α₀) :
    MInt (A ∪ B) (fun α => f α * g α) α₀ ∧
      mint (A ∪ B) (fun α => f α * g α) α₀ = mint A f α₀ * mint B g α₀ := by
  have hp := measurePreserving_piFinsetUnion hAB (fun _ : V => (volume : Measure ℝ))
  set e := MeasurableEquiv.piFinsetUnion (fun _ : V => ℝ) hAB
  have hcomp : ∀ p : (↥A → ℝ) × (↥B → ℝ),
      f (updateFinset α₀ (A ∪ B) (e p)) * g (updateFinset α₀ (A ∪ B) (e p)) =
        f (updateFinset α₀ A p.1) * g (updateFinset α₀ B p.2) := by
    intro p
    have he : updateFinset α₀ (A ∪ B) (e p) = updateFinset (updateFinset α₀ A p.1) B p.2 :=
      (updateFinset_updateFinset hAB).symm
    rw [he]
    congr 1
    · refine hf fun v hv => ?_
      have hvB : v ∉ B := Finset.disjoint_left.1 hAB hv
      simp [updateFinset, hvB]
    · refine hg fun v hv => ?_
      have hv' : v ∈ B := hv
      simp [updateFinset, hv']
  have hprod : Integrable (fun p : (↥A → ℝ) × (↥B → ℝ) =>
      f (updateFinset α₀ A p.1) * g (updateFinset α₀ B p.2))
      ((Measure.pi fun _ : ↥A => (volume : Measure ℝ)).prod
        (Measure.pi fun _ : ↥B => (volume : Measure ℝ))) := by
    unfold MInt at hfi hgi
    rw [volume_pi] at hfi hgi
    exact hfi.mul_prod hgi
  refine ⟨?_, ?_⟩
  · exact (hp.integrable_comp_emb e.measurableEmbedding).1
      (hprod.congr (Eventually.of_forall fun p => (hcomp p).symm))
  · have h1 : mint (A ∪ B) (fun α => f α * g α) α₀ = ∫ p, (f (updateFinset α₀ (A ∪ B) (e p)) *
        g (updateFinset α₀ (A ∪ B) (e p))) ∂((Measure.pi fun _ : ↥A => (volume : Measure ℝ)).prod
          (Measure.pi fun _ : ↥B => (volume : Measure ℝ))) :=
      (hp.integral_comp e.measurableEmbedding _).symm
    rw [h1]
    simp_rw [hcomp]
    rw [integral_prod_mul (f := fun y : ↥A → ℝ => f (updateFinset α₀ A y))
      (g := fun z : ↥B → ℝ => g (updateFinset α₀ B z))]
    rfl

/-- **Fubini between the variables and a time integral.** -/
theorem mint_intervalIntegral {S : Finset V} {φ : (V → ℝ) → ℝ → ℂ} {a b : ℝ} (α₀ : V → ℝ)
    (hφ : Continuous fun p : (V → ℝ) × ℝ => φ p.1 p.2) {ψ : (V → ℝ) → ℝ}
    (hb : ∀ α, ∀ τ ∈ uIcc a b, ‖φ α τ‖ ≤ ψ α) (hψ : Integrable fun y : ↥S → ℝ =>
      ψ (updateFinset α₀ S y)) :
    mint S (fun α => ∫ τ in a..b, φ α τ) α₀ = ∫ τ in a..b, mint S (fun α => φ α τ) α₀ := by
  unfold mint
  refine (intervalIntegral_integral_swap ?_).symm
  have hc : Continuous (Function.uncurry fun (τ : ℝ) (y : ↥S → ℝ) => φ (updateFinset α₀ S y) τ) :=
    hφ.comp ((continuous_updateFinset α₀ S).comp continuous_snd |>.prodMk continuous_fst)
  have hg : Integrable (fun p : ℝ × (↥S → ℝ) => (1 : ℝ) * ψ (updateFinset α₀ S p.2))
      ((volume.restrict (uIoc a b)).prod volume) := by
    have : IsFiniteMeasure (volume.restrict (uIoc a b)) :=
      isFiniteMeasure_restrict.2 (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
    exact Integrable.mul_prod (μ := volume.restrict (uIoc a b)) (integrable_const (1 : ℝ)) hψ
  refine Integrable.mono' hg hc.aestronglyMeasurable ?_
  rw [show (volume.restrict (uIoc a b)).prod (volume : Measure (↥S → ℝ)) =
      (volume.prod volume).restrict (uIoc a b ×ˢ univ) by
    rw [← Measure.prod_restrict, Measure.restrict_univ],
    ae_restrict_iff' (measurableSet_uIoc.prod MeasurableSet.univ)]
  refine Eventually.of_forall fun p hp => ?_
  simp only [Function.uncurry, one_mul]
  exact hb _ p.1 (uIoc_subset_uIcc hp.1)

end WaveTurbulence.Cancel
