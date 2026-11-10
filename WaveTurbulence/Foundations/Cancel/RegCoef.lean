/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.RegSteps

/-!
# Regularized integrals of time coefficients (DH21 §7.2–7.3)

For a time coefficient `F(α, t, s)` in the variables `S` (DH21's `B̃_Q`),
`RI θ ζ Z S F t s = ∫ F(α, t, s) ∏_{z∈Z∩S} θζ_zπiα_z ∏_{w∈S} e^{-πθ²α_w²} dα[S]`. `RegCoef ζ Z S F J` says
that these regularized integrals have the invariant `RegLim2` with limit `J`.

* `regCoef_one`, `regCoef_mul`, `regCoef_swap`: the trivial couple, products of coefficients in
  disjoint variables (the pair coefficients of DH21 (newexp2)), and the time swaps of DH21 L924.
* `regCoef_type1`: the type 1 recursion DH21 (newexp1). `RI` of `type1F v sw F` is the type 1
  regularized integral of the `RI` of the `F j` (Fubini). Its limit is DH21 (recurtype1), or `0` if the
  root variable is in `Z`.
* `mint_eq_of_regCoef`: **the integral of the `Z` component** of any expansion of DH21 (maincoef3)
  equals the limit `J`.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral Function
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR

variable {V : Type} [DecidableEq V]

/-- **The `Z`-weighted Gaussian regularization** of a time coefficient over its variables `S`. -/
@[expose] noncomputable def RI (θ : ℝ) (ζ : V → ℤ) (Z S : Finset V) (F : (V → ℝ) → ℝ → ℝ → ℂ)
    (t s : ℝ) : ℂ :=
  mint S (fun α => F α t s * wgt θ ζ Z S α) 0

/-- A time coefficient in the variables `S`: jointly continuous, bounded on the square uniformly in
the variables, and depending only on the variables in `S`. -/
structure NiceCoef (S : Finset V) (F : (V → ℝ) → ℝ → ℝ → ℂ) : Prop where
  dep : ∀ t s, DependsOn (fun α => F α t s) ↑S
  cont : Continuous fun p : (V → ℝ) × ℝ × ℝ => F p.1 p.2.1 p.2.2
  bdd : ∃ B, ∀ α, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ‖F α t s‖ ≤ B

/-- **A time coefficient with a regularized limit**: its regularized integrals have the invariant
`RegLim2` with limit `J`. -/
structure RegCoef (ζ : V → ℤ) (Z S : Finset V) (F : (V → ℝ) → ℝ → ℝ → ℂ) (J : ℝ → ℝ → ℂ) :
    Prop where
  nice : NiceCoef S F
  lim : RegLim2 (fun θ t s => RI θ ζ Z S F t s) J

/-! ### Basic facts -/

omit [DecidableEq V] in
theorem continuous_at_times {F : (V → ℝ) → ℝ → ℝ → ℂ}
    (hF : Continuous fun p : (V → ℝ) × ℝ × ℝ => F p.1 p.2.1 p.2.2) (t s : ℝ) :
    Continuous fun α => F α t s :=
  hF.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : V → ℝ => ((t, s) : ℝ × ℝ)))

omit [DecidableEq V] in
theorem dependsOn_mono {f : (V → ℝ) → ℂ} {A B : Set V} (h : DependsOn f A) (hAB : A ⊆ B) :
    DependsOn f B := fun _ _ hx => h fun i hi => hx i (hAB hi)

omit [DecidableEq V] in
theorem dependsOn_mul {f g : (V → ℝ) → ℂ} {A : Set V} (hf : DependsOn f A) (hg : DependsOn g A) :
    DependsOn (fun α => f α * g α) A := by
  intro α α' h
  simp only
  rw [hf h, hg h]

theorem mint_eq_of_dependsOn {W : Finset V} {f : (V → ℝ) → ℂ} (hf : DependsOn f ↑W) (α₀ α₁ : V → ℝ) :
    mint W f α₀ = mint W f α₁ := by
  unfold mint
  refine integral_congr_ae (Eventually.of_forall fun y => hf fun i hi => ?_)
  simp [updateFinset, Finset.mem_coe.1 hi]

theorem wgt_union {A B : Finset V} (h : Disjoint A B) (θ : ℝ) (ζ : V → ℤ) (Z : Finset V)
    (α : V → ℝ) : wgt θ ζ Z (A ∪ B) α = wgt θ ζ Z A α * wgt θ ζ Z B α := by
  unfold wgt; rw [Finset.prod_union h]

/-- **Fubini for a product of functions of disjoint groups, with the weights.** -/
theorem mint_mul_wgt {θ : ℝ} (hθ : 0 < θ) (ζ : V → ℤ) (Z : Finset V) {A B : Finset V}
    (hAB : Disjoint A B) {f g : (V → ℝ) → ℂ} (hf : DependsOn f ↑A) (hg : DependsOn g ↑B)
    (hfc : Continuous f) (hgc : Continuous g) {Cf Cg : ℝ} (hfb : ∀ α, ‖f α‖ ≤ Cf)
    (hgb : ∀ α, ‖g α‖ ≤ Cg) (α₀ : V → ℝ) :
    MInt (A ∪ B) (fun α => f α * g α * wgt θ ζ Z (A ∪ B) α) α₀ ∧
      mint (A ∪ B) (fun α => f α * g α * wgt θ ζ Z (A ∪ B) α) α₀ =
        mint A (fun α => f α * wgt θ ζ Z A α) α₀ * mint B (fun α => g α * wgt θ ζ Z B α) α₀ := by
  have e : (fun α => f α * g α * wgt θ ζ Z (A ∪ B) α) =
      fun α => (f α * wgt θ ζ Z A α) * (g α * wgt θ ζ Z B α) := by
    funext α; rw [wgt_union hAB]; ring
  rw [e]
  exact mint_mul_of_dependsOn hAB (dependsOn_mul hf (dependsOn_wgt θ ζ Z A))
    (dependsOn_mul hg (dependsOn_wgt θ ζ Z B)) (mInt_mul_wgt hθ ζ Z A α₀ hfc hfb)
    (mInt_mul_wgt hθ ζ Z B α₀ hgc hgb)

/-- `∫ e^{πiεα_v u} (weight of v) dα_v`. -/
theorem mint_phase_wgt {θ : ℝ} (hθ : 0 < θ) (ζ : V → ℤ) (Z : Finset V) (v : V) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (u : ℝ) (α₀ : V → ℝ) :
    mint {v} (fun α => cexp (π * I * (ε * α v * u)) * wgt θ ζ Z {v} α) α₀ =
      if v ∈ Z then (ζ v * ε : ℂ) * hk θ u else gk θ u := by
  rw [mint_singleton]
  simp only [wgt, Finset.prod_singleton, update_self]
  rw [integral_phase_omg hθ hε]
  by_cases hv : v ∈ Z <;> simp [hv]

/-! ### The closure lemmas -/

theorem regCoef_one (ζ : V → ℤ) (Z : Finset V) :
    RegCoef ζ Z ∅ (fun _ _ _ => 1) (fun _ _ => 1) := by
  refine ⟨⟨fun _ _ _ _ _ => rfl, continuous_const, ⟨1, fun _ _ _ _ _ => by simp⟩⟩, ?_⟩
  refine (RegLim2.const 1).congr (Eventually.of_forall fun θ t _ s _ => ?_)
  simp [RI, mint_empty, wgt]

theorem regCoef_swap {ζ : V → ℤ} {Z S : Finset V} {F : (V → ℝ) → ℝ → ℝ → ℂ} {J : ℝ → ℝ → ℂ}
    (h : RegCoef ζ Z S F J) (b : Bool) :
    RegCoef ζ Z S (swapT b F) (fun t s => if b then J s t else J t s) := by
  cases b
  · simpa [swapT] using h
  · simp only [swapT, ite_true]
    obtain ⟨B, hB⟩ := h.nice.bdd
    refine ⟨⟨fun t s => h.nice.dep s t, h.nice.cont.comp
      (continuous_fst.prodMk (continuous_snd.snd.prodMk continuous_snd.fst)),
      ⟨B, fun α t ht s hs => hB α s hs t ht⟩⟩, ?_⟩
    exact h.lim.swap

theorem nice_mul {A B : Finset V} {F₁ F₂ : (V → ℝ) → ℝ → ℝ → ℂ} (h₁ : NiceCoef A F₁)
    (h₂ : NiceCoef B F₂) : NiceCoef (A ∪ B) fun α t s => F₁ α t s * F₂ α t s := by
  obtain ⟨B₁, hB₁⟩ := h₁.bdd
  obtain ⟨B₂, hB₂⟩ := h₂.bdd
  refine ⟨fun t s => dependsOn_mul (dependsOn_mono (h₁.dep t s) (by simp))
    (dependsOn_mono (h₂.dep t s) (by simp)), h₁.cont.mul h₂.cont, ⟨max B₁ 0 * max B₂ 0, ?_⟩⟩
  intro α t ht s hs
  rw [norm_mul]
  exact mul_le_mul ((hB₁ α t ht s hs).trans (le_max_left _ _)) ((hB₂ α t ht s hs).trans
    (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)

theorem RI_mul {θ : ℝ} (hθ : 0 < θ) (ζ : V → ℤ) (Z : Finset V) {A B : Finset V}
    (hAB : Disjoint A B) {F₁ F₂ : (V → ℝ) → ℝ → ℝ → ℂ} (h₁ : NiceCoef A F₁) (h₂ : NiceCoef B F₂)
    {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    RI θ ζ Z (A ∪ B) (fun α t s => F₁ α t s * F₂ α t s) t s = RI θ ζ Z A F₁ t s * RI θ ζ Z B F₂ t s := by
  obtain ⟨B₁, hB₁⟩ := h₁.bdd
  obtain ⟨B₂, hB₂⟩ := h₂.bdd
  exact (mint_mul_wgt hθ ζ Z hAB (h₁.dep t s) (h₂.dep t s) (continuous_at_times h₁.cont t s)
    (continuous_at_times h₂.cont t s) (fun α => hB₁ α t ht s hs) (fun α => hB₂ α t ht s hs) 0).2

theorem regCoef_mul {ζ : V → ℤ} {Z A B : Finset V} (hAB : Disjoint A B)
    {F₁ F₂ : (V → ℝ) → ℝ → ℝ → ℂ} {J₁ J₂ : ℝ → ℝ → ℂ} (h₁ : RegCoef ζ Z A F₁ J₁)
    (h₂ : RegCoef ζ Z B F₂ J₂) :
    RegCoef ζ Z (A ∪ B) (fun α t s => F₁ α t s * F₂ α t s) (fun t s => J₁ t s * J₂ t s) := by
  refine ⟨nice_mul h₁.nice h₂.nice, (h₁.lim.mul h₂.lim).congr ?_⟩
  filter_upwards [eventually_pos_nhdsGT] with θ hθ t ht s hs
  exact RI_mul hθ ζ Z hAB h₁.nice h₂.nice ht hs

/-! ### The extraction of the `Z` component -/

/-- **`𝒥B̃_{Q,Z}` is the regularized limit** (DH21 (defintcal)). If `F` has a regularized limit `J`
and an expansion `F = Σ_{Z'⊆S} ∏_{z∈Z'} Φ(ζ_zα_z) G_{Z'}` on the square as in DH21 (maincoef3), with
`G_{Z'}` a function of `α[S∖Z']`, integrable there, then `∫ G_Z dα[S∖Z] = J` on the square. -/
theorem mint_eq_of_regCoef {ζ : V → ℤ} (hζ : ∀ v, ζ v = 1 ∨ ζ v = -1) {Z S : Finset V}
    (hZ : Z ⊆ S) {F : (V → ℝ) → ℝ → ℝ → ℂ} {J : ℝ → ℝ → ℂ} (hR : RegCoef ζ Z S F J)
    {G : Finset V → (V → ℝ) → ℝ → ℝ → ℂ}
    (hGd : ∀ Z' ⊆ S, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      DependsOn (fun α => G Z' α t s) ↑(S \ Z'))
    (hGi : ∀ Z' ⊆ S, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, MInt (S \ Z') (fun α => G Z' α t s) 0)
    (hF : ∀ α, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      F α t s = ∑ Z' ∈ S.powerset, (∏ z ∈ Z', PhiZ ζ z (α z)) * G Z' α t s)
    {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) (α₀ : V → ℝ) :
    mint (S \ Z) (fun α => G Z α t s) α₀ = J t s := by
  rw [mint_eq_of_dependsOn (hGd Z hZ t ht s hs) α₀ 0]
  have h1 := tendsto_mint_wgt_of_expansion hZ hζ (F := fun α => F α t s)
    (G := fun Z' α => G Z' α t s) (α₀ := 0) (fun Z' hZ' => hGd Z' hZ' t ht s hs)
    (fun Z' hZ' => hGi Z' hZ' t ht s hs) (fun α => hF α t ht s hs)
  exact tendsto_nhds_unique h1 (hR.lim.lim t ht s hs)

end WaveTurbulence.Cancel
