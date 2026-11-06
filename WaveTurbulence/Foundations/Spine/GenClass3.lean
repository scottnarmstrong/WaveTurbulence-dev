/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GenClass2
import Mathlib.Tactic
/-! Per-pattern preparation: the enumeration of `X_θ ⊔ Y_θ`, the Y-forest, the product-model
localization, and the bound from `gen_core`. -/
@[expose] public section
open MeasureTheory Set Finset Function
open scoped ENNReal
namespace WaveTurbulence.Ladder
open scoped Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Type} [Fintype Q] [DecidableEq Q] {K : Q → ℕ}

theorem xθ_injective (ua va : Jr K → ι) (hinj : Function.Injective (Sum.elim ua va)) (θ : Jr K → Bool) :
    Function.Injective (xθ ua va θ) := by
  intro j j' h
  unfold xθ at h
  by_cases h1 : θ j <;> by_cases h2 : θ j' <;> simp only [h1, h2, if_true, if_false] at h
  · exact (Sum.inl.inj (hinj (a₁ := Sum.inl j) (a₂ := Sum.inl j') (by simpa using h)))
  · have := hinj (a₁ := Sum.inl j) (a₂ := Sum.inr j') (by simpa using h); simp at this
  · have := hinj (a₁ := Sum.inr j) (a₂ := Sum.inl j') (by simpa using h); simp at this
  · exact (Sum.inr.inj (hinj (a₁ := Sum.inr j) (a₂ := Sum.inr j') (by simpa using h)))

theorem yθ_ne_xθ (ua va : Jr K → ι) (hinj : Function.Injective (Sum.elim ua va)) (θ : Jr K → Bool)
    (j j' : Jr K) : yθ ua va θ j ≠ xθ ua va θ j' := by
  intro h
  unfold yθ xθ at h
  by_cases h1 : θ j <;> by_cases h2 : θ j' <;> simp only [h1, h2, if_true, if_false] at h
  · have := hinj (a₁ := Sum.inr j) (a₂ := Sum.inl j') (by simpa using h); simp at this
  · have := hinj (a₁ := Sum.inr j) (a₂ := Sum.inr j') (by simpa using h)
    have hj : j = j' := Sum.inr.inj this
    subst hj; simp_all
  · have := hinj (a₁ := Sum.inl j) (a₂ := Sum.inl j') (by simpa using h)
    have hj : j = j' := Sum.inl.inj this
    subst hj; simp_all
  · have := hinj (a₁ := Sum.inl j) (a₂ := Sum.inr j') (by simpa using h); simp at this

theorem measurableSet_RvOf {k : ℕ} (σ : Fin k ≃ Jr K) (D : ℝ) : MeasurableSet (RvOf σ D) := by
  unfold RvOf
  have : {tx : Fin k → ℝ | ∀ q, (fun j : Fin (K q) => tx (σ.symm ⟨q, j⟩)) ∈ Vset (K q) D} =
      ⋂ q, (fun tx : Fin k → ℝ => fun j : Fin (K q) => tx (σ.symm ⟨q, j⟩)) ⁻¹' Vset (K q) D := by
    ext tx; simp
  rw [this]
  refine MeasurableSet.iInter (fun q => (measurableSet_Vset _ _).preimage ?_)
  exact measurable_pi_iff.mpr (fun j => measurable_pi_apply _)

theorem theta_bound
    (ch : ι → ι → Prop) (dep : ι → ℕ) (hdep : ∀ a b, ch a b → dep b < dep a)
    (huniq : ∀ a b b', ch a b → ch a b' → b = b')
    (ua va : Jr K → ι) (hinj : Function.Injective (Sum.elim ua va))
    (ls cap : ι → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (σ : Fin (Fintype.card (Jr K)) ≃ Jr K) (θ : Jr K → Bool) (A : Finset ι)
    (Sy : ι → Set ℝ) (hSy : ∀ b, MeasurableSet (Sy b)) (Kc : ℝ≥0∞)
    (hKc : ∀ b (β : ℝ), ∫⁻ a in Sy b, ENNReal.ofReal (br (a + β))⁻¹ ≤ Kc)
    (ρb : Jr K → ℝ) (hX : ι → (ι → ℝ) → ℝ) (hXm : ∀ x, Measurable (hX x))
    (hXd : ∀ x (β β' : ι → ℝ), (∀ b, b ∉ Finset.univ.image (xθ ua va θ) → β b = β' b) →
      hX x β = hX x β')
    (W : Set (ι → ℝ))
    (hW : ∀ α ∈ W, (∀ b, b ∉ Finset.univ.image (xθ ua va θ) → α b ∈ Sy b) ∧
      ∀ j, |α (xθ ua va θ j) - hX (xθ ua va θ j) α| ≤ ρb j) :
    ∃ m : ℕ, Fintype.card ι = Fintype.card (Jr K) + m ∧
      ∫⁻ α in W, ‖Phi (OmegaC ls cap (ltθ ch ua va θ) (leθ ua va θ) (fun i => xθ ua va θ (σ i))
          (RvOf σ D)) ls A α‖ₑ ≤
        (∏ j, ENNReal.ofReal (2 * ρb j)) *
          ((∏ q, ENNReal.ofReal (2 ^ (K q) * D ^ (K q) / (Nat.factorial (K q) : ℝ))) *
            ENNReal.ofReal (Real.pi ^ (Fintype.card (Jr K) + m) * 3 ^ m) * (2 * Kc) ^ m) := by
  set X : Finset ι := Finset.univ.image (xθ ua va θ) with hXdef
  have hxinj := xθ_injective ua va hinj θ
  -- the `X`-enumeration
  have hbij : Function.Bijective (fun j : Jr K => (⟨xθ ua va θ j, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩ : {a // a ∈ X})) := by
    constructor
    · intro j j' h; exact hxinj (congrArg Subtype.val h)
    · rintro ⟨a, ha⟩
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
      exact ⟨j, rfl⟩
  let eX : {a // a ∈ X} ≃ Fin (Fintype.card (Jr K)) := (Equiv.ofBijective _ hbij).symm.trans σ.symm
  obtain ⟨m, e, par, hp, hxX, hyX, hparc⟩ := exists_split_with X eX ch dep hdep huniq
  have hxv : ∀ i, e.symm (Sum.inl i) = xθ ua va θ (σ i) := by
    intro i
    rw [hxX]
    simp [eX]
  have hxfun : (fun i => e.symm (Sum.inl i)) = fun i => xθ ua va θ (σ i) := funext hxv
  have hmemX : ∀ b, b ∈ X ↔ ∃ j, xθ ua va θ j = b := by
    intro b; simp [hXdef]
  have hpar' : ∀ j j', par j = some j' ↔
      ltθ ch ua va θ (e.symm (Sum.inr j)) (e.symm (Sum.inr j')) := by
    intro j j'
    rw [hparc j j']
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨i, hi, _, hb⟩)
      · exact h
      · exfalso
        apply hyX j'
        rw [hb, hmemX]
        exact ⟨i, by simp [xθ, hi]⟩
  have hle' : ∀ j j', ¬ leθ ua va θ (e.symm (Sum.inr j)) (e.symm (Sum.inr j')) := by
    rintro j j' ⟨i, hi, _, hb⟩
    apply hyX j'
    rw [hb, hmemX]
    exact ⟨i, by simp [xθ, hi]⟩
  have hcard : Fintype.card ι = Fintype.card (Jr K) + m := by
    rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  have hRvm := measurableSet_RvOf σ D
  -- localization in the product model
  let Yext : (Fin m → ℝ) → ι → ℝ := fun y b => Sum.elim (fun _ : Fin (Fintype.card (Jr K)) => (0 : ℝ)) y (e b)
  have hYext : Measurable Yext := by
    refine measurable_pi_iff.mpr (fun b => ?_)
    show Measurable (fun y : Fin m → ℝ => Sum.elim (fun _ : Fin (Fintype.card (Jr K)) => (0 : ℝ)) y (e b))
    rcases hb : e b with i | j
    · exact measurable_const
    · exact measurable_pi_apply j
  let hfun : (Fin m → ℝ) → (Fin (Fintype.card (Jr K)) → ℝ) := fun y i => hX (xθ ua va θ (σ i)) (Yext y)
  have hh : Measurable hfun := measurable_pi_iff.mpr (fun i => (hXm _).comp hYext)
  have hWloc : ∀ α ∈ W, (Th e α).2 ∈ Set.pi univ (fun j : Fin m => Sy (e.symm (Sum.inr j))) ∧
      ∀ i, |(Th e α).1 i - hfun (Th e α).2 i| ≤ ρb (σ i) := by
    intro α hα
    obtain ⟨hS, hL⟩ := hW α hα
    refine ⟨fun j _ => ?_, fun i => ?_⟩
    · rw [Th_apply]; exact hS _ (hyX j)
    · have hYe : ∀ b, b ∉ X → Yext (Th e α).2 b = α b := by
        intro b hb
        have : ∃ j, e b = Sum.inr j := by
          rcases h : e b with i | j
          · exfalso; apply hb
            have : b = e.symm (Sum.inl i) := by rw [← h]; simp
            rw [this, hxv]; exact (hmemX _).mpr ⟨σ i, rfl⟩
          · exact ⟨j, rfl⟩
        obtain ⟨j, hj⟩ := this
        simp only [Yext, hj, Sum.elim_inr]
        rw [Th_apply]
        have : b = e.symm (Sum.inr j) := by rw [← hj]; simp
        simp only [this]
      have h1 := hXd (xθ ua va θ (σ i)) (Yext (Th e α).2) α hYe
      simp only [hfun, h1]
      rw [Th_apply]
      have := hL (σ i)
      simpa [hxv] using this
  have hKc' : ∀ j (β : ℝ), ∫⁻ a in Sy (e.symm (Sum.inr j)), ENNReal.ofReal (br (a + β))⁻¹ ≤ Kc :=
    fun j β => hKc _ β
  have hcore := gen_core e ls cap (ltθ ch ua va θ) (leθ ua va θ) (RvOf σ D) hRvm par hp hpar' hle' A
    (fun j => Sy (e.symm (Sum.inr j))) (fun j => hSy _) Kc hKc' hfun hh (fun i => ρb (σ i)) W hWloc
  refine ⟨m, hcard, ?_⟩
  rw [← hxfun]
  refine hcore.trans ?_
  have hprod : ∏ i : Fin (Fintype.card (Jr K)), ENNReal.ofReal (2 * ρb (σ i)) =
      ∏ j, ENNReal.ofReal (2 * ρb j) :=
    Equiv.prod_comp σ (fun j => ENNReal.ofReal (2 * ρb j))
  rw [hprod]
  refine mul_le_mul' le_rfl ?_
  have hvol : volume (Rmod ls cap (ltθ ch ua va θ) (leθ ua va θ) (fun i => e.symm (Sum.inl i)) (RvOf σ D)) ≤
      ∏ q, ENNReal.ofReal (2 ^ (K q) * D ^ (K q) / (Nat.factorial (K q) : ℝ)) :=
    (measure_mono Set.inter_subset_left).trans (volume_groups K σ hD)
  exact mul_le_mul' (mul_le_mul' hvol le_rfl) le_rfl

end WaveTurbulence.Ladder
