/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.JRChain

/-!
# Class `J` and class `R` operators on subsets of a global set of variables

DH21 Lemmas 5.9–5.10 compose operators whose variables `α[A]` are disjoint subsets of a common
family. Here every operator is a family `T : P → (V → ℝ) → ℝ → ℝ → ℂ` over a global variable type
`V` and parameter space `P`. `MJ θ A N S T` says that `T` is, on the triangle, a parametric class `J`
operator in the variables `α ∘ f` for an injection `f : ι → V` with range `S`. `MR θ A N S v₀ T` is
the class `R` analogue with special variable `v₀ = f none`. `MJR` is class `J` plus class `R`
(the `R` part possibly zero). Relabellings are absorbed into the injections, so the composition and
sandwich steps need no reindexing.

This file: parameter pullback (`ClassJP.comap`, `ClassRP.comap`), `ClassRP.reindex`, the masked
classes and their sums.
-/

public section

open MeasureTheory Filter Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Comap

variable {P P' : Type*} [MeasurableSpace P] [MeasurableSpace P'] {ι : Type*} [Fintype ι]
variable {θ A N : ℝ}

/-- The parametric basic class `J` datum pulled back along `f : P' → P`. -/
@[expose] def JSymP.comap (R : JSymP P ι) (f : P' → P) : JSymP P' ι := ⟨R.y, fun p' => R.m (f p')⟩

/-- The parametric basic class `R` datum pulled back along `f : P' → P`. -/
@[expose] def RSymP.comap (R : RSymP P ι) (f : P' → P) : RSymP P' ι :=
  ⟨R.ε, R.y₁, R.y₂, fun p' => R.m (f p')⟩

theorem JSymP.Bound.comap {R : JSymP P ι} (h : R.Bound θ A N) {f : P' → P} (hf : Measurable f) :
    (R.comap f).Bound θ A N where
  bound p' := h.bound (f p')
  meas := h.meas.comp_measurable (g := fun x : P' × ((ι → ℝ) × (ℝ × ℝ)) => (f x.1, x.2))
    ((hf.comp measurable_fst).prodMk measurable_snd)
  nonneg := h.nonneg
  bundle := h.bundle

theorem RSymP.Bound.comap {R : RSymP P ι} (h : R.Bound θ A N) {f : P' → P} (hf : Measurable f) :
    (R.comap f).Bound θ A N where
  bound p' := h.bound (f p')
  meas := h.meas.comp_measurable (g := fun x : P' × ((ι → ℝ) × (ℝ × ℝ × ℝ)) => (f x.1, x.2))
    ((hf.comp measurable_fst).prodMk measurable_snd)
  nonneg := h.nonneg
  sign := h.sign
  bundle₁ := h.bundle₁
  bundle₂ := h.bundle₂

/-- **Pulling back the parameters of a parametric class `J` operator.** -/
theorem ClassJP.comap {T : P → (ι → ℝ) → ℝ → ℝ → ℂ} (h : ClassJP θ A N T) {f : P' → P}
    (hf : Measurable f) : ClassJP θ A N fun p' => T (f p') := by
  obtain ⟨n, R, c, hb, hs, he⟩ := h
  exact ⟨n, fun i => (R i).comap f, c, fun i => (hb i).comap hf, hs, fun p' α => he (f p') α⟩

/-- **Pulling back the parameters of a parametric class `R` operator.** -/
theorem ClassRP.comap {T : P → (Option ι → ℝ) → ℝ → ℝ → ℂ} (h : ClassRP θ A N T) {f : P' → P}
    (hf : Measurable f) : ClassRP θ A N fun p' => T (f p') := by
  obtain ⟨n, R, c, hb, hs, he⟩ := h
  exact ⟨n, fun i => (R i).comap f, c, fun i => (hb i).comap hf, hs, fun p' α => he (f p') α⟩

theorem ClassRP.congr {T T' : P → (Option ι → ℝ) → ℝ → ℝ → ℂ} (h : ClassRP θ A N T)
    (he : ∀ p α, KEqOn (T' p α) (T p α)) : ClassRP θ A N T' := by
  obtain ⟨n, R, c, hb, hs, he'⟩ := h
  exact ⟨n, R, c, hb, hs, fun p α => (he p α).trans (he' p α)⟩

/-- **Relabelling the non-special variables of a parametric class `R` operator.** -/
theorem ClassRP.reindex {ι' : Type*} [Fintype ι'] (e : ι ≃ ι')
    {T : P → (Option ι → ℝ) → ℝ → ℝ → ℂ} (h : ClassRP θ A N T) :
    ClassRP θ A N fun p α' => T p fun o => α' (Option.map e o) := by
  obtain ⟨n, R, c, hb, hs, he⟩ := h
  refine ⟨n, fun i => (R i).reindex e, c, fun i => (hb i).reindex e, hs, fun p α' => ?_⟩
  intro t s h0 h1 h2
  beta_reduce
  rw [he _ _ t s h0 h1 h2]
  exact Finset.sum_congr rfl fun i _ => (RSymP.reindex_kernel e (R i) p α' t s).symm

end Comap

section Defs

variable {P : Type*} [MeasurableSpace P] {V : Type}

/-- **Masked class `J`**: on the triangle, `T p α` is a parametric class `J` operator (norm `≤ N`)
in the variables `α ∘ f`, for an injection `f : ι → V` with range `S`. -/
@[expose] def MJ (θ A N : ℝ) (S : Set V) (T : P → (V → ℝ) → ℝ → ℝ → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (f : ι → V), Function.Injective f ∧ Set.range f = S ∧
    ∃ T' : P → (ι → ℝ) → ℝ → ℝ → ℂ, ClassJP θ A N T' ∧ ∀ p α, KEqOn (T p α) (T' p (α ∘ f))

/-- **Masked class `R`** with special variable `v₀`: on the triangle, `T p α` is a parametric class
`R` operator in the variables `α ∘ f`, `f : Option ι → V` injective with range `S`, `f none = v₀`. -/
@[expose] def MR (θ A N : ℝ) (S : Set V) (v₀ : V) (T : P → (V → ℝ) → ℝ → ℝ → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (f : Option ι → V), Function.Injective f ∧ Set.range f = S ∧
    f none = v₀ ∧
    ∃ T' : P → (Option ι → ℝ) → ℝ → ℝ → ℂ, ClassRP θ A N T' ∧ ∀ p α, KEqOn (T p α) (T' p (α ∘ f))

/-- A masked class `R` operator for some special variable, or zero on the triangle. -/
@[expose] def MR0 (θ A N : ℝ) (S : Set V) (T : P → (V → ℝ) → ℝ → ℝ → ℂ) : Prop :=
  (∃ v₀, MR θ A N S v₀ T) ∨ (0 ≤ N ∧ ∀ p α, KEqOn (T p α) fun _ _ => 0)

/-- **Masked class `J` plus class `R`** in the variables `S` (DH21: "the sum of an operator of class
`J` and an operator of class `R`"), with total norm at most `N`. -/
@[expose] def MJR (θ A N : ℝ) (S : Set V) (T : P → (V → ℝ) → ℝ → ℝ → ℂ) : Prop :=
  ∃ (NJ NR : ℝ) (TJ TR : P → (V → ℝ) → ℝ → ℝ → ℂ), MJ θ A NJ S TJ ∧ MR0 θ A NR S TR ∧
    NJ + NR ≤ N ∧ ∀ p α, KEqOn (T p α) fun t s => TJ p α t s + TR p α t s

end Defs

section Basic

variable {P : Type*} [MeasurableSpace P] {V : Type} {θ A N N' : ℝ} {S : Set V}
variable {T T' : P → (V → ℝ) → ℝ → ℝ → ℂ}

theorem MJ.nonneg (h : MJ θ A N S T) : 0 ≤ N := by
  obtain ⟨ι, _, f, -, -, U, hU, -⟩ := h
  exact hU.nonneg

theorem MR.nonneg {v₀ : V} (h : MR θ A N S v₀ T) : 0 ≤ N := by
  obtain ⟨ι, _, f, -, -, -, U, hU, -⟩ := h
  exact hU.nonneg

theorem MR0.nonneg (h : MR0 θ A N S T) : 0 ≤ N := by
  rcases h with ⟨v₀, h⟩ | ⟨h, -⟩
  · exact h.nonneg
  · exact h

theorem MJR.nonneg (h : MJR θ A N S T) : 0 ≤ N := by
  obtain ⟨NJ, NR, TJ, TR, hJ, hR, hN, -⟩ := h
  exact (add_nonneg hJ.nonneg hR.nonneg).trans hN

theorem MJ.mono (h : MJ θ A N S T) (hN : N ≤ N') : MJ θ A N' S T := by
  obtain ⟨ι, _, f, hf, hr, U, hU, he⟩ := h
  exact ⟨ι, inferInstance, f, hf, hr, U, hU.mono hN, he⟩

theorem MR.mono {v₀ : V} (h : MR θ A N S v₀ T) (hN : N ≤ N') : MR θ A N' S v₀ T := by
  obtain ⟨ι, _, f, hf, hr, h0, U, hU, he⟩ := h
  exact ⟨ι, inferInstance, f, hf, hr, h0, U, hU.mono hN, he⟩

theorem MJR.mono (h : MJR θ A N S T) (hN : N ≤ N') : MJR θ A N' S T := by
  obtain ⟨NJ, NR, TJ, TR, hJ, hR, hN', he⟩ := h
  exact ⟨NJ, NR, TJ, TR, hJ, hR, hN'.trans hN, he⟩

theorem MJ.congr (h : MJ θ A N S T) (he : ∀ p α, KEqOn (T' p α) (T p α)) : MJ θ A N S T' := by
  obtain ⟨ι, _, f, hf, hr, U, hU, he'⟩ := h
  exact ⟨ι, inferInstance, f, hf, hr, U, hU, fun p α => (he p α).trans (he' p α)⟩

theorem MR.congr {v₀ : V} (h : MR θ A N S v₀ T) (he : ∀ p α, KEqOn (T' p α) (T p α)) :
    MR θ A N S v₀ T' := by
  obtain ⟨ι, _, f, hf, hr, h0, U, hU, he'⟩ := h
  exact ⟨ι, inferInstance, f, hf, hr, h0, U, hU, fun p α => (he p α).trans (he' p α)⟩

theorem MJR.congr (h : MJR θ A N S T) (he : ∀ p α, KEqOn (T' p α) (T p α)) :
    MJR θ A N S T' := by
  obtain ⟨NJ, NR, TJ, TR, hJ, hR, hN, he'⟩ := h
  exact ⟨NJ, NR, TJ, TR, hJ, hR, hN, fun p α => (he p α).trans (he' p α)⟩

/-- The zero operator in the variables of a masked class `J` operator. -/
theorem MJ.zero_of (h : MJ θ A N S T) : MJ θ A 0 S (fun (_ : P) (_ : V → ℝ) (_ _ : ℝ) => (0 : ℂ)) := by
  obtain ⟨ι, _, f, hf, hr, U, -, -⟩ := h
  exact ⟨ι, inferInstance, f, hf, hr, _, ClassJP.zero, fun _ _ => KEqOn.refl _⟩

/-- The zero operator in the variables of a masked class `R` operator, as a class `J` operator. -/
theorem MR.zero_of {v₀ : V} (h : MR θ A N S v₀ T) : MJ θ A 0 S (fun (_ : P) (_ : V → ℝ) (_ _ : ℝ) => (0 : ℂ)) := by
  obtain ⟨ι, _, f, hf, hr, -, U, -, -⟩ := h
  exact ⟨Option ι, inferInstance, f, hf, hr, _, ClassJP.zero, fun _ _ => KEqOn.refl _⟩

theorem MJR.of_MJ (h : MJ θ A N S T) : MJR θ A N S T :=
  ⟨N, 0, T, (fun (_ : P) (_ : V → ℝ) (_ _ : ℝ) => (0 : ℂ)), h, Or.inr ⟨le_rfl, fun _ _ => KEqOn.refl _⟩, by simp,
    fun p α t s _ _ _ => by simp⟩

theorem MJR.of_MR {v₀ : V} (h : MR θ A N S v₀ T) : MJR θ A N S T :=
  ⟨0, N, (fun (_ : P) (_ : V → ℝ) (_ _ : ℝ) => (0 : ℂ)), T, h.zero_of, Or.inl ⟨v₀, h⟩, by simp, fun p α t s _ _ _ => by simp⟩

theorem MJ.exists_rep (h : MJ θ A N S T) (p : P) (α : V → ℝ) :
    ∃ K : ℝ → ℝ → ℂ, (Continuous fun q : ℝ × ℝ => K q.1 q.2) ∧ KEqOn (T p α) K := by
  obtain ⟨ι, _, f, -, -, U, hU, he⟩ := h
  obtain ⟨K, hK, hKe⟩ := hU.exists_rep p (α ∘ f)
  exact ⟨K, hK, (he p α).trans hKe⟩

theorem MR0.exists_rep (h : MR0 θ A N S T) (p : P) (α : V → ℝ) :
    ∃ K : ℝ → ℝ → ℂ, (Continuous fun q : ℝ × ℝ => K q.1 q.2) ∧ KEqOn (T p α) K := by
  rcases h with ⟨v₀, ι, _, f, -, -, -, U, hU, he⟩ | ⟨-, hz⟩
  · obtain ⟨K, hK, hKe⟩ := hU.exists_rep p (α ∘ f)
    exact ⟨K, hK, (he p α).trans hKe⟩
  · exact ⟨fun _ _ => 0, continuous_const, hz p α⟩

/-- An equivalence of the index types of two injections with the same range. -/
theorem exists_equiv_of_range_eq {ι₁ ι₂ : Type} {f₁ : ι₁ → V} {f₂ : ι₂ → V}
    (hf₁ : Function.Injective f₁) (hf₂ : Function.Injective f₂) (hr : Set.range f₂ = Set.range f₁) :
    ∃ e : ι₂ ≃ ι₁, ∀ i, f₁ (e i) = f₂ i := by
  refine ⟨(Equiv.ofInjective f₂ hf₂).trans ((Set.equivOfEq hr).trans
    (Equiv.ofInjective f₁ hf₁).symm), fun i => ?_⟩
  simp only [Equiv.trans_apply]
  rw [Equiv.apply_ofInjective_symm hf₁]
  rfl

/-- **Sums of masked class `J` operators** in the same variables. -/
theorem MJ.add {N₁ N₂ : ℝ} {T₁ T₂ : P → (V → ℝ) → ℝ → ℝ → ℂ} (h₁ : MJ θ A N₁ S T₁)
    (h₂ : MJ θ A N₂ S T₂) : MJ θ A (N₁ + N₂) S fun p α t s => T₁ p α t s + T₂ p α t s := by
  obtain ⟨ι₁, _, f₁, hf₁, hr₁, U₁, hU₁, he₁⟩ := h₁
  obtain ⟨ι₂, _, f₂, hf₂, hr₂, U₂, hU₂, he₂⟩ := h₂
  obtain ⟨e, hfe⟩ := exists_equiv_of_range_eq hf₁ hf₂ (hr₂.trans hr₁.symm)
  refine ⟨ι₁, inferInstance, f₁, hf₁, hr₁, _, hU₁.add (hU₂.reindex e), fun p α => ?_⟩
  have hα : (fun i => (α ∘ f₁) (e i)) = α ∘ f₂ := funext fun i => by simp [hfe]
  intro t s h0 h1 h2
  simp only
  rw [he₁ p α t s h0 h1 h2, he₂ p α t s h0 h1 h2, hα]

/-- **Sums of masked class `R` operators** with the same variables and special variable. -/
theorem MR.add {N₁ N₂ : ℝ} {v₀ : V} {T₁ T₂ : P → (V → ℝ) → ℝ → ℝ → ℂ}
    (h₁ : MR θ A N₁ S v₀ T₁) (h₂ : MR θ A N₂ S v₀ T₂) :
    MR θ A (N₁ + N₂) S v₀ fun p α t s => T₁ p α t s + T₂ p α t s := by
  obtain ⟨ι₁, _, f₁, hf₁, hr₁, h01, U₁, hU₁, he₁⟩ := h₁
  obtain ⟨ι₂, _, f₂, hf₂, hr₂, h02, U₂, hU₂, he₂⟩ := h₂
  obtain ⟨E, hfE⟩ := exists_equiv_of_range_eq hf₁ hf₂ (hr₂.trans hr₁.symm)
  have hE0 : E none = none := hf₁ ((hfE none).trans (h02.trans h01.symm))
  have hEs : ∀ i, ∃ x', E (some i) = some x' := fun i => by
    rcases h : E (some i) with _ | x'
    · exact absurd (E.injective (h.trans hE0.symm)) (Option.some_ne_none i)
    · exact ⟨x', rfl⟩
  set e : ι₂ ≃ ι₁ := Equiv.removeNone E
  have hmap : ∀ o, Option.map e o = E o := fun o => by
    rcases o with _ | i
    · simp [hE0]
    · exact Equiv.removeNone_some E (hEs i)
  refine ⟨ι₁, inferInstance, f₁, hf₁, hr₁, h01, _, hU₁.add (hU₂.reindex e), fun p α => ?_⟩
  have hα : (fun o => (α ∘ f₁) (Option.map e o)) = α ∘ f₂ := funext fun o => by
    simp [hmap, hfE]
  intro t s h0 h1 h2
  simp only
  rw [he₁ p α t s h0 h1 h2, he₂ p α t s h0 h1 h2, hα]

end Basic

end WaveTurbulence.ClassJR
