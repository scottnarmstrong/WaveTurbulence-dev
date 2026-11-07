/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.DegenVine.CharMix

/-! # Algebra of character mixtures (DEGEN-VINE)

Constants, negation, sums and products of character mixtures: the values add / multiply, the masses add /
multiply (negation preserves the mass).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.DegenVine
open WaveTurbulence MeasureTheory

variable {d : ℕ} {S : SumintShape}

theorem meInl {α β : Type} [MeasurableSpace α] [MeasurableSpace β] :
    MeasurableEmbedding (Sum.inl : α → α ⊕ β) :=
  ⟨Sum.inl_injective, measurable_inl, fun s hs => by
    rw [measurableSet_sum_iff]
    refine ⟨?_, ?_⟩
    · rw [Set.preimage_image_eq _ Sum.inl_injective]; exact hs
    · have : (Sum.inr ⁻¹' (Sum.inl '' s) : Set β) = ∅ := by ext b; simp
      rw [this]; exact MeasurableSet.empty⟩

theorem meInr {α β : Type} [MeasurableSpace α] [MeasurableSpace β] :
    MeasurableEmbedding (Sum.inr : β → α ⊕ β) :=
  ⟨Sum.inr_injective, measurable_inr, fun s hs => by
    rw [measurableSet_sum_iff]
    refine ⟨?_, ?_⟩
    · have : (Sum.inl ⁻¹' (Sum.inr '' s) : Set α) = ∅ := by ext b; simp
      rw [this]; exact MeasurableSet.empty
    · rw [Set.preimage_image_eq _ Sum.inr_injective]; exact hs⟩

namespace CharMix

/-- The constant mixture `1`. -/
noncomputable def one (S : SumintShape) (d : ℕ) : CharMix S d where
  α := Unit
  μ := Measure.dirac ()
  ζ := fun _ _ => 0
  hζ := measurable_const
  u := fun _ _ => 1
  hu := fun _ => measurable_const
  hu1 := fun _ _ => by simp

theorem charOf_zero (L : ℝ) (x : S.VIdx → Fin d → ℤ) : charOf S L (fun _ => (0 : Mom d)) x = 1 := by
  unfold charOf
  simp

@[simp] theorem val_one (L : ℝ) (E : Fin 4 → Mom d) (x : S.VIdx → Fin d → ℤ) :
    (one S d).val L E x = 1 := by
  unfold val one
  simp [charOf_zero]

@[simp] theorem mass_one : (one S d).mass = 1 := by
  unfold mass one
  simp [Measure.real]

/-- Negation. -/
noncomputable def neg (M : CharMix S d) : CharMix S d :=
  { M with u := fun a E => - M.u a E, hu := fun E => (M.hu E).neg, hu1 := fun a E => by simpa using M.hu1 a E }

@[simp] theorem val_neg (M : CharMix S d) (L : ℝ) (E : Fin 4 → Mom d) (x : S.VIdx → Fin d → ℤ) :
    (neg M).val L E x = - M.val L E x := by
  unfold val neg
  simp only [neg_mul]
  exact integral_neg _

@[simp] theorem mass_neg (M : CharMix S d) : (neg M).mass = M.mass := rfl

/-- Product. -/
noncomputable def mul (M N : CharMix S d) : CharMix S d where
  α := M.α × N.α
  μ := M.μ.prod N.μ
  ζ := fun q => M.ζ q.1 + N.ζ q.2
  hζ := (M.hζ.comp measurable_fst).add (N.hζ.comp measurable_snd)
  u := fun q E => M.u q.1 E * N.u q.2 E
  hu := fun E => ((M.hu E).comp measurable_fst).mul ((N.hu E).comp measurable_snd)
  hu1 := fun q E => by
    rw [norm_mul]
    calc _ ≤ 1 * 1 := mul_le_mul (M.hu1 _ _) (N.hu1 _ _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

theorem val_mul (M N : CharMix S d) (L : ℝ) (E : Fin 4 → Mom d) (x : S.VIdx → Fin d → ℤ) :
    (mul M N).val L E x = M.val L E x * N.val L E x := by
  have h := integral_prod_mul (μ := M.μ) (ν := N.μ)
    (fun a => M.u a E * charOf S L (M.ζ a) x) (fun b => N.u b E * charOf S L (N.ζ b) x)
  unfold val mul
  rw [h.symm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  show M.u q.1 E * N.u q.2 E * charOf S L (M.ζ q.1 + N.ζ q.2) x =
    (M.u q.1 E * charOf S L (M.ζ q.1) x) * (N.u q.2 E * charOf S L (N.ζ q.2) x)
  rw [charOf_add]
  ring

theorem mass_mul (M N : CharMix S d) : (mul M N).mass = M.mass * N.mass := by
  unfold mass mul
  simp only [Measure.real]
  rw [show (Set.univ : Set (M.α × N.α)) = Set.univ ×ˢ Set.univ from Set.univ_prod_univ.symm,
    Measure.prod_prod, ENNReal.toReal_mul]

/-- Sum. -/
noncomputable def add (M N : CharMix S d) : CharMix S d where
  α := M.α ⊕ N.α
  μ := M.μ.map (Sum.inl : M.α → M.α ⊕ N.α) + N.μ.map (Sum.inr : N.α → M.α ⊕ N.α)
  hμ := by
    haveI : IsFiniteMeasure (M.μ.map (Sum.inl : M.α → M.α ⊕ N.α)) := Measure.isFiniteMeasure_map _ _
    haveI : IsFiniteMeasure (N.μ.map (Sum.inr : N.α → M.α ⊕ N.α)) := Measure.isFiniteMeasure_map _ _
    infer_instance
  ζ := Sum.elim M.ζ N.ζ
  hζ := M.hζ.sumElim N.hζ
  u := fun a E => Sum.elim (fun a => M.u a E) (fun b => N.u b E) a
  hu := fun E => (M.hu E).sumElim (N.hu E)
  hu1 := fun a E => by rcases a with a | b; exact M.hu1 a E; exact N.hu1 b E

theorem val_add (M N : CharMix S d) (L : ℝ) (E : Fin 4 → Mom d) (x : S.VIdx → Fin d → ℤ) :
    (add M N).val L E x = M.val L E x + N.val L E x := by
  unfold val add
  simp only
  rw [integral_add_measure]
  · rw [MeasurableEmbedding.integral_map meInl, MeasurableEmbedding.integral_map meInr]
    rfl
  · rw [MeasurableEmbedding.integrable_map_iff meInl]
    exact M.integrable_integrand L E x
  · rw [MeasurableEmbedding.integrable_map_iff meInr]
    exact N.integrable_integrand L E x

theorem mass_add (M N : CharMix S d) : (add M N).mass = M.mass + N.mass := by
  unfold mass add
  simp only [Measure.real, Measure.add_apply]
  rw [Measure.map_apply measurable_inl MeasurableSet.univ, Measure.map_apply measurable_inr MeasurableSet.univ]
  simp only [Set.preimage_univ]
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

end CharMix
end WaveTurbulence.DegenVine
