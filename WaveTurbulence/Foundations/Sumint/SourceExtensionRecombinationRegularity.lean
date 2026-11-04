/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceExtensionFiniteRank

/-!
# Joint regularity needed for spatial Fourier recombination

Finite rank gives genuine product integrability against every integrable
spatial coefficient and measurable unit-bounded external character.
-/

public section
open MeasureTheory
namespace WaveTurbulence.Sumint

/-- Joint measurability of the actual extension in its independent input frequencies and time. -/
theorem measurable_weightedSourceExtension_joint {α : Type*} [MeasurableSpace α]
    {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I) (N : ℕ) (h : ℝ)
    {L : ℝ} (hL : 0 < L) (γ δ η : ℝ) (hη : η ≤ 1/3)
    (p : D.S.VIdx → Fin d → ℝ) (ν : α → D.S.VIdx → Mom d) (hν : Measurable ν) (r : Mom d) :
    Measurable (fun q : α × (Fin 3 → ℝ) => weightedSourceExtension D hI N h L γ δ η p (ν q.1) r q.2) := by
  simp_rw [weightedSourceExtension_eq_sum D hI N h hL γ δ η hη]
  apply Finset.measurable_sum
  intro x _
  have hfst : Measurable (Prod.fst : α × (Fin 3 → ℝ) → α) := measurable_fst
  have hsnd : Measurable (Prod.snd : α × (Fin 3 → ℝ) → (Fin 3 → ℝ)) := measurable_snd
  have hc := ((continuous_inputCharacter D L x).measurable.comp hν).comp hfst
  have ht := (measurable_phaseCellExtension D hI N h L γ δ η x r).comp hsnd
  exact ((measurable_const.mul measurable_const).mul hc).mul ht

/-- Every independent input-frequency slice satisfies genuine time integrability. -/
theorem integrable_weightedSourceExtension {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (N : ℕ) (h : ℝ) {L : ℝ} (hL : 0 < L) (γ δ η : ℝ) (hη : η ≤ 1/3)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) :
    Integrable (weightedSourceExtension D hI N h L γ δ η p ν r) := by
  have he := funext (weightedSourceExtension_eq_sum D hI N h hL γ δ η hη p ν r)
  rw [he]
  apply integrable_finsetSum
  intro x _
  exact (integrable_phaseCellExtension D hI N h L γ δ η hη x r).const_mul _

/-- Product integrability against a spatial coefficient and bounded external modulation. -/
theorem integrable_coefficient_weightedSourceExtension {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (N : ℕ) (h : ℝ) {L : ℝ} (hL : 0 < L) (γ δ η : ℝ) (hη : η ≤ 1/3)
    (p : D.S.VIdx → Fin d → ℝ) (ν : α → D.S.VIdx → Mom d) (hν : Measurable ν)
    (r : Mom d) (C χ : α → ℂ) (hC : Integrable C μ) (hχ : Measurable χ)
    (hχnorm : ∀ a, ‖χ a‖ ≤ 1) :
    Integrable (fun q : α × (Fin 3 → ℝ) => C q.1*χ q.1*
      weightedSourceExtension D hI N h L γ δ η p (ν q.1) r q.2) (μ.prod volume) := by
  let W : ℂ := ((sourceWeightDecay D L γ η*
    ‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card : ℝ):ℂ)
  have hχC := hC.mul_bdd hχ.aestronglyMeasurable (ae_of_all _ hχnorm)
  have hchar (x : D.S.VIdx → Fin d → ℤ) :
      Integrable (fun a => C a*χ a*inputCharacter D L (ν a) x) μ :=
    hχC.mul_bdd ((continuous_inputCharacter D L x).measurable.comp hν).aestronglyMeasurable
      (ae_of_all _ (fun a => (norm_inputCharacter D L (ν a) x).le))
  have he : (fun q : α × (Fin 3 → ℝ) => C q.1*χ q.1*
      weightedSourceExtension D hI N h L γ δ η p (ν q.1) r q.2) =
      fun q => ∑ x ∈ inputCutoffBox L p,
        (C q.1*χ q.1*inputCharacter D L (ν q.1) x *
          (W*((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ):ℂ))) *
          phaseCellExtension D hI N h L γ δ η x r q.2 := by
    funext q
    rw [weightedSourceExtension_eq_sum D hI N h hL γ δ η hη,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [W]
    ring
  rw [he]
  apply integrable_finsetSum
  intro x _
  exact ((hchar x).mul_const _).mul_prod
    (integrable_phaseCellExtension D hI N h L γ δ η hη x r)

end WaveTurbulence.Sumint
