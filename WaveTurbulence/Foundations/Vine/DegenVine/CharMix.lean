/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.SumintDatum

public import WaveTurbulence.Frozen.Defs.SumintDatumAdmissible

public import WaveTurbulence.Frozen.Defs.SumintDatumEllVec

public import WaveTurbulence.Frozen.Defs.SumintDatumExpr

public import WaveTurbulence.Frozen.Defs.SumintDatumKVec

public import WaveTurbulence.Frozen.Defs.SumintDatumM0

public import WaveTurbulence.Frozen.Defs.SumintDatumM1

public import WaveTurbulence.Frozen.Defs.SumintDatumPhase

public import WaveTurbulence.Frozen.Defs.SumintDatumTimeDom

public import WaveTurbulence.Frozen.Defs.SumintShape

public import WaveTurbulence.Frozen.Defs.SumintShapeLexLt

public import WaveTurbulence.Frozen.Defs.SumintShapeM

public import WaveTurbulence.Frozen.Defs.SumintShapeN

public import WaveTurbulence.Frozen.Defs.SumintShapeTVar

public import WaveTurbulence.Frozen.Defs.SumintShapeUSlot

public import WaveTurbulence.Frozen.Defs.SumintShapeVIdx

public import WaveTurbulence.Frozen.Defs.SumintShapeX0Slot

public import WaveTurbulence.Frozen.Defs.SumintShapeXSlot

public import WaveTurbulence.Frozen.Defs.SumintShapeYSlot

public import WaveTurbulence.Frozen.Defs.WTPrefixA

public import WaveTurbulence.Frozen.Defs.EpsCoef

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import Mathlib.Analysis.Fourier.FourierTransform

/-! # Character mixtures: bounded multipliers of the lattice sum (DEGEN-VINE)

A *character mixture* on the input lattice of a `sumint` datum is a multiplier
`m(E, x) = ∫ u(a, E) · ∏ᵥ e^{2πi⟨ζ(a)ᵥ, Xᵥ⟩} dμ(a)` with a finite measure `μ`, a measurable family of input
frequencies `ζ`, and unimodular-bounded output-dependent scalars `u`.  The indicator of an affine lattice
constraint `y(x, E) = 0` is a mixture of mass `1` (Fourier inversion on `ℤ_L^d`); products of mixtures are
mixtures, with multiplied masses.  Because the `sumint` kernel estimate is uniform in the input modulation
(`SumintSigned.exists_source_static_power_bound`), a sum weighted by a mixture of mass `K` obeys the `sumint`
bound with the constant multiplied by `K`; see `DegenVine.MixRecomb`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.DegenVine
open WaveTurbulence MeasureTheory

variable {d : ℕ}

/-- The input character with frequencies `ν` at the lattice inputs `x` (shape version of `inputCharacter`). -/
noncomputable def charOf (S : SumintShape) (L : ℝ) (ν : S.VIdx → Mom d) (x : S.VIdx → Fin d → ℤ) : ℂ :=
  ∏ v, (Real.fourierChar (inner ℝ (ν v) (latticePoint L (x v))) : ℂ)

/-- A character mixture on the input lattice of a `sumint` shape. -/
structure CharMix (S : SumintShape) (d : ℕ) where
  α : Type
  [mα : MeasurableSpace α]
  μ : Measure α
  [hμ : IsFiniteMeasure μ]
  ζ : α → S.VIdx → Mom d
  hζ : Measurable ζ
  u : α → (Fin 4 → Mom d) → ℂ
  hu : ∀ E, Measurable fun a => u a E
  hu1 : ∀ a E, ‖u a E‖ ≤ 1

attribute [instance] CharMix.mα CharMix.hμ

namespace CharMix
variable {S : SumintShape} (M : CharMix S d)

/-- The multiplier. -/
noncomputable def val (L : ℝ) (E : Fin 4 → Mom d) (x : S.VIdx → Fin d → ℤ) : ℂ :=
  ∫ a, M.u a E * charOf S L (M.ζ a) x ∂M.μ

/-- The mass. -/
noncomputable def mass : ℝ := M.μ.real Set.univ

theorem mass_nonneg : 0 ≤ M.mass := measureReal_nonneg

theorem norm_charOf (L : ℝ) (ν : S.VIdx → Mom d) (x : S.VIdx → Fin d → ℤ) :
    ‖charOf S L ν x‖ = 1 := by
  simp only [charOf, norm_prod, Circle.norm_coe, Finset.prod_const_one]

theorem continuous_charOf (L : ℝ) (x : S.VIdx → Fin d → ℤ) :
    Continuous fun ν : S.VIdx → Mom d => charOf S L ν x := by
  unfold charOf
  refine continuous_finset_prod _ fun v _ => ?_
  exact (continuous_subtype_val.comp Real.continuous_fourierChar).comp
    ((continuous_id.inner continuous_const).comp (continuous_apply v))

theorem measurable_char (L : ℝ) (x : S.VIdx → Fin d → ℤ) :
    Measurable fun a => charOf S L (M.ζ a) x :=
  (continuous_charOf L x).measurable.comp M.hζ

theorem norm_integrand_le (L : ℝ) (E : Fin 4 → Mom d) (x : S.VIdx → Fin d → ℤ) (a : M.α) :
    ‖M.u a E * charOf S L (M.ζ a) x‖ ≤ 1 := by
  rw [norm_mul, norm_charOf, mul_one]; exact M.hu1 a E

theorem integrable_integrand (L : ℝ) (E : Fin 4 → Mom d) (x : S.VIdx → Fin d → ℤ) :
    Integrable (fun a => M.u a E * charOf S L (M.ζ a) x) M.μ :=
  Integrable.of_bound ((M.hu E).mul (M.measurable_char L x)).aestronglyMeasurable 1
    (ae_of_all _ (M.norm_integrand_le L E x))

theorem norm_val_le (L : ℝ) (E : Fin 4 → Mom d) (x : S.VIdx → Fin d → ℤ) :
    ‖M.val L E x‖ ≤ M.mass := by
  unfold val mass
  refine (norm_integral_le_of_norm_le_const (ae_of_all _ (M.norm_integrand_le L E x))).trans ?_
  simp [Measure.real]

end CharMix

/-- Additivity of input characters. -/
theorem charOf_add (S : SumintShape) (L : ℝ) (ν ν' : S.VIdx → Mom d) (x : S.VIdx → Fin d → ℤ) :
    charOf S L (ν + ν') x = charOf S L ν x * charOf S L ν' x := by
  unfold charOf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [Pi.add_apply, inner_add_left]
  rw [← Circle.coe_mul]
  congr 1
  exact AddChar.map_add_eq_mul _ _ _

end WaveTurbulence.DegenVine
