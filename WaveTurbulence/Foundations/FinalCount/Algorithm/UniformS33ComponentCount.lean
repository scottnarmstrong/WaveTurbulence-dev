/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33ComponentCount
public import WaveTurbulence.Foundations.FinalCount.AppBS33LeftCount
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformS33LeftTupleCount
public import WaveTurbulence.Foundations.FinalCount.AppBS33RightCount
public import WaveTurbulence.Foundations.FinalCount.AppBFiniteFiberSum
import Mathlib.Tactic

/-! # Sequential left--pair--right counting for 3S3-3G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
open scoped ENNReal
universe u v

/-- The right parameters are chosen after the internal pair. Independent
component projection tests are explicit in the post predicate. The sole
window loss is linear in the size of the left component. -/
theorem uniform_s33_component_countE_bound (d : ℕ) (hd : 2 ≤ d) (δ γ : ℝ)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.s33.pattern),
      AppbS33SplitGeometry M r → ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbS33LabelConditions M r L γ (min γ (1-γ)) w κ) →
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        (2*((appbS33Side r).card+1)+2 : ℕ)*
          ENNReal.ofReal (L^((d : ℝ)-γ-31*min γ (1-γ)/48))*
          (appbCountE (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L γ δ w
            (appbS33SeparatedPostAdmissibility r Adm) : ℝ≥0∞) := by
  classical
  obtain ⟨L₀,hL₀⟩ := uniform_s33_left_fixed_tuple_bound d hd δ γ hδ hγ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M r hg w Adm htest
  obtain ⟨p,hp⟩ := appbCountE_attained M hLp γ δ w Adm
  let T := (p.decorations_finite hLp γ δ w Adm).toFinset
  have hT : ∀ κ ∈ T,κ ∈ p.decorations L γ δ w Adm := fun κ hκ =>
    (p.decorations_finite hLp γ δ w Adm).mem_toFinset.mp hκ
  let Eleft : ℝ≥0∞ := appbCountE (appbS33LeftMolecule r hg) L γ δ w (appbS33LeftAdmissibility r Adm)
  let Eright : ℝ≥0∞ := appbCountE (appbS33RightMolecule r hg) L γ δ w (appbS33RightAdmissibility r Adm)
  let A := ENNReal.ofReal (L^((d : ℝ)-γ-31*min γ (1-γ)/48))
  let C : ℝ≥0∞ := (2*((appbS33Side r).card+1)+2 : ℕ)
  have hinner (ζ) :
      ((T.filter (fun κ => appbS33LeftLabels r κ = ζ)).card : ℝ≥0∞) ≤ A*Eright := by
    let U := T.filter (fun κ => appbS33LeftLabels r κ = ζ)
    have hU : (U.card : ℝ≥0∞) ≤ ((U.image r.localLabels).card : ℝ≥0∞)*Eright := by
      apply appb_finite_fiber_sum_le U r.localLabels Eright
      intro q hq
      have hb := appb_s33_right_fiber_card_le r hg L γ δ w p Adm q ζ
        (U.filter (fun κ => r.localLabels κ = q)) (by
          intro κ hκ
          obtain ⟨hU,hqκ⟩ := mem_filter.mp hκ
          obtain ⟨hκ,hζ⟩ := mem_filter.mp hU
          exact ⟨hT κ hκ,hqκ,hζ⟩)
      have hh := ENat.toENNReal_mono hb
      simpa only [ENat.toENNReal_coe] using hh
    have hQ := hL₀ V D L hL hLp M r hg p w Adm htest T hT ζ
    have hQ' : ((U.image r.localLabels).card : ℝ≥0∞) ≤ A := by
      have hh := ENNReal.ofReal_le_ofReal hQ
      simpa only [ENNReal.ofReal_natCast] using hh
    exact hU.trans (mul_le_mul_left hQ' Eright)
  have hout := appb_finite_fiber_sum_le T (appbS33LeftLabels r) (A*Eright) (fun ζ _ => hinner ζ)
  have hleft : ((T.image (appbS33LeftLabels r)).card : ℝ≥0∞) ≤ C*Eleft := by
    have hh := ENat.toENNReal_mono (appb_s33_left_image_count_le r hg hLp hδ.1 w p Adm T hT)
    with_reducible_and_instances
      simpa +instances only [ENNReal.instLE,ENNReal.instPartialOrder,C,Eleft,ENat.toENNReal_mul,ENat.toENNReal_add,ENat.toENNReal_coe,
      ENat.toENNReal_ofNat,ENat.toENNReal_one,Nat.cast_one,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh
  have hprod : Eleft*Eright ≤
      (appbCountE (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L γ δ w
        (appbS33SeparatedPostAdmissibility r Adm) : ℝ≥0∞) := by
    have hh := ENat.toENNReal_mono (appb_component_product_le
      (r.directedPostWithBond 3 5 ⟨1,by decide⟩) (appbS33Side r)
      (appb_s33_reinsert_closedSide M r (appb_s33_splitTopology_of_geometry hg) ⟨1,by decide⟩)
      hLp γ δ w (appbS33LeftAdmissibility r Adm) (appbS33RightAdmissibility r Adm))
    with_reducible_and_instances
      simpa +instances only [ENNReal.instLE,ENNReal.instPartialOrder,Eleft,Eright,appbS33LeftMolecule,appbS33RightMolecule,appbS33RightSide,
      appbS33SeparatedPostAdmissibility,ENat.toENNReal_mul] using hh
  have hc : (T.card : ℝ≥0∞) = (appbCountE M L γ δ w Adm : ℝ≥0∞) :=
    congrArg ENat.toENNReal ((p.decorations_finite hLp γ δ w Adm).encard_eq_coe_toFinset_card.symm.trans hp)
  rw [← hc]
  calc
    _ ≤ ((T.image (appbS33LeftLabels r)).card : ℝ≥0∞)*(A*Eright) := hout
    _ ≤ (C*Eleft)*(A*Eright) := mul_le_mul_left hleft _
    _ = (C*A)*(Eleft*Eright) := by ring
    _ ≤ _ := mul_le_mul_right hprod _

end WaveTurbulence.Mole.AppbAlgorithm
