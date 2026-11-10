/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCProd

/-!
# Measure-preserving reorderings of product spaces

The coefficients of DH21 Proposition 5.1 are integrals over products of auxiliary variables. The
order in which these variables appear differs between the product estimates (`kprod`, the couplings)
and the final pushforward to the frequency variables `(λ₁, λ₂)` (`pushSym`). This file gives the
volume-preserving reorderings:
* `mswap : (A × B) × (C × D) ≃ (A × C) × (B × D)`;
* `frontSwap : A × (Z × T) ≃ Z × (A × T)`.
-/

public section

open MeasureTheory Set Filter Finset
open scoped ENNReal

namespace WaveTurbulence.ClassJR

section Reorder

variable {A B C D Z T : Type*} [MeasureSpace A] [MeasureSpace B] [MeasureSpace C] [MeasureSpace D]
  [MeasureSpace Z] [MeasureSpace T]

/-- `A × (Z × T) ≃ Z × (A × T)`. -/
@[expose] def frontSwap : A × (Z × T) ≃ᵐ Z × (A × T) :=
  (MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodComm).prodCongr (MeasurableEquiv.refl T))).trans
    MeasurableEquiv.prodAssoc

theorem frontSwap_apply (p : A × (Z × T)) : frontSwap p = (p.2.1, (p.1, p.2.2)) := rfl

theorem measurePreserving_frontSwap [SFinite (volume : Measure A)] [SFinite (volume : Measure Z)]
    [SFinite (volume : Measure T)] :
    MeasurePreserving (frontSwap : A × (Z × T) ≃ᵐ Z × (A × T)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm : A × (Z × T) ≃ᵐ (A × Z) × T) :=
    volume_preserving_prodAssoc.symm _
  have h2 : MeasurePreserving ((MeasurableEquiv.prodComm).prodCongr (MeasurableEquiv.refl T) :
      (A × Z) × T ≃ᵐ (Z × A) × T) :=
    (Measure.measurePreserving_swap (μ := (volume : Measure A))
      (ν := (volume : Measure Z))).prod (MeasurePreserving.id (volume : Measure T))
  have h3 : MeasurePreserving (MeasurableEquiv.prodAssoc : (Z × A) × T ≃ᵐ Z × (A × T)) :=
    volume_preserving_prodAssoc
  exact (h3.comp h2).comp h1

/-- `(A × B) × (C × D) ≃ (A × C) × (B × D)`. -/
@[expose] def mswap : (A × B) × (C × D) ≃ᵐ (A × C) × (B × D) :=
  (MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl A).prodCongr
    (frontSwap : B × (C × D) ≃ᵐ C × (B × D)))).trans MeasurableEquiv.prodAssoc.symm

theorem measurePreserving_mswap [SFinite (volume : Measure A)] [SFinite (volume : Measure B)]
    [SFinite (volume : Measure C)] [SFinite (volume : Measure D)] :
    MeasurePreserving (mswap : (A × B) × (C × D) ≃ᵐ (A × C) × (B × D)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc : (A × B) × (C × D) ≃ᵐ A × (B × (C × D))) :=
    volume_preserving_prodAssoc
  have h2 : MeasurePreserving ((MeasurableEquiv.refl A).prodCongr
      (frontSwap : B × (C × D) ≃ᵐ C × (B × D))) :=
    (MeasurePreserving.id (volume : Measure A)).prod measurePreserving_frontSwap
  have h3 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm : A × (C × (B × D)) ≃ᵐ (A × C) × (B × D)) :=
    volume_preserving_prodAssoc.symm _
  exact (h3.comp h2).comp h1

end Reorder

end WaveTurbulence.ClassJR
