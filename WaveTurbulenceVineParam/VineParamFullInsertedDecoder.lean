/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNewRungDecoder
import Mathlib.Tactic

/-! # The complete explicit integer decoder is the actual full source inverse -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset
variable {V β ι E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
  [DecidableEq ι] [Fintype ι] [AddCommGroup E]
variable (G : RungSpliceGeometry V β)

/-- A previously proved physical integer decoder lifts to every actual new
bond with the explicit complete coefficients. Together with the unit and
reference-column lemmas, this is the affine part of the one-rung chart lift. -/
theorem full_inserted_decoder_of_old
    (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b) (g r : E)
    (old : DirectedRootFiber G.ends a b r ≃ (ι → E)) (ref : ι) (anchor : Bool)
    (A : β → ι → ℤ) (D : β → ℤ) (href : ∀ e,A e ref= -1)
    (hdecode : ∀ z e,(old.symm z).1 e=g+(∑ i,A e i • z i)+D e • r)
    (x : ι ⊕ Fin 2 → E) (e : SpliceEdge G.i G.j) :
    ((G.anchoredInsertionChart a b hab ha hb r old ref anchor).symm x).1 e=
      g+(∑ i,G.insertedDecoderFree anchor A e i • x i)+
        G.insertedDecoderGap anchor D (G.gapSign a b) e • r := by
  cases e with
  | inl e =>
    have h := G.representative_decoder_of_old a b hab ha hb g r old ref anchor A D href hdecode x
      e.1 (G.inside e) (fun _ _ => rfl)
    rw [G.representative_rest e.1 e.2.1 e.2.2] at h
    exact h
  | inr j =>
    fin_cases j
    · have h := G.representative_decoder_of_old a b hab ha hb g r old ref anchor A D href hdecode x
        G.i false (by intro hi; exact (hi rfl).elim)
      rw [G.representative_first] at h
      exact h
    · have h := G.representative_decoder_of_old a b hab ha hb g r old ref anchor A D href hdecode x
        G.j false (by intro _ hj; exact (hj rfl).elim)
      rw [G.representative_second] at h
      exact h
    · exact G.new_rung_decoder_of_old a b hab ha hb g r old ref anchor A D href hdecode x 0
    · exact G.new_rung_decoder_of_old a b hab ha hb g r old ref anchor A D href hdecode x 1
    · cases hr : G.pattern.reversesPorts
      · have h := G.representative_decoder_of_old a b hab ha hb g r old ref anchor A D href hdecode x
          G.i true (by intro hi; exact (hi rfl).elim)
        rw [G.representative_first] at h
        simp only [hr,Bool.false_eq_true,ite_false,ite_true] at h
        change _=g+(∑ i,insertedRestFree G.pattern anchor true
          (A (if G.pattern.reversesPorts then G.j else G.i)) i • x i)+
          insertedRestGap G.pattern anchor true
            (D (if G.pattern.reversesPorts then G.j else G.i)) (G.gapSign a b) • r
        rw [hr]
        exact h
      · have h := G.representative_decoder_of_old a b hab ha hb g r old ref anchor A D href hdecode x
          G.j true (by intro _ hj; exact (hj rfl).elim)
        rw [G.representative_second] at h
        simp only [hr,ite_true] at h
        change _=g+(∑ i,insertedRestFree G.pattern anchor true
          (A (if G.pattern.reversesPorts then G.j else G.i)) i • x i)+
          insertedRestGap G.pattern anchor true
            (D (if G.pattern.reversesPorts then G.j else G.i)) (G.gapSign a b) • r
        rw [hr]
        exact h
    · cases hr : G.pattern.reversesPorts
      · have h := G.representative_decoder_of_old a b hab ha hb g r old ref anchor A D href hdecode x
          G.j true (by intro _ hj; exact (hj rfl).elim)
        rw [G.representative_second] at h
        simp only [hr,Bool.false_eq_true,ite_false,ite_true] at h
        change _=g+(∑ i,insertedRestFree G.pattern anchor true
          (A (if G.pattern.reversesPorts then G.i else G.j)) i • x i)+
          insertedRestGap G.pattern anchor true
            (D (if G.pattern.reversesPorts then G.i else G.j)) (G.gapSign a b) • r
        rw [hr]
        exact h
      · have h := G.representative_decoder_of_old a b hab ha hb g r old ref anchor A D href hdecode x
          G.i true (by intro hi; exact (hi rfl).elim)
        rw [G.representative_first] at h
        simp only [hr,ite_true] at h
        change _=g+(∑ i,insertedRestFree G.pattern anchor true
          (A (if G.pattern.reversesPorts then G.i else G.j)) i • x i)+
          insertedRestGap G.pattern anchor true
            (D (if G.pattern.reversesPorts then G.i else G.j)) (G.gapSign a b) • r
        rw [hr]
        exact h

end WaveTurbulence.Vine.Param.RungSpliceGeometry
