/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamInsertedRungDecoder
public import WaveTurbulenceVineParam.VineParamAnchoredRepresentatives
import Mathlib.Tactic

/-! # Complete integer decoder coefficients after an actual rung insertion -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
variable {V β ι : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- Every actual new bond has one fixed affine decoder row. Cut reflection
only selects which of the two old rail rows supplies the following rail. -/
@[expose] def insertedDecoderFree (anchor : Bool) (A : β → ι → ℤ) :
    SpliceEdge G.i G.j → (ι ⊕ Fin 2 → ℤ)
  | .inl e => insertedRestFree G.pattern anchor (G.inside e) (A e.1)
  | .inr j => ![
      insertedRestFree G.pattern anchor false (A G.i),
      insertedRestFree G.pattern anchor false (A G.j),
      insertedRungFree G.pattern anchor 0 (A G.j),
      insertedRungFree G.pattern anchor 1 (A G.j),
      insertedRestFree G.pattern anchor true (A (if G.pattern.reversesPorts then G.j else G.i)),
      insertedRestFree G.pattern anchor true (A (if G.pattern.reversesPorts then G.i else G.j))] j

/-- The complete gap column is integral, with no magnitude restriction. -/
@[expose] def insertedDecoderGap (anchor : Bool) (D : β → ℤ) (ε : ℤ) : SpliceEdge G.i G.j → ℤ
  | .inl e => insertedRestGap G.pattern anchor (G.inside e) (D e.1) ε
  | .inr j => ![
      insertedRestGap G.pattern anchor false (D G.i) ε,
      insertedRestGap G.pattern anchor false (D G.j) ε,
      insertedRungGap G.pattern anchor 0 (D G.j) ε,
      insertedRungGap G.pattern anchor 1 (D G.j) ε,
      insertedRestGap G.pattern anchor true (D (if G.pattern.reversesPorts then G.j else G.i)) ε,
      insertedRestGap G.pattern anchor true (D (if G.pattern.reversesPorts then G.i else G.j)) ε] j

/-- Every free coefficient of every actual new label is still ternary. -/
theorem insertedDecoderFree_unit (anchor : Bool) (A : β → ι → ℤ)
    (hA : ∀ e i,A e i ∈ ({-1,0,1} : Finset ℤ)) :
    ∀ e i,G.insertedDecoderFree anchor A e i ∈ ({-1,0,1} : Finset ℤ) := by
  intro e i
  cases e with
  | inl e => exact insertedRestFree_unit G.pattern anchor (G.inside e) (A e.1) (hA e.1) i
  | inr j =>
    fin_cases j
    · exact insertedRestFree_unit G.pattern anchor false (A G.i) (hA G.i) i
    · exact insertedRestFree_unit G.pattern anchor false (A G.j) (hA G.j) i
    · exact insertedRungFree_unit G.pattern anchor 0 (A G.j) (hA G.j) i
    · exact insertedRungFree_unit G.pattern anchor 1 (A G.j) (hA G.j) i
    · exact insertedRestFree_unit G.pattern anchor true _ (hA _) i
    · exact insertedRestFree_unit G.pattern anchor true _ (hA _) i

/-- The physical reference column remains exactly -1 on all labels. -/
theorem insertedDecoderFree_reference (anchor : Bool) (A : β → ι → ℤ) (ref : ι)
    (href : ∀ e,A e ref= -1) : ∀ e,G.insertedDecoderFree anchor A e (.inl ref)= -1 := by
  intro e
  cases e with
  | inl e => exact href e.1
  | inr j =>
    fin_cases j
    all_goals change A _ ref= -1
    all_goals exact href _

end WaveTurbulence.Vine.Param.RungSpliceGeometry
