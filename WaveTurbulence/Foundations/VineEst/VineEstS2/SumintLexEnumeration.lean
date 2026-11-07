/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9ShapeSlots
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Data.Finset.Sort

/-! # Increasing enumeration of the exact frozen sumint row order -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2

def rowKey (S : SumintShape) (v : S.VIdx) : ℕ ×ₗ ℕ := toLex (v.1.val,v.2.val)

theorem rowKey_injective (S : SumintShape) : Function.Injective (rowKey S) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ h
  have hh : (i.val,j.val) = (k.val,l.val) := congrArg ofLex h
  have hi : i = k := Fin.ext (congrArg Prod.fst hh)
  subst k
  exact congrArg (Sigma.mk i) (Fin.ext (congrArg Prod.snd hh))

noncomputable abbrev rowOrder (S : SumintShape) : LinearOrder S.VIdx :=
  LinearOrder.lift' (rowKey S) (rowKey_injective S)

/-- Unlike an arbitrary cardinality bijection, this enumeration is
increasing for exactly TARGET's block-then-slot predecessor relation. -/
noncomputable def sumintRowEnumeration (S : SumintShape) : Fin S.M ≃ S.VIdx :=
  (@Fintype.orderIsoFinOfCardEq S.VIdx (rowOrder S) _ S.M (Sumint.card_vector_index S)).toEquiv

theorem sumintRowEnumeration_lt (S : SumintShape) {i j : Fin S.M} (h : i < j) :
    S.LexLt (sumintRowEnumeration S i) (sumintRowEnumeration S j) := by
  have hh := (@OrderIso.lt_iff_lt (Fin S.M) S.VIdx inferInstance
    (rowOrder S).toPartialOrder.toPreorder
    (@Fintype.orderIsoFinOfCardEq S.VIdx (rowOrder S) _ S.M (Sumint.card_vector_index S)) i j).mpr h
  rcases Prod.Lex.toLex_lt_toLex.mp hh with hfirst | ⟨heq,hlast⟩
  · exact Or.inl hfirst
  · exact Or.inr ⟨Fin.ext heq,hlast⟩

end WaveTurbulence.VineEstS2
