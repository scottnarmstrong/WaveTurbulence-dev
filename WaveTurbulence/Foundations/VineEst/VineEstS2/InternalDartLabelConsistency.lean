/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.InternalBondLabels

/-! # Reconstructed bond labels are consistent at each actual garden node -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree
variable {V D : Type*} [DecidableEq V] [Fintype D]

noncomputable def internalDartMate (M : Molecule V D) (S : Finset V) (x : InternalDart M S) :
    InternalDart M S := ⟨M.mate x.1,(inGroup_mate M S x.1).mpr x.2⟩

theorem internalDartMate_bondDart (M : Molecule V D) (S : Finset V) (e : Bond M S) (s : Bool) :
    internalDartMate M S (internalBondDart M S (e,s)) = internalBondDart M S (e,!s) := by
  cases s
  · rfl
  · exact Subtype.ext (M.mate_mate e.1)

theorem internalDartValue_mate {E : Type*} (M : Molecule V D) (S : Finset V)
    (k : Bond M S → E) (x : InternalDart M S) :
    internalDartValue M S k (internalDartMate M S x) = internalDartValue M S k x := by
  obtain ⟨⟨e,s⟩,rfl⟩ := (internalBondDartEquiv M S).surjective x
  change internalDartValue M S k (internalDartMate M S (internalBondDart M S (e,s))) =
    internalDartValue M S k (internalBondDart M S (e,s))
  rw [internalDartMate_bondDart,internalDartValue_bondDart,internalDartValue_bondDart]

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}

/-- Different internal incidences at the same source node receive the same
label. PC incidences are the two mates; an LP node has a unique incidence. -/
theorem internalDartValue_eq_of_node_eq {E : Type*} (k : Bond G.molecule U → E)
    (x y : InternalDart G.molecule U) (he : Mole.dartNode G x.1 = Mole.dartNode G y.1) :
    internalDartValue G.molecule U k x = internalDartValue G.molecule U k y := by
  rcases x with ⟨x,hx⟩
  rcases y with ⟨y,hy⟩
  rcases x with ⟨c,s⟩ | ℓ
  · rcases y with ⟨d,t⟩ | l
    · have hc : c = d := Subtype.ext (Mole.branch_toNode_injective he)
      subst d
      cases s <;> cases t
      · rfl
      · exact (internalDartValue_mate G.molecule U k ⟨.inl (c,false),hx⟩).symm
      · exact internalDartValue_mate G.molecule U k ⟨.inl (c,false),hy⟩
      · rfl
    · exact (Mole.branch_toNode_ne_leaf c.1 l.1 he).elim
  · rcases y with ⟨d,t⟩ | l
    · exact (Mole.branch_toNode_ne_leaf d.1 ℓ.1 he.symm).elim
    · have hl : ℓ = l := Subtype.ext (Mole.leaf_toNode_injective he)
      subst l
      rfl

end WaveTurbulence.VineEstS2
