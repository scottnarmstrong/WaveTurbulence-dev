/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSGSingleVine
public import WaveTurbulence.Foundations.Molecule.VineGapProperness
import Mathlib.Tactic

/-! # Ordinary SG vines are double bonds or the complete VII side -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- An ordinary SG vine in one LG/ZG vine is type I, or type V with
outer type VII. A two-double-bond chain is not an additional vine case. -/
theorem SG_ordinary_vine_shape (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S A : Finset V} {a b x y : V} (hV : M.IsVine X S a b)
    (hA : IsSomeVine M A x y) (hAS : A ⊆ S)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r r' : Mom d} (hr : M.IsBlockGap L w κ S a r) (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) :
    M.IsVine .I A x y ∨ (X=.VII ∧ M.IsVine .V A x y) := by
  obtain ⟨Y,hY⟩ := hA
  have hVC : IsVC M A x y := ⟨hY.1,1,Chain.single ⟨Y,hY⟩⟩
  rcases SG_VC_in_single_vine M hM hV hVC hAS L γ η w c κ hκ hc hr hr' houter hsmall with h | h | h
  · have hcard := doubleChain_card h
    have htype := isVine_typeI_of_card_lt_four hY (by omega)
    subst Y
    exact Or.inl hY
  · have hcard := doubleChain_card h
    have htype := isVine_typeI_of_card_lt_four hY (by omega)
    subst Y
    exact Or.inl hY
  · exact Or.inr h

/-- A non-type-I ordinary SG vine in VII is the actual complete side,
with the fixed side joint pair. These data follow from containment and
source gap premises, not an assumed side representation. -/
theorem typeVII_SG_nonI_vine_side (M : Molecule V D) (hM : M.IsMolecule)
    {S A : Finset V} {a b x y : V} (R : VineRealization M .VII S a b)
    (hS : M.IsBlock S a b) (hA : IsSomeVine M A x y)
    (hnot : ¬M.IsVine .I A x y) (hAS : A ⊆ S)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r r' : Mom d} (hr : M.IsBlockGap L w κ S a r) (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) :
    ∃ kr kc kg,R.k=[kr,kc,kg] ∧ A=R.selectedAtoms (sideLabels (11+2*kr) kc) ∧
      ({x,y} : Finset V)={(R.coreAtom (7 : Fin 11)).1,(R.coreAtom (8 : Fin 11)).1} := by
  obtain ⟨Y,hY⟩ := hA
  have hVC : IsVC M A x y := ⟨hY.1,1,Chain.single ⟨Y,hY⟩⟩
  have hcard : 2<A.card := by
    by_contra hh
    have htype := isVine_typeI_of_card_lt_four hY (by omega)
    subst Y
    exact hnot hY
  have hj := SG_block_outer_joints_absent M hM hS hY.1 hAS
    L γ η w c κ hκ hc hr hr' houter hsmall
  obtain ⟨kr,kc,kg,hks,_hkc,hAe,_hcount,hpair⟩ := typeVII_VC_side_length M hM R hS hVC hAS hcard hj.1 hj.2
  exact ⟨kr,kc,kg,hks,hAe,hpair⟩

end WaveTurbulence.Vine
