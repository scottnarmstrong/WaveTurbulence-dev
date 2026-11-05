/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideRealization
public import WaveTurbulence.Foundations.Molecule.VineSideVIILength
public import WaveTurbulence.Foundations.Molecule.VineSGNonVII
import Mathlib.Tactic

/-! # Ordinary VC containment in one source vine, all eight templates -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The only VC larger than a double bond avoiding the two outer joints
in a type-VII vine is exactly a type-V vine. This includes arbitrary extra
rung counts on every slot of the outer vine. -/
theorem typeVII_inner_VC_isVineV (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (R : VineRealization M .VII S a b) (hS : M.IsBlock S a b)
    {A : Finset V} {x y : V} (hVC : IsVC M A x y) (hAS : A ⊆ S)
    (hcard : 2<A.card) (ha : a ∉ A) (hb : b ∉ A) : M.IsVine .V A x y := by
  obtain ⟨kr,kc,kg,hks,hkc,hAe,_hcount,hj⟩ :=
    typeVII_VC_side_length M hM R hS hVC hAS hcard ha hb
  obtain ⟨m,rfl⟩ : ∃ m,kc=m+2 := ⟨kc-2,by omega⟩
  have hB := hVC.1
  rw [hAe] at hB
  have hv := selected_typeVII_side_isVine R kr m kg hks hB hj
  simpa only [← hAe] using hv

/-- TARGET subsetvc, ordinary VC inside a single outer vine: the inner
SG VC in an LG/ZG vine is one or two double bonds, or a type-V vine inside
type VII. The inputs are the source containment, decoration and gap premises;
no graph classification, side shape or bound on rung counts is assumed. -/
theorem SG_VC_in_single_vine (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (hV : M.IsVine X S a b)
    {A : Finset V} {x y : V} (hVC : IsVC M A x y) (hAS : A ⊆ S)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r r' : Mom d} (hr : M.IsBlockGap L w κ S a r) (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ (X=.VII ∧ M.IsVine .V A x y) := by
  by_cases hX : X=.VII
  · subst X
    by_cases hcard : A.card ≤ 3
    · rcases isVC_doubleChain_of_card_le_three hVC hcard with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · obtain ⟨hS,⟨R⟩⟩ := isVine_iff_realization.mp hV
      have hj := SG_block_outer_joints_absent M hM hS hVC.1 hAS
        L γ η w c κ hκ hc hr hr' houter hsmall
      exact Or.inr (Or.inr ⟨rfl,typeVII_inner_VC_isVineV M hM R hS hVC hAS
        (by omega) hj.1 hj.2⟩)
  · rcases SG_VC_in_nonVII M hM hX hV hVC hAS L γ η w c κ hκ hc hr hr' houter hsmall with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end WaveTurbulence.Vine
