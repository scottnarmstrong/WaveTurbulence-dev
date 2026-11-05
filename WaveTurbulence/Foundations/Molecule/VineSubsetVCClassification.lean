/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDVHyper
public import WaveTurbulence.Foundations.Molecule.VineSubsetVCVineLike
import Mathlib.Tactic

/-! # The full structural classification in TARGET Lemma subsetvc

This module proves the classification clause for every allowed outer object.
Simultaneous removal connectivity is a separate clause and is not asserted here.
-/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc's complete DV structural clause; it holds without a
small-gap premise, by the two actual type-V branch structures. -/
theorem subsetvc_DV_classification (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (hU : IsDV M U a b)
    (P : VineLikeObject M A x y) (hAU : A ⊆ U) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsVine .V A x y ∨
      ∃ e : D,M.ends e=s(x,y) ∧
        (DoubleChain (Mole.eraseBond M e) A x y 2 ∨ (Mole.eraseBond M e).IsVine .V A x y) := by
  cases P with
  | vc hA =>
    rcases VC_in_DV M hM hU hA hAU with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  | hyper P =>
    exact Or.inr (Or.inr (Or.inr
      (hyperLike_in_DV_adjoint M hM hU (hyperLike_iff_realization.mpr ⟨P⟩) hAU)))

/-- TARGET Lemma subsetvc, full structural classification for an SG
contained vine-like object in either a DV or an LG/ZG vine-like object.
Hyper gaps and equal-group containment retain the same actual designation,
according to the owner's 2026-11-04 reading flagged for statement audit. -/
theorem subsetvc_classification (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (P : VineLikeObject M A x y) (hAU : A ⊆ U)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r' : Mom d} (hr' : P.IsGap L w κ r') (hsmall : Molecule.gapKind L γ η r'=.SG)
    (houter : IsDV M U a b ∨ ∃ C : VineLikeObject M U a b,P.IsContained C ∧
      ∃ r : Mom d,C.IsGap L w κ r ∧
        (Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsVine .V A x y ∨
      ∃ e : D,M.ends e=s(x,y) ∧
        (DoubleChain (Mole.eraseBond M e) A x y 2 ∨ (Mole.eraseBond M e).IsVine .V A x y) := by
  rcases houter with hDV | ⟨C,hcont,r,hr,hkind⟩
  · exact subsetvc_DV_classification M hM hDV P hAU
  · exact subsetvc_vineLike_classification M hM C P hcont L γ η w c κ hκ hc hr hr' hkind hsmall

end WaveTurbulence.Vine
