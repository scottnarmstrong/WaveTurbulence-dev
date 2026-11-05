/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineLikeGapObjects
public import WaveTurbulence.Foundations.Molecule.VineSGVCInHyperLike
public import WaveTurbulence.Foundations.Molecule.VineHyperGapProperness
import Mathlib.Tactic

/-! # All structural subsetvc classifications for an LG/ZG outer vine-like object -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET Lemma subsetvc, complete structural classification when the
outer object is vine-like (VC/HV/HVC). Exact source gap and containment data
are used; equal hyper groups obey the owner's compatible-designation reading.
The DV and simultaneous-removal clauses are separate goals. -/
theorem subsetvc_vineLike_classification (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V}
    (C : VineLikeObject M U a b) (P : VineLikeObject M A x y) (hcont : P.IsContained C)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r r' : Mom d} (hr : C.IsGap L w κ r) (hr' : P.IsGap L w κ r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsVine .V A x y ∨
      ∃ f : D,M.ends f=s(x,y) ∧
        (DoubleChain (Mole.eraseBond M f) A x y 2 ∨ (Mole.eraseBond M f).IsVine .V A x y) := by
  cases C with
  | vc hU =>
    cases P with
    | vc hA =>
      rcases SG_VC_in_VC M hM hA hU hcont L γ η w c κ hκ hc hr hr' houter hsmall with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    | hyper P =>
      exact Or.inr (Or.inr (Or.inr (hyperLike_in_VC_adjoint M hM
        (hyperLike_iff_realization.mpr ⟨P⟩) hU hcont)))
  | hyper C =>
    cases P with
    | vc hA =>
      rcases SG_VC_in_hyperLike M hM C hA hcont L γ η w c κ hκ hc hr hr' houter hsmall with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    | hyper P =>
      exact Or.inr (Or.inr (Or.inr (SG_hyperLike_in_hyperLike_adjoint M hM C P hcont
        L γ η w c κ hκ hc hr hr' houter hsmall)))

end WaveTurbulence.Vine
