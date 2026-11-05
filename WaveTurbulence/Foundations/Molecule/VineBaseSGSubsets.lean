/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBaseVCSubsets
public import WaveTurbulence.Foundations.Molecule.VineGapProperness
import Mathlib.Tactic

/-! # The decorated zero-extra-rung VC case of TARGET subsetvc -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc, restricted to a single unexpanded outer vine and an
inner VC: every SG inner VC in an LG or ZG outer vine is one double bond or
two concatenated double bonds. Properness is proved from decoration and
gap separation, rather than assumed. -/
theorem base_SG_VC_subsets (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (hV : M.IsVine X S a b)
    (R : VineRealization M X S a b) (hk : R.k=List.replicate X.template.slots.length 0)
    {A : Finset V} {x y : V} (hAS : A ⊆ S) (hVC : IsVC M A x y)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r r' : Mom d} (hr : M.IsBlockGap L w κ S a r)
    (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 := by
  exact base_proper_VC_doubleChain R hk hAS hVC
    (SG_block_ne_outer M hM hV.1 hVC.1 L γ η w c κ hκ hc hr hr' houter hsmall)

end WaveTurbulence.Vine
