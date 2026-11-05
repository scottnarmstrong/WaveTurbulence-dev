/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCentralII
public import WaveTurbulence.Foundations.Molecule.VineCentralIII
public import WaveTurbulence.Foundations.Molecule.VineCentralIV
public import WaveTurbulence.Foundations.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.Molecule.VineCentralV
public import WaveTurbulence.Foundations.Molecule.VineCentralVI
public import WaveTurbulence.Foundations.Molecule.VineCentralVIII
import Mathlib.Tactic

/-! # The arbitrary-rung VC containment cases for all outer types except VII -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc, every outer type except VII and ordinary inner VC: under the
source decoration and SG/LG/ZG gap premises, the inner object is one double
bond or two concatenated double bonds. All slot lengths are arbitrary. -/
theorem SG_VC_in_nonVII (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} (hX : X ≠ .VII)
    {S : Finset V} {a b : V} (hV : M.IsVine X S a b)
    {A : Finset V} {x y : V} (hVC : IsVC M A x y) (hAS : A ⊆ S)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r r' : Mom d} (hr : M.IsBlockGap L w κ S a r) (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 := by
  obtain ⟨hS,⟨R⟩⟩ := isVine_iff_realization.mp hV
  apply isVC_doubleChain_of_card_le_three hVC
  by_contra hlarge
  have hcard : 2<A.card := by omega
  have hj := SG_block_outer_joints_absent M hM hS hVC.1 hAS L γ η w c κ hκ hc hr hr' houter hsmall
  have hC := isVC_connected hVC
  cases X
  case I =>
    have hs := congrArg Finset.card R.image_eq
    rw [Finset.card_image_of_injOn R.injOn,Finset.card_range,expand_atoms] at hs
    norm_num [VineType.template] at hs
    have hsub := Finset.card_le_card hAS
    omega
  case II =>
    exact typeII_no_large_inner M hM R hS hVC.1 hC hAS hcard hj.1 hj.2
  case III =>
    have hh := typeIII_inner_card_le_three M hM R hS hVC.1 hC hAS hcard hj.1 hj.2
    omega
  case IV =>
    have hh := typeIV_inner_card_le_three M hM R hS hVC.1 hC hAS hcard hj.1 hj.2
    omega

  case V =>
    have hh := typeV_inner_card_le_three M hM R hS hVC.1 hC hAS hcard hj.1 hj.2
    omega
  case VI =>
    have hh := typeVI_inner_card_le_three M hM R hS hVC.1 hC hAS hcard hj.1 hj.2
    omega
  case VII => exact hX rfl
  case VIII =>
    have hh := typeVIII_inner_card_le_three M hM R hS hVC.1 hC hAS hcard hj.1 hj.2
    omega

end WaveTurbulence.Vine
