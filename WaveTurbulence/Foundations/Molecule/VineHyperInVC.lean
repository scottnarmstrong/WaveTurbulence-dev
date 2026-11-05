/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineEraseChainIngredient
public import WaveTurbulence.Foundations.Molecule.VineHyperVertexConnected
public import WaveTurbulence.Foundations.Molecule.VineHyperSingleVine
import Mathlib.Tactic

/-! # Hyper-object localization and adjoint classification in an outer VC -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, hyper-object localization in an outer VC. The closing
bond makes the inner object vertex connected, so no gap premise is needed. -/
theorem hyperLike_in_VC_ingredient (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (h : IsHV M A x y ∨ IsHVC M A x y)
    (hU : IsVC M U a b) (hAU : A ⊆ U) :
    ∃ n T p q,ChainIngredient M U a b n T p q ∧ A ⊆ T := by
  obtain ⟨hUB,n,hchain⟩ := hU
  obtain ⟨T,p,q,hT,hAT⟩ := erase_connected_in_chain_ingredient M hM
    (fun z => hyperLike_erase_connected M h z) hchain hUB hAU
  exact ⟨n,T,p,q,hT,hAT⟩

/-- TARGET subsetvc, hyper-object structural clause in any outer VC:
the designated adjoint is exactly two double bonds or a type-V vine.
All ingredient and cap data are constructed from source containment. -/
theorem hyperLike_in_VC_adjoint (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (h : IsHV M A x y ∨ IsHVC M A x y)
    (hU : IsVC M U a b) (hAU : A ⊆ U) :
    ∃ e : D,M.ends e=s(x,y) ∧
      (DoubleChain (Mole.eraseBond M e) A x y 2 ∨ (Mole.eraseBond M e).IsVine .V A x y) := by
  obtain ⟨n,T,p,q,hT,hAT⟩ := hyperLike_in_VC_ingredient M hM h hU hAU
  obtain ⟨_hchain,⟨X,hX⟩,_hTU⟩ := chainIngredient_spec hT
  exact hyperLike_in_single_vine_adjoint M hM hX hAT h

end WaveTurbulence.Vine
