/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperVCapData
public import WaveTurbulence.Foundations.Molecule.VineHyperVICapData
public import WaveTurbulence.Foundations.Molecule.VineHyperVIICapData
public import WaveTurbulence.Foundations.Molecule.VineHyperVIIICapData
public import WaveTurbulence.Foundations.Molecule.VineCapAdjointClassification
import Mathlib.Tactic

/-! # Every hyper-vine-like object contained in one vine has the source adjoint form -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The actual old-core cut and rail incidences construct primitive cap
prefix data for every hyper-block contained in any of the eight vine types. -/
theorem hyperBlock_in_single_vine_cap_data (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S A : Finset V} {a b x y : V} (hV : M.IsVine X S a b)
    (hAS : A ⊆ S) (hH : Mole.IsHyperBlock M A x y) :
    ∃ n r,Nonempty (CapPrefixData M A n r) := by
  cases X with
  | I => exact False.elim (noncap_vine_no_hyperBlock_subset M hM (Or.inl rfl) hV hAS hH)
  | II => exact False.elim (noncap_vine_no_hyperBlock_subset M hM (Or.inr (Or.inl rfl)) hV hAS hH)
  | III => exact False.elim (noncap_vine_no_hyperBlock_subset M hM (Or.inr (Or.inr (Or.inl rfl))) hV hAS hH)
  | IV => exact False.elim (noncap_vine_no_hyperBlock_subset M hM (Or.inr (Or.inr (Or.inr rfl))) hV hAS hH)
  | V => exact typeV_hyper_cap_data M hM hV hAS hH
  | VI => exact typeVI_hyper_cap_data M hM hV hAS hH
  | VII => exact typeVII_hyper_cap_data M hM hV hAS hH
  | VIII => exact typeVIII_hyper_cap_data M hM hV hAS hH

/-- TARGET Lemma subsetvc, hyper-object clause inside a single vine:
every contained HV/HVC has an actual designated adjoint consisting of two
double bonds or a type-V vine. All cap incidence, prefix and realization data
are derived from source containment, for arbitrary inserted rung counts.
No gap assumption is required for this structural clause. The short-cap
exclusions use the B2 family confirmed by the F69 investigation. -/
theorem hyperLike_in_single_vine_adjoint (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S A : Finset V} {a b x y : V} (hV : M.IsVine X S a b)
    (hAS : A ⊆ S) (h : IsHV M A x y ∨ IsHVC M A x y) :
    ∃ e : D,M.ends e=s(x,y) ∧
      (DoubleChain (Mole.eraseBond M e) A x y 2 ∨ (Mole.eraseBond M e).IsVine .V A x y) := by
  obtain ⟨e,he,hVC⟩ := hyperLike_iff_adjoint_VC.mp h
  have hH : Mole.IsHyperBlock M A x y := ⟨e,he,hVC.1⟩
  obtain ⟨n,r,⟨C⟩⟩ := hyperBlock_in_single_vine_cap_data M hM hV hAS hH
  exact C.hyperLike_adjoint_classification hM h

end WaveTurbulence.Vine
