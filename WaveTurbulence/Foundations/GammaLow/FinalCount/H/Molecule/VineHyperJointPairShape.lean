/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineHyperJointPairShape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperBothJoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineVCJointEdge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineHyperJointPairShape`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # A both-joints ordinary piece in a hyper-object forces a type-V adjoint 

**Low-range change (L6-HDS).** N3 Cor 1.16′ (L-b): the designated adjoint is a T-vine with `σ = 1` (main: a vine (V)); the selected
ordinary vine is the (I) formed by the added bond and the adjoint's joint bond.
-/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An actual ordinary vine selecting both outer hyper-object joints is
exactly their type-I double bond; the designated outer adjoint is type V.
This is structural and needs no decoration or gap assumption. -/
theorem ordinary_vine_in_hyperLike_both_joint_shape (M : Molecule V D) (hM : M.IsMolecule)
    {U P : Finset V} {a b x y : V} (R : Src.HyperLikeRealization Src.γL M U a b)
    (hP : Src.IsSomeVine Src.γL M P x y) (hPU : P ⊆ U) (ha : a ∈ P) (hb : b ∈ P) :
    P={a,b} ∧ M.IsVine .I P x y ∧ (Mole.eraseBond M R.added).IsTVine U a b ∧
      (Mole.eraseBond M R.added).sigma a b = 1 := by
  have hX := hP
  have hHyper : Src.IsHV Src.γL M U a b ∨ Src.IsHVC Src.γL M U a b := hyperLike_iff_realization.mpr ⟨R⟩
  have hAtoms := block_in_hyperLike_both_joints_atoms M hM hHyper hX.block hPU ha hb
  have hcard : P.card=2 := by rw [hAtoms,card_pair R.adjoint.1.2.2.2.1]
  replace hX : M.IsVine .I P x y := DS.typeI_of_card_lt_four hX (by omega)
  have haPair : a=x ∨ a=y := by
    have hh := ha
    rw [typeI_atoms hX] at hh
    simpa only [mem_insert,mem_singleton] using hh
  have hdeg : M.degIn P a=2 := haPair.elim
    (fun h => h.symm ▸ (Mole.block_joint_degrees M hX.1).1)
    (fun h => h.symm ▸ (Mole.block_joint_degrees M hX.1).2)
  rw [hAtoms] at hdeg
  have hOne := eraseBond_pair_degree_one M R.added R.ends_eq R.adjoint.1.2.2.2.1 hdeg
  have hσ : (Mole.eraseBond M R.added).sigma a b = 1 := by
    have := DS.degIn_pair (M := Mole.eraseBond M R.added) R.adjoint.1.2.2.2.1
    omega
  exact ⟨hAtoms,hX,VC_joint_pair_degree_one_isTVine _ R.adjoint hOne,hσ⟩

end WaveTurbulence.GammaLow.FinalCount.H
