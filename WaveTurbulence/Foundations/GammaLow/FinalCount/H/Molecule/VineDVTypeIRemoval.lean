/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineDVTypeIRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVOrdinaryShapes
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.RemovalDV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineDVTypeIRemoval`** (sha256 in H/COPIED-SHA256SUMS), **restated over the
low family by L6-HDS** (PLAN-L6 §3e–3f, layer H-DS). Main's DV is two vines (V); here it is the DV′ of D11
(`Src.IsDV Src.γL`), whose branches are T-vines with `σ = 1` (`H/DS/DV.lean`); the removal arguments are N3 Cor 1.16′(3) and
N3 Lemma P (proved by L3, L3-LP; `H/DS/Removal.lean`, `H/DS/RemovalDV.lean`). Low-range change: the proof is `DS.DV_split_removal_connected` (N3 Cor 1.16′(3) in each T-vine branch) instead of the
type-(V) template paths; the statement is main's.

# Removal of double bonds in a DV′ -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A disjoint family of type-I removals in a DV′ preserves connectivity. Each double bond lies in one T-vine branch and
avoids the shared joints, so the two retained branches glue at a joint. -/
theorem DV_typeI_removal_connected (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b : V} (hU : Src.IsDV Src.γL M U a b) (ps : List (RemovalPiece V D))
    (hI : ∀ P ∈ ps, M.IsVine .I P.atoms P.left P.right)
    (hsub : ∀ P ∈ ps, P.atoms ⊆ U)
    (hD : ∀ P ∈ ps, P.darts = univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps, ∀ Q ∈ ps, P ≠ Q → Disjoint P.atoms Q.atoms) :
    ∀ u ∈ remainingAtoms U ps, ∀ v ∈ remainingAtoms U ps, (removeBlocks M U ps).SameComponent u v := by
  obtain ⟨S, T, hσ, hS, hT, hi, rfl⟩ := DS.dv_branches hU
  refine DS.DV_split_removal_connected hM hS hT ps
    (fun P hP => ⟨Src.Object.ofVine (Src.isSomeVine_of_I (hI P hP)), rfl, rfl, rfl, fun x => ?_⟩)
    (fun P hP x hx => by rw [hD P hP] at hx; exact (mem_filter.mp hx).2)
    (fun P hP => typeI_in_DV_split_disjoint M hM hσ hS hT hi (hI P hP) (hsub P hP)) hdis
  rw [hD P hP]
  exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨mem_univ _, h⟩⟩

end WaveTurbulence.GammaLow.FinalCount.H
