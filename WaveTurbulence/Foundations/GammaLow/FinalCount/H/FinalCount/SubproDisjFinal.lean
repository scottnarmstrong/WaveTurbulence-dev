/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.SubproDisjFinal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproC2Second
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproVcShape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.SubproDisjFinal`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# S4-DISJ: the Step-1 objects `C₁ ∪ C₂` of S2a's construction are pairwise atom-disjoint (TARGET L2175)

Package theorem for `collectionChoices G σ` (S2a) and G3's `C2Of`.
-/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCountG3 Finset

variable {w d : ℕ}

/-- **`C₂` against `C₁` and the hinges.** A member of `C₂` lies in a host disjoint from `C₁` and the hinges. -/
theorem c2Of_disjoint_c1_hinges {V : Type*} [DecidableEq V] {D₀ : Type*} [Fintype D₀] [DecidableEq D₀]
    {M₀ : Molecule V D₀} {L γ η : ℝ} {base : Mom d} {κ : D₀ → (Fin d → ℤ)} (C : CollData M₀)
    {Unsel : Set (Src.Object Src.γL M₀)} {U : Src.Object Src.γL M₀} (hU : U ∈ C.C2Of L γ η base κ Unsel) :
    (∀ i, Disjoint U.atoms (C.collection i).atoms) ∧ Disjoint U.atoms C.hinges := by
  obtain ⟨⟨⟨hsg, hout, hdis, hhost⟩, _⟩, _⟩ := hU
  refine ⟨?_, hdis⟩
  intro i
  rcases hhost with ⟨S, a, b, hDV, hsub, hSh, hSC⟩ | ⟨Q, hsub, hQk, hQh, hQC⟩
  · exact Finset.disjoint_of_subset_left hsub (hSC i)
  · exact Finset.disjoint_of_subset_left hsub (hQC i)

/-- **S4-DISJ goal 1 (TARGET L2175) for S2a's construction.** For `C := collectionChoices G σ` and G3's `C₂ = C2Of C Unsel`
(with `Unsel` the pool members whose atom set is omitted by lg-spine's source second collection `hc`, the literal DV rule of
TARGET L2101: exactly one vine of each SG double vine is omitted):
* the members of `C₁` are pairwise atom-disjoint (`Structural`, S2a);
* the members of `C₂` are disjoint from every member of `C₁` and from the hinges;
* two members of `C₂` have equal or disjoint atom sets (equal only for two designations of one hyper group). -/
theorem step1_objects_disjoint {G : Garden w} (hM : G.molecule.IsMolecule) (σ : RedSplice.Prescription G)
    (hno : ∀ a b, G.molecule.bondsBetween a b ≠ 3) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart (stSt G σ).G → (Fin d → ℤ)} {c0 : GBranch (stSt G σ).G.tree → Mom d}
    (hκ : (stSt G σ).G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ (stSt G σ).G.molecule.atoms, (stSt G σ).G.molecule.deg v = 4 → c0 v = 0)
    {omitted : Set (Finset (GBranch (stSt G σ).G.tree))}
    {collection : Set (Src.Object Src.γL (stSt G σ).G.molecule)}
    (hc : Src.IsSourceSecondCollection Src.γL (stSt G σ).G L γ η base κ
      (collectionChoices G σ).forbidden omitted collection) :
    let C := collDataOf (collectionChoices G σ)
    let Unsel := unselOf C L γ η base κ omitted
    (∀ i j, i ≠ j → Disjoint (C.collection i).atoms (C.collection j).atoms) ∧
    (∀ U ∈ C.C2Of L γ η base κ Unsel, ∀ i, Disjoint U.atoms (C.collection i).atoms) ∧
    (∀ U ∈ C.C2Of L γ η base κ Unsel, Disjoint U.atoms C.hinges) ∧
    (∀ U ∈ C.C2Of L γ η base κ Unsel, ∀ U' ∈ C.C2Of L γ η base κ Unsel,
      U.atoms = U'.atoms ∨ Disjoint U.atoms U'.atoms) := by
  intro C Unsel
  refine ⟨(structural_collectionChoices hM σ hno).2.1,
    fun U hU => (c2Of_disjoint_c1_hinges C hU).1, fun U hU => (c2Of_disjoint_c1_hinges C hU).2,
    fun U hU U' hU' => c2Of_atoms_eq_or_disjoint (Mole.garden_isMolecule (stSt G σ).G) hκ hc0 C hc hU hU'⟩

end WaveTurbulence.GammaLow.FinalCount.H
