/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineEraseChainIngredient
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSubproObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjectBridge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceOneJointUnion`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 The union object of two ordinary chain objects meeting at one joint, its small gap, and the
maximality consequence: a selected object cannot be strictly below an eligible non-omitted object.
The eligibility (container) of the union is NOT proved here; see WORKLOG. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine.SourceVine
open Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- The ordinary union object of two chains `a - c` and `c - b` meeting exactly at `c`, when the
union is a block. -/
noncomputable def oneJointUnionObject {S T : Finset V} {a b c : V} {n m : ℕ}
    (hS : Src.Chain Src.γL M S a c n) (hT : Src.Chain Src.γL M T c b m) (hST : S ∩ T = {c})
    (hB : M.IsBlock (S ∪ T) a b) : Src.Object Src.γL M :=
  ⟨S ∪ T, a, b, .vc ⟨hB, n + m, chain_union_of_one_joint hS hT hST⟩⟩

theorem oneJointUnionObject_atoms {S T : Finset V} {a b c : V} {n m : ℕ}
    (hS : Src.Chain Src.γL M S a c n) (hT : Src.Chain Src.γL M T c b m) (hST : S ∩ T = {c})
    (hB : M.IsBlock (S ∪ T) a b) :
    (oneJointUnionObject hS hT hST hB).atoms = S ∪ T := rfl

theorem oneJointUnionObject_hasGapKind {S T : Finset V} {a b c : V} {n m : ℕ}
    (hS : Src.Chain Src.γL M S a c n) (hT : Src.Chain Src.γL M T c b m) (hST : S ∩ T = {c})
    (hB : M.IsBlock (S ∪ T) a b) {d : ℕ} {L γ η : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)}
    {kind : Molecule.GapKind}
    (hP : ∃ r, M.IsBlockGap L w κ S a r ∧ Molecule.gapKind L γ η r = kind) :
    (oneJointUnionObject hS hT hST hB).HasGapKind L γ η w κ kind := by
  obtain ⟨r, hr, hk⟩ := hP
  exact ⟨r, blockGap_mono subset_union_left hr, hk⟩

end WaveTurbulence.GammaLow.FinalCount.H

namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open SourceVine Finset

/-- A selected object is not strictly below an eligible non-omitted ordinary object. -/
theorem selected_not_strictly_below_vc {w d : ℕ} {G : Garden w} {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))}
    {collection : Set (Src.Object Src.γL G.molecule)}
    (hc : Src.IsSourceSecondCollection Src.γL G L γ η base κ F omitted collection)
    {P U : Src.Object Src.γL G.molecule} (hP : P ∈ collection)
    (hU : Src.eligibleSecondObject Src.γL G L γ η base κ F U) (hUo : U.atoms ∉ omitted)
    (hUvc : ∃ h, U.shape = .vc h) (hsub : P.atoms ⊆ U.atoms) : U.atoms ⊆ P.atoms := by
  obtain ⟨_, _, hmax⟩ := (hc.2.2 P).mp hP
  have hPU : P.IsContained U := by
    have hsub' := hsub
    rcases hUvc with ⟨h, hh⟩
    rcases P with ⟨A, x, y, Psh⟩
    rcases U with ⟨S, a, b, Ush⟩
    cases Psh <;> cases Ush
    · exact hsub'
    · cases hh
    · exact hsub'
    · cases hh
  exact Src.Object.contained_atoms_subset _ _ (hmax U hU hUo hPU)

end WaveTurbulence.GammaLow.FinalCount.H
