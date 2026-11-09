/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineSGOrdinaryRemovalSingle
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGOrdinaryVineShape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.Removal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineSGOrdinaryRemovalSingle`** (sha256 in H/COPIED-SHA256SUMS), **restated over the
low family by L6-HDS** (PLAN-L6 §3e–3f, layer H-DS). Main's statement names the drawn vine types; in the low family
`𝒱_{γL}` a vine is of type (I), (II) or a T-vine, and the drawn-type classification is replaced by N3 Cor 1.16′ (proved
by L3; `H/DS/Member.lean`, `H/DS/Removal.lean`). Low-range change: the outer vine is a member of the low family (`Src.IsSomeVine Src.γL`, main: `M.IsVine X`); the proof
is N3 Cor 1.16′(3) (`DS.removal_connected_of_objects`; the SG pieces are proper by main's `SG_block_ne_outer`) instead of
the drawn template paths.

# Removal of SG vines in a single vine of the low family -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc, ordinary removals in one vine ingredient of the low family. Source SG vines form a disjoint family
in an LG/ZG vine; deleting all their bonds and nonjoint atoms preserves connectivity (N3 Cor 1.16′(3)). -/
theorem SG_ordinary_vines_removal_in_single_vine_connected (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hV : Src.IsSomeVine Src.γL M S a b)
    (ps : List (RemovalPiece V D))
    (hvine : ∀ P ∈ ps, Src.IsSomeVine Src.γL M P.atoms P.left P.right)
    (hsub : ∀ P ∈ ps, P.atoms ⊆ S)
    (hD : ∀ P ∈ ps, P.darts = univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps, ∀ Q ∈ ps, P ≠ Q → Disjoint P.atoms Q.atoms)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0)
    {r : Mom d} (hr : M.IsBlockGap L w κ S a r)
    (houter : Molecule.gapKind L γ η r = .LG ∨ Molecule.gapKind L γ η r = .ZG)
    (hSG : ∀ P ∈ ps, ∃ r' : Mom d, M.IsBlockGap L w κ P.atoms P.left r' ∧
      Molecule.gapKind L γ η r' = .SG) :
    ∀ u ∈ remainingAtoms S ps, ∀ v ∈ remainingAtoms S ps, (removeBlocks M S ps).SameComponent u v := by
  refine DS.removal_connected_of_objects hM hV ps
    (fun P hP => ⟨Src.Object.ofVine (hvine P hP), rfl, rfl, rfl, fun x => ?_⟩) ?_ hdis
  · rw [hD P hP]
    exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨mem_univ _, h⟩⟩
  · intro P hP
    obtain ⟨r', hr', hk⟩ := hSG P hP
    exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub P hP,
      SG_block_ne_outer M hM hV.block (hvine P hP).block L γ η w c κ hκ hc hr hr' houter hk⟩

end WaveTurbulence.GammaLow.FinalCount.H
