/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineEraseChainIngredient
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineBranchingEnds`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Short chains with branching endpoints are single vines -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A chain with one ingredient is a vine. -/
theorem chain_one_isSomeVine {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.Chain Src.γL M S a b 1) : Src.IsSomeVine Src.γL M S a b := by
  cases h with
  | single h => exact h
  | append h _ _ _ => have := chain_pos h; omega

/-- Every chain on fewer than seven atoms with two distinct neighbors at
each joint is a single vine. This excludes the short side pieces of the
finite cores from being multi-ingredient chains. -/
theorem small_chain_single_of_branching_ends (M : Molecule V D)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b) {n : ℕ} (h : Src.Chain Src.γL M S a b n)
    (hcard : S.card<7)
    (ha : ∃ u v,(Mole.induced M S).Adj a u ∧ (Mole.induced M S).Adj a v ∧ u ≠ v)
    (hb : ∃ u v,(Mole.induced M S).Adj b u ∧ (Mole.induced M S).Adj b v ∧ u ≠ v) :
    Src.IsSomeVine Src.γL M S a b := by
  have hd := Mole.block_joint_degrees M hB
  rcases chain_small_end_typeI h hcard with hn | ⟨A,x,hI,hAS⟩ | ⟨A,x,hI,hAS⟩
  · subst n
    exact chain_one_isSomeVine h
  · exact False.elim (no_typeI_at_branching_joint M hB.2.1 hd.1 ha hI hAS)
  · obtain ⟨R⟩ := typeI_twoIncidences hI
    obtain ⟨u,v,hu,hv,hne⟩ := hb
    have hx := hAS hI.1.2.1
    have heu := twoIncidences_unique_internal_neighbor M R.mates hB.2.2.1 hx hd.2 hu
    have hev := twoIncidences_unique_internal_neighbor M R.mates hB.2.2.1 hx hd.2 hv
    exact False.elim (hne (heu.trans hev.symm))

/-! Main's `not_isVC_five_of_branching` and `not_isVC_five_or_seven_of_erase_connected` are NOT ported: they are false
over the low family (a T-vine has `2m + 5` atoms; the five-atom T-vine with core `p, q, r`, bonds `pq, qr` simple and
`pr` double, joints `j₁ ∼ p, q` and `j₂ ∼ q, r` is a VC with branching joints, connected after every one-atom removal).
See `FINDINGS-H.md` (H-1); their consumers (`VineSideVIILength`, `VineCapShortAdjoints`) are re-argued in their layers. -/

end WaveTurbulence.GammaLow.FinalCount.H
