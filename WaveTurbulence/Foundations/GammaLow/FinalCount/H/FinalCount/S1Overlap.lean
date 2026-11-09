/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.S1Overlap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Split
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.Base
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.S1Overlap`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# Stage 1 combinatorics: overlap of two designated vine-like objects

TARGET `disjointlem` (L1337-L1343, DH23 Lemma 4.11) applied to two non-nested overlapping
vine-like objects `P`, `Q` yields exactly one of two outcomes: either some designated vine-like
object contains `P ∪ Q` (scenarios (b) and (c) of the source proof), or `P` and `Q` are two
type-V vines with the same two joints meeting exactly in these (scenario (a), a double vine).


**Low-range change (L6-HDS).** Main's `isVine_V_of_chain_sigma` (a chain block with `σ = 1` is a vine (V)) becomes
`isTVine_of_chain_sigma` (a T-vine).
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Stage1
open Finset WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- An object whose atom set is an ordinary block has an ordinary vine chain shape. -/
theorem chain_of_isBlock (O : Src.Object Src.γL M) (hB : M.IsBlock O.atoms O.upper O.lower) :
    ∃ n, Src.Chain Src.γL M O.atoms O.upper O.lower n := by
  rcases O with ⟨S, a, b, shape⟩
  cases shape with
  | vc h => exact h.2
  | hyper R =>
    exfalso
    have h3 := Mole.hyperBlock_degrees M ⟨R.added, R.ends_eq, R.adjoint.1⟩
    have h2 := Mole.block_joint_degrees M hB
    have := h3.1
    have h2a := h2.1
    simp only at hB h3 h2
    omega

/-- A chain with at least two ingredients that is a block has no bond between its joints. -/
theorem sigma_chain_two (hM : M.IsMolecule) {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain Src.γL M S a b n) (hB : M.IsBlock S a b) (hn : 2 ≤ n) : M.sigma a b = 0 := by
  cases h with
  | single => omega
  | @append S' T a q b n' hS hT hi hne =>
    have hX := hT
    have hBS' := chain_prefix_isBlock M hM hS.toVine hX hi hB
    have hqT : q ∈ T := hX.block.2.1
    have hbT : b ∈ T := hX.block.2.2.1
    have hqb : q ≠ b := hX.block.2.2.2.1
    have hbS' : b ∉ S' := by
      intro hb
      have : b ∈ S' ∩ T := mem_inter.mpr ⟨hb, hbT⟩
      rw [hi] at this
      exact hqb (mem_singleton.mp this).symm
    have hne' : a ≠ b := hne
    unfold Molecule.sigma
    rw [Mole.bondsBetween_eq_card_darts M hne']
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx hxb
    have hxa := (Mole.mem_dartsAt M a x).mp hx
    have hS'S : S' ⊆ S' ∪ T := subset_union_left
    have hsub : (M.dartsAt a).filter (M.InGroup S') ⊆ (M.dartsAt a).filter (M.InGroup (S' ∪ T)) := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hy1, inGroup_of_subset hS'S hy2⟩
    have hd1 := (Mole.block_joint_degrees M hBS').1
    have hd2 := (Mole.block_joint_degrees M hB).1
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      change M.degIn (S' ∪ T) a ≤ M.degIn S' a
      omega)
    have hxg : x ∈ (M.dartsAt a).filter (M.InGroup (S' ∪ T)) :=
      Finset.mem_filter.mpr ⟨hx, ⟨hxa ▸ hB.2.1, hxb ▸ hB.2.2.1⟩⟩
    rw [← heq] at hxg
    exact hbS' (hxb ▸ (Finset.mem_filter.mp hxg).2.2)

/-- A vine chain of the low family that is a block with exactly one bond between its joints is a T-vine (main: a vine
(V); a single member with `σ = 1` is a T-vine, `DS.isTVine_of_sigma_one`). -/
theorem isTVine_of_chain_sigma (hM : M.IsMolecule) {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain Src.γL M S a b n) (hB : M.IsBlock S a b) (hs : M.sigma a b = 1) : M.IsTVine S a b := by
  by_cases hn : 2 ≤ n
  · have := sigma_chain_two hM h hB hn
    omega
  · cases h with
    | single hv => exact DS.isTVine_of_sigma_one hv hs
    | append hS _ _ _ => exact absurd (by have := chain_pos_S1Basic hS; omega) hn

theorem chain_orient {S : Finset V} {x y a b : V} {n : ℕ} (h : Src.Chain Src.γL M S x y n)
    (hj : ({x, y} : Finset V) = {a, b}) : Src.Chain Src.γL M S a b n := by
  rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h
  · exact chain_swap h

end WaveTurbulence.GammaLow.FinalCount.H
