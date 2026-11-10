/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Shared.S1VInvChain` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.Molecule.VineJointFlows
public import WaveTurbulence.Foundations.Molecule.MoleculeHyperBlocks
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects


/-!
# Ingredients of a group: separation and cross-decomposition

A chain decomposition as an explicit list of (ingredient, joint, joint).  Two ingredients of one
decomposition of a block meet in at most one atom, which is a joint of both.  Two decompositions of
the same block have the same ingredient sets (every vine of a block lies in one ingredient).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.GammaLow.FinalCount

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- A chain decomposition of `U` with joints `a, b`, as the list of its ingredients with their joints. -/
inductive ChainL (γ : ℝ) [Fact (γ ≤ 1 / 2)] (N : Molecule V D) : Finset V → V → V → List (Finset V × V × V) → Prop
  | single {S a b} : Src.IsSomeVine γ N S a b → ChainL γ N S a b [(S, a, b)]
  | append {S T a b c L} : ChainL γ N S a b L → Src.IsSomeVine γ N T b c → S ∩ T = {b} → a ≠ c →
      ChainL γ N (S ∪ T) a c (L ++ [(T, b, c)])

namespace ChainL
variable {N : Molecule V D} {U : Finset V} {a b : V} {L : List (Finset V × V × V)}

theorem chain (h : ChainL γ N U a b L) : ∃ n, Src.Chain γ N U a b n := by
  induction h with
  | single hv => exact ⟨1, Src.Chain.single hv⟩
  | append _ hT hi hne ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, Src.Chain.append hn hT hi hne⟩

theorem entry_vine (h : ChainL γ N U a b L) : ∀ t ∈ L, Src.IsSomeVine γ N t.1 t.2.1 t.2.2 := by
  induction h with
  | single hv => intro t ht; simp at ht; subst ht; exact hv
  | append _ hT _ _ ih =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact ih t ht
    · simp at ht; subst ht; exact hT

theorem entry_subset (h : ChainL γ N U a b L) : ∀ t ∈ L, t.1 ⊆ U := by
  induction h with
  | single hv => intro t ht; simp at ht; subst ht; exact subset_rfl
  | append _ hT _ _ ih =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact (ih t ht).trans subset_union_left
    · simp at ht; subst ht; exact subset_union_right

end ChainL

theorem exists_chainL_of_chain {N : Molecule V D} {U : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain γ N U a b n) : ∃ L, ChainL γ N U a b L ∧ L.length = n := by
  induction h with
  | single hv => exact ⟨_, ChainL.single hv, rfl⟩
  | append _ hT hi hne ih =>
    obtain ⟨L, hL, hl⟩ := ih
    exact ⟨_, ChainL.append hL hT hi hne, by simp [hl]⟩

theorem exists_chainL_of_ingredient {N : Molecule V D} {U A : Finset V} {a b x y : V} {n : ℕ}
    (h : ChainIngredientG γ N U a b n A x y) :
    ∃ L, ChainL γ N U a b L ∧ (A, x, y) ∈ L ∧ L.length = n := by
  induction h with
  | single hv => exact ⟨_, ChainL.single hv, by simp, rfl⟩
  | append_left _ hT hi hne ih =>
    obtain ⟨L, hL, hm, hl⟩ := ih
    exact ⟨_, ChainL.append hL hT hi hne, List.mem_append_left _ hm, by simp [hl]⟩
  | append_last hS hT hi hne =>
    obtain ⟨L, hL, hl⟩ := exists_chainL_of_chain hS
    exact ⟨_, ChainL.append hL hT hi hne, by simp, by simp [hl]⟩





theorem chainL_pairwise {N : Molecule V D} (hN : N.IsMolecule) {U : Finset V} {a b : V}
    {L : List (Finset V × V × V)} (h : ChainL γ N U a b L) (hU : N.IsBlock U a b) :
    L.Pairwise (EntrySep N) := by
  induction h with
  | single hv => exact List.pairwise_singleton _ _
  | @append S T a b c L hL hT hi hne ih =>
    have hX := hT
    obtain ⟨n, hn⟩ := hL.chain
    have hSb : N.IsBlock S a b := chain_prefix_isBlock N hN hn hX hi hU
    refine List.pairwise_append.mpr ⟨ih hSb, List.pairwise_singleton _ _, ?_⟩
    intro t ht t' ht'
    simp only [List.mem_singleton] at ht'
    subst ht'
    have htS : t.1 ⊆ S := hL.entry_subset t ht
    have hmem : ∀ z ∈ t.1 ∩ T, z = b := by
      intro z hz
      have : z ∈ S ∩ T := mem_inter.mpr ⟨htS (mem_inter.mp hz).1, (mem_inter.mp hz).2⟩
      rw [hi] at this
      simpa using this
    refine ⟨fun z hz z' hz' => (hmem z hz).trans (hmem z' hz').symm, fun z hz => ?_⟩
    have hzb := hmem z hz
    subst hzb
    have hX' := hL.entry_vine t ht
    have hzt : z ∈ t.1 := (mem_inter.mp hz).1
    have hle : N.degIn t.1 z ≤ N.degIn S z := Vine.degIn_mono N htS z
    have h2 : N.degIn S z = 2 := (Mole.block_joint_degrees N hSb).2
    refine ⟨?_, (Mole.block_joint_degrees N (Src.isBlock_of_isSomeVine hX)).1⟩
    rcases block_degIn_cases (Src.isBlock_of_isSomeVine hX') hzt with ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · omega

theorem chainL_contains {N : Molecule V D} (hN : N.IsMolecule) {U : Finset V} {a b : V}
    {L : List (Finset V × V × V)} (h : ChainL γ N U a b L) (hU : N.IsBlock U a b)
    {A : Finset V} {x y : V} (hA : Src.IsSomeVine γ N A x y) (hAU : A ⊆ U) :
    ∃ t ∈ L, A ⊆ t.1 := by
  induction h with
  | single hv => exact ⟨_, List.mem_singleton_self _, hAU⟩
  | @append S T a b c L hL hT hi hne ih =>
    have hY := hT
    obtain ⟨n, hn⟩ := hL.chain
    have hSb : N.IsBlock S a b := chain_prefix_isBlock N hN hn hY hi hU
    rcases vine_in_terminal_split N hN (Src.isBlock_of_isSomeVine hY) hU (chain_joints_mem hn).2 hA hAU with hAS | hAT
    · obtain ⟨t, ht, hAt⟩ := ih hSb hAS
      exact ⟨t, List.mem_append_left _ ht, hAt⟩
    · exact ⟨(T, b, c), by simp, hAT⟩

theorem chainL_cross {N : Molecule V D} (hN : N.IsMolecule) {U : Finset V} {a1 b1 a2 b2 : V}
    {L1 L2 : List (Finset V × V × V)} (h1 : ChainL γ N U a1 b1 L1) (hU1 : N.IsBlock U a1 b1)
    (h2 : ChainL γ N U a2 b2 L2) (hU2 : N.IsBlock U a2 b2) {t : Finset V × V × V} (ht : t ∈ L1) :
    ∃ t' ∈ L2, t'.1 = t.1 := by
  have hX := h1.entry_vine t ht
  obtain ⟨t2, ht2, hsub2⟩ := chainL_contains hN h2 hU2 hX (h1.entry_subset t ht)
  have hX2 := h2.entry_vine t2 ht2
  obtain ⟨t1, ht1, hsub1⟩ := chainL_contains hN h1 hU1 hX2 (h2.entry_subset t2 ht2)
  have hsub : t.1 ⊆ t1.1 := hsub2.trans hsub1
  by_cases heq : t.1 = t1.1
  · exact ⟨t2, ht2, subset_antisymm (fun z hz => by rw [heq]; exact hsub1 hz) hsub2⟩
  · exfalso
    have hne : t ≠ t1 := fun h => heq (congrArg Prod.fst h)
    have hsep := (chainL_pairwise hN h1 hU1).forall ht ht1 hne
    have hj1 : t.2.1 ∈ t.1 := (Src.isBlock_of_isSomeVine hX).2.1
    have hj2 : t.2.2 ∈ t.1 := (Src.isBlock_of_isSomeVine hX).2.2.1
    have hne2 : t.2.1 ≠ t.2.2 := (Src.isBlock_of_isSomeVine hX).2.2.2.1
    exact hne2 (hsep.1 _ (mem_inter.mpr ⟨hj1, hsub hj1⟩) _ (mem_inter.mpr ⟨hj2, hsub hj2⟩))

/-- Two entries of two decompositions of the same block, with different sets, are separated. -/
theorem chainL_sep {N : Molecule V D} (hN : N.IsMolecule) {U : Finset V} {a1 b1 a2 b2 : V}
    {L1 L2 : List (Finset V × V × V)} (h1 : ChainL γ N U a1 b1 L1) (hU1 : N.IsBlock U a1 b1)
    (h2 : ChainL γ N U a2 b2 L2) (hU2 : N.IsBlock U a2 b2) {t t' : Finset V × V × V}
    (ht : t ∈ L1) (ht' : t' ∈ L2) (hne : t.1 ≠ t'.1) :
    (∀ z ∈ t.1 ∩ t'.1, ∀ z' ∈ t.1 ∩ t'.1, z = z') ∧
      (∀ z ∈ t.1 ∩ t'.1, N.degIn t.1 z = 2 ∧ N.degIn t'.1 z = 2) := by
  obtain ⟨t'', ht'', htT⟩ := chainL_cross hN h1 hU1 h2 hU2 ht
  have hpw := chainL_pairwise hN h2 hU2
  have htne : t'' ≠ t' := fun h => hne (htT.symm.trans (congrArg Prod.fst h))
  have hsep := hpw.forall ht'' ht' htne
  obtain ⟨hs1, hs2⟩ := hsep
  rw [htT] at hs1 hs2
  exact ⟨hs1, hs2⟩

/-- `T` is an ingredient of a chain decomposition of the block `U`. -/
@[expose] def IngredientIn (γ : ℝ) [Fact (γ ≤ 1 / 2)] (N : Molecule V D) (U T : Finset V) : Prop :=
  ∃ a b n x y, N.IsBlock U a b ∧ ChainIngredientG γ N U a b n T x y

/-- Two distinct ingredients of a block (of possibly different decompositions) meet in at most one
atom, and this atom has degree `2` in both. -/
theorem ingredientIn_sep {N : Molecule V D} (hN : N.IsMolecule) {U T T' : Finset V}
    (h : IngredientIn γ N U T) (h' : IngredientIn γ N U T') (hne : T ≠ T') :
    (∀ z ∈ T ∩ T', ∀ z' ∈ T ∩ T', z = z') ∧ (∀ z ∈ T ∩ T', N.degIn T z = 2 ∧ N.degIn T' z = 2) := by
  obtain ⟨a1, b1, n1, x1, y1, hU1, hc1⟩ := h
  obtain ⟨a2, b2, n2, x2, y2, hU2, hc2⟩ := h'
  obtain ⟨L1, hL1, hm1, -⟩ := exists_chainL_of_ingredient hc1
  obtain ⟨L2, hL2, hm2, -⟩ := exists_chainL_of_ingredient hc2
  exact chainL_sep hN hL1 hU1 hL2 hU2 hm1 hm2 hne


end WaveTurbulence.GammaLow.Fama
