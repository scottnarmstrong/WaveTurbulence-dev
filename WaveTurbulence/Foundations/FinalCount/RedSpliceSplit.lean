/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.Spine.SourceChainSwap
public import WaveTurbulence.Foundations.Spine.SourceVineObjectBridge
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): a vine chain splits around any of its ingredients

If `A` is an ingredient (joints `x`, `y`) of the chain `S` from `a` to `b`, then `S = L ∪ A ∪ R` where `L` is
empty (`x = a`) or a chain from `a` to `x` meeting `A` exactly in `x`, and `R` is empty (`y = b`) or a chain
from `y` to `b` meeting `A` exactly in `y`; `L` and `R` are disjoint.  These are the two runs of ingredients
on either side of a skipped ingredient (TARGET L1934-L1937, `defcong`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Vine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}


theorem isSomeVine_ends {T : Finset V} {b c : V} (h : IsSomeVine M T b c) : b ∈ T ∧ c ∈ T ∧ b ≠ c := by
  obtain ⟨X, hX⟩ := h
  exact ⟨hX.1.2.1, hX.1.2.2.1, hX.1.2.2.2.1⟩

theorem chain_ends' {S : Finset V} {a b : V} {n : ℕ} (h : Chain M S a b n) : a ∈ S ∧ b ∈ S ∧ a ≠ b := by
  induction h with
  | single hv => exact isSomeVine_ends hv
  | @append S T a b c n _ hT hi hne ih =>
    exact ⟨mem_union_left _ ih.1, mem_union_right _ (isSomeVine_ends hT).2.1, hne⟩

theorem chainIngredient_split (hM : M.IsMolecule) {S A : Finset V} {a b x y : V} {n : ℕ}
    (h : ChainIngredient M S a b n A x y) :
    ∃ L R : Finset V, S = L ∪ A ∪ R ∧
      (L = ∅ ∧ x = a ∨ (x ≠ a ∧ (∃ m, Chain M L a x m) ∧ L ∩ A = {x} ∧ (M.IsBlock S a b → M.IsBlock L a x))) ∧
      (R = ∅ ∧ y = b ∨ (y ≠ b ∧ (∃ m, Chain M R y b m) ∧ R ∩ A = {y})) ∧ Disjoint L R := by
  induction h with
  | single hv =>
    exact ⟨∅, ∅, by simp, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, disjoint_empty_left _⟩
  | @append_left S T A a b c x y n hI hT hi hne ih =>
    obtain ⟨L, R, hS, hL0, hR, hd⟩ := ih
    have hspec := chainIngredient_spec hI
    obtain ⟨X, hX⟩ := hT
    have hL : L = ∅ ∧ x = a ∨ (x ≠ a ∧ (∃ m, Chain M L a x m) ∧ L ∩ A = {x} ∧
        (M.IsBlock (S ∪ T) a c → M.IsBlock L a x)) := by
      rcases hL0 with h0 | ⟨h1, h2, h3, h4⟩
      · exact Or.inl h0
      · exact Or.inr ⟨h1, h2, h3, fun hU => h4 (chain_prefix_isBlock M hM hspec.1 hX hi hU)⟩
    have hT : IsSomeVine M T b c := ⟨X, hX⟩
    have hAS : A ⊆ S := hspec.2.2
    have hAv : IsSomeVine M A x y := hspec.2.1
    have hxy : x ≠ y := (isSomeVine_ends hAv).2.2
    have hyA : y ∈ A := (isSomeVine_ends hAv).2.1
    have hbc : b ≠ c := (isSomeVine_ends hT).2.2
    have hbT : b ∈ T := (isSomeVine_ends hT).1
    have hcT : c ∈ T := (isSomeVine_ends hT).2.1
    have hcS : c ∉ S := fun hc => by
      have : c ∈ S ∩ T := mem_inter.mpr ⟨hc, hcT⟩
      rw [hi] at this; exact hbc (mem_singleton.mp this).symm
    have hTS : ∀ z, z ∈ T → z ∈ S → z = b := fun z hzT hzS => by
      have : z ∈ S ∩ T := mem_inter.mpr ⟨hzS, hzT⟩
      rw [hi] at this; exact mem_singleton.mp this
    have hLS : L ⊆ S := by rw [hS]; intro z hz; simp [hz]
    have hRS : R ⊆ S := by rw [hS]; intro z hz; simp [hz]
    rcases hR with ⟨hR0, hyb⟩ | ⟨hyb, ⟨m, hm⟩, hRA⟩
    · subst hR0
      obtain rfl : y = b := hyb
      refine ⟨L, T, ?_, hL, Or.inr ⟨hbc, ⟨1, .single hT⟩, ?_⟩, ?_⟩
      · rw [hS]; simp
      · ext z
        simp only [mem_inter, mem_singleton]
        constructor
        · rintro ⟨hzT, hzA⟩
          exact hTS z hzT (hAS hzA)
        · rintro rfl
          exact ⟨hbT, hyA⟩
      · rcases hL with ⟨hL0, -⟩ | ⟨-, -, hLA, -⟩
        · rw [hL0]; exact disjoint_empty_left _
        · rw [Finset.disjoint_left]
          intro z hzL hzT
          have hzb : z = y := hTS z hzT (hLS hzL)
          have : z ∈ L ∩ A := mem_inter.mpr ⟨hzL, hzb ▸ hyA⟩
          rw [hLA] at this
          exact hxy ((mem_singleton.mp this).symm.trans hzb)
    · have hbR : b ∈ R := (chain_ends' hm).2.1
      have hyR : y ∈ R := (chain_ends' hm).1
      have hRT : R ∩ T = {b} := by
        ext z
        simp only [mem_inter, mem_singleton]
        exact ⟨fun ⟨hzR, hzT⟩ => hTS z hzT (hRS hzR), fun hz => hz ▸ ⟨hbR, hbT⟩⟩
      have hyc : y ≠ c := fun hh => hcS (hh ▸ hRS hyR)
      refine ⟨L, R ∪ T, ?_, hL, Or.inr ⟨hyc, ⟨m + 1, Chain.append hm hT hRT hyc⟩, ?_⟩, ?_⟩
      · rw [hS]; ext z; simp only [mem_union]; tauto
      · ext z
        simp only [mem_inter, mem_singleton, mem_union]
        constructor
        · rintro ⟨hz | hz, hzA⟩
          · have : z ∈ R ∩ A := mem_inter.mpr ⟨hz, hzA⟩
            rw [hRA] at this; exact mem_singleton.mp this
          · have hzb : z = b := hTS z hz (hAS hzA)
            have : b ∈ R ∩ A := mem_inter.mpr ⟨hbR, hzb ▸ hzA⟩
            rw [hRA] at this
            exact absurd (mem_singleton.mp this).symm hyb
        · rintro rfl
          exact ⟨Or.inl hyR, hyA⟩
      · rw [Finset.disjoint_union_right]
        refine ⟨hd, ?_⟩
        rw [Finset.disjoint_left]
        intro z hzL hzT
        have hzb : z = b := hTS z hzT (hLS hzL)
        exact Finset.disjoint_left.mp hd hzL (hzb ▸ hbR)
  | @append_last S T a b c n hC hT hi hne =>
    obtain ⟨X, hX⟩ := hT
    exact ⟨S, ∅, by simp, Or.inr ⟨(chain_ends' hC).2.2.symm, ⟨n, hC⟩, hi,
      fun hU => chain_prefix_isBlock M hM hC hX hi hU⟩, Or.inl ⟨rfl, rfl⟩, disjoint_empty_right _⟩


/-- The spine's chains and the VINES chains coincide. -/
theorem chain_of_vine {S : Finset V} {a b : V} {n : ℕ} (h : Chain M S a b n) :
    LGSpine.SourceVine.Chain M S a b n := by
  induction h with
  | single h => exact .single h
  | append _ hV hI hne ih => exact .append ih hV hI hne

/-- Removing a suffix chain from a block chain leaves a block. -/
theorem prefix_block_of_suffix_chain (hM : M.IsMolecule) {X Y U : Finset V} {a p b : V} {n m : ℕ}
    (hX : Chain M X a p n) (hY : Chain M Y p b m) (hXY : X ∩ Y = {p}) (hU : U = X ∪ Y)
    (hB : M.IsBlock U a b) : M.IsBlock X a p := by
  induction hY generalizing X U n with
  | @single Y p b hv =>
    obtain ⟨Z, hZ⟩ := hv
    subst hU
    exact chain_prefix_isBlock M hM hX hZ hXY hB
  | @append Y' T p b' b m hY' hT hi hne ih =>
    obtain ⟨Z, hZ⟩ := hT
    have hpY' : p ∈ Y' := (chain_ends' hY').1
    have hb'Y' : b' ∈ Y' := (chain_ends' hY').2.1
    have hpb' : p ≠ b' := (chain_ends' hY').2.2
    have hXT : X ∩ T = ∅ := by
      ext z
      simp only [mem_inter, Finset.notMem_empty, iff_false, not_and]
      intro hzX hzT
      have : z ∈ X ∩ (Y' ∪ T) := mem_inter.mpr ⟨hzX, mem_union_right _ hzT⟩
      rw [hXY] at this
      have hzp : z = p := mem_singleton.mp this
      have : z ∈ Y' ∩ T := mem_inter.mpr ⟨hzp ▸ hpY', hzT⟩
      rw [hi] at this
      exact hpb' (hzp.symm.trans (mem_singleton.mp this))
    have hXY' : X ∩ Y' = {p} := by
      ext z
      simp only [mem_inter, mem_singleton]
      constructor
      · rintro ⟨hzX, hzY⟩
        have : z ∈ X ∩ (Y' ∪ T) := mem_inter.mpr ⟨hzX, mem_union_left _ hzY⟩
        rw [hXY] at this; exact mem_singleton.mp this
      · rintro rfl
        exact ⟨(chain_ends' hX).2.1, hpY'⟩
    have hXY'T : (X ∪ Y') ∩ T = {b'} := by
      rw [Finset.union_inter_distrib_right, hXT, Finset.empty_union]; exact hi
    have hch : Chain M (X ∪ Y') a b' (n + m) :=
      LGSpine.SourceVine.chain_append_chain (chain_of_vine hX) (chain_of_vine hY') hXY' |>.toVine
    have hU' : M.IsBlock (X ∪ Y') a b' := by
      apply chain_prefix_isBlock M hM hch hZ hXY'T
      rw [Finset.union_assoc, ← hU]; exact hB
    exact ih hX hXY' rfl hU'

/-- A suffix chain of a block chain is a block. -/
theorem suffix_block_of_prefix_chain (hM : M.IsMolecule) {X Y U : Finset V} {a p b : V} {n m : ℕ}
    (hX : Chain M X a p n) (hY : Chain M Y p b m) (hXY : X ∩ Y = {p}) (hU : U = X ∪ Y)
    (hB : M.IsBlock U a b) : M.IsBlock Y p b := by
  have hXs := (chain_of_vine hX)
  have hYs := (chain_of_vine hY)
  have hYr := (LGSpine.SourceVine.chain_swap hYs).toVine
  have hXr := (LGSpine.SourceVine.chain_swap hXs).toVine
  have h := prefix_block_of_suffix_chain hM hYr hXr (by rw [Finset.inter_comm]; exact hXY)
    (U := U) (by rw [hU, Finset.union_comm]) (Mole.block_swap_joints M hB)
  exact Mole.block_swap_joints M h


/-- **The two runs around an ingredient.** In a block chain `S` from `a` to `b`, an ingredient `A` with joints
`x, y` splits `S` into the run `L` of ingredients on the `a`-side (a block from `a` to `x`) and the run `R` on the
`b`-side (a block from `y` to `b`), each possibly empty. -/
theorem ingredient_runs (hM : M.IsMolecule) {S A : Finset V} {a b x y : V} {n : ℕ}
    (hI : ChainIngredient M S a b n A x y) (hB : M.IsBlock S a b) :
    ∃ L R : Finset V, S = L ∪ A ∪ R ∧
      (L = ∅ ∧ x = a ∨ (x ≠ a ∧ M.IsBlock L a x ∧ (∃ m, Chain M L a x m) ∧ L ∩ A = {x})) ∧
      (R = ∅ ∧ y = b ∨ (y ≠ b ∧ M.IsBlock R y b ∧ (∃ m, Chain M R y b m) ∧ R ∩ A = {y})) ∧ Disjoint L R := by
  obtain ⟨L, R, hS, hL, hR, hd⟩ := chainIngredient_split hM hI
  have hspec := chainIngredient_spec hI
  have hAv : IsSomeVine M A x y := hspec.2.1
  refine ⟨L, R, hS, ?_, ?_, hd⟩
  · rcases hL with h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h4 hB, h2, h3⟩
  · rcases hR with h | ⟨h1, ⟨m, hm⟩, h3⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, ?_, ⟨m, hm⟩, h3⟩
      -- the prefix chain `P = L ∪ A` from `a` to `y`
      have hP : ∃ k, Chain M (L ∪ A) a y k := by
        rcases hL with ⟨h0, hxa⟩ | ⟨h1', ⟨m', hm'⟩, h3', -⟩
        · subst h0; subst hxa
          exact ⟨1, by rw [Finset.empty_union]; exact Chain.single hAv⟩
        · have hay : a ≠ y := fun hh => by
            have : a ∈ L ∩ A := mem_inter.mpr ⟨(chain_ends' hm').1, hh ▸ (isSomeVine_ends hAv).2.1⟩
            rw [h3'] at this; exact h1' (mem_singleton.mp this).symm
          exact ⟨m' + 1, Chain.append hm' hAv h3' hay⟩
      obtain ⟨k, hk⟩ := hP
      have hPR : (L ∪ A) ∩ R = {y} := by
        rw [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hd, Finset.empty_union,
          Finset.inter_comm, h3]
      exact suffix_block_of_prefix_chain hM hk hm hPR (by rw [hS]) hB

end WaveTurbulence.RedSplice
