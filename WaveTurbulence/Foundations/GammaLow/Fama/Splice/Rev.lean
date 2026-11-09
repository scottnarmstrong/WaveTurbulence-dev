/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceRev` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceRev


/-!
# REDSPLICE-DEF (S2a): reversal of spines

`Spine.cons` prepends a vine to a spine, and `Spine.reverse` reverses a spine (members `(T, p, q)` become
`(T, q, p)` in the opposite order).  Consequently an ingredient of a block chain read from either joint order is a
member of the spine in a fixed order (`Spine.ingredient_mem_or_reverse`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine
open WaveTurbulence.LGSpine.SourceVine (isSomeVine_swap)

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {γ : ℝ} [Fact TVineF1Input]

namespace Spine

/-- Prepend a vine to a spine. -/
theorem cons {L : List (Finset V × V × V)} {U T : Finset V} {b a c : V} (h : Spine γ M L U b a)
    (hT : Src.IsSomeVine γ M T c b) (hi : T ∩ U = {b}) (hne : c ≠ a) :
    Spine γ M ((T, c, b) :: L) (T ∪ U) c a := by
  induction h with
  | @one U' b' a' hv =>
    have := Spine.snoc (Spine.one hT) hv hi hne
    simpa using this
  | @snoc L' U' T' b' x a' h' hT' hi' hne' ih =>
    have hbU' : b' ∈ U' := h'.ends.1
    have hxU' : x ∈ U' := h'.ends.2.1
    have hbT : b' ∈ T := (isSomeVine_ends hT).2.1
    have hTU' : T ∩ U' = {b'} := by
      apply Finset.Subset.antisymm
      · intro v hv
        obtain ⟨h1, h2⟩ := mem_inter.mp hv
        have : v ∈ T ∩ (U' ∪ T') := mem_inter.mpr ⟨h1, mem_union_left _ h2⟩
        rw [hi] at this
        exact this
      · intro v hv
        rw [mem_singleton] at hv
        subst hv
        exact mem_inter.mpr ⟨hbT, hbU'⟩
    have hcx : c ≠ x := by
      intro hcx
      have : c ∈ T ∩ U' := mem_inter.mpr ⟨(isSomeVine_ends hT).1, hcx ▸ hxU'⟩
      rw [hTU'] at this
      exact (isSomeVine_ends hT).2.2 (mem_singleton.mp this)
    have ih' := ih hT hTU' hcx
    have hi3 : (T ∪ U') ∩ T' = {x} := by
      apply Finset.Subset.antisymm
      · intro v hv
        obtain ⟨h1, h2⟩ := mem_inter.mp hv
        rcases mem_union.mp h1 with h1 | h1
        · have : v ∈ T ∩ (U' ∪ T') := mem_inter.mpr ⟨h1, mem_union_right _ h2⟩
          rw [hi, mem_singleton] at this
          subst this
          have : v ∈ U' ∩ T' := mem_inter.mpr ⟨hbU', h2⟩
          rw [hi'] at this
          exact this
        · have : v ∈ U' ∩ T' := mem_inter.mpr ⟨h1, h2⟩
          rw [hi'] at this
          exact this
      · intro v hv
        rw [mem_singleton] at hv
        subst hv
        exact mem_inter.mpr ⟨mem_union_right _ hxU', (isSomeVine_ends hT').1⟩
    have := Spine.snoc ih' hT' hi3 hne
    rw [← Finset.union_assoc]
    simpa using this

/-- Reversal of a spine. -/
theorem reverse {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (h : Spine γ M L U a b) :
    Spine γ M (L.reverse.map (fun t => (t.1, t.2.2, t.2.1))) U b a := by
  induction h with
  | @one T a b hv => exact Spine.one (isSomeVine_swap hv)
  | @snoc L' U' T a b c h' hT hi hne ih =>
    have := Spine.cons ih (isSomeVine_swap hT) (by rw [Finset.inter_comm]; exact hi) (Ne.symm hne)
    simpa [List.reverse_append, Finset.union_comm] using this

/-- An ingredient of the chain read in either joint order is a member of a fixed spine, in some order. -/
theorem ingredient_mem_or_reverse {L : List (Finset V × V × V)} {U : Finset V} {a b : V}
    (hM : M.IsMolecule) (hB : M.IsBlock U a b) (hs : Spine γ M L U a b)
    {n : ℕ} {T : Finset V} {x y : V} (h : ChainIngredientG γ M U b a n T x y) :
    (T, y, x) ∈ L ∨ (T, x, y) ∈ L := by
  obtain ⟨L', hL', hm⟩ := Spine.mem_of_ingredient h
  have hrev := hs.reverse
  have hu := Spine.unique hM hL' hrev (Mole.block_swap_joints M hB)
  rw [hu] at hm
  simp only [List.mem_map, List.mem_reverse] at hm
  obtain ⟨⟨T', p, q⟩, hmem, heq⟩ := hm
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact Or.inl hmem

end Spine

end WaveTurbulence.GammaLow.Fama
