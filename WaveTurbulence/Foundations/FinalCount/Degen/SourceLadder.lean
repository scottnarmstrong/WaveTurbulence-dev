/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.Molecules
import Mathlib.Tactic

/-!
# Selected rung-and-rail ladders (adopted pre-freeze source reading)

TARGET defvine L1384–1386; DH23 Definition 5.1 L789–808; owner ruling in
DEGEN continuation. A selected ladder carries its double rungs and its
oppositely directed single rails. Extra bonds between end atoms are
allowed; in particular a chord closing only one rail is allowed. Rungs
have exactly two actual bonds, and selected consecutive rail pairs have
exactly one actual bond, so extra parallel copies of those prescribed
bonds are excluded. The degree cap forces any other internal bond to
join end atoms; this is a derived property, not an induced-group premise.

This does not modify the B2 draft's induced IsLadder or countA. The source
normalization below uses selected maximal ladders as explicitly authorized.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def SourceLadder (M : Molecule V D) {m : ℕ} (u v : Fin (m + 1) → V) : Prop :=
  1 ≤ m ∧ Function.Injective (Sum.elim u v) ∧ (∀ j, u j ∈ M.atoms ∧ v j ∈ M.atoms) ∧
    (∀ j, M.bondsBetween (u j) (v j) = 2) ∧
    (∀ j : Fin m, M.bondsBetween (u j.castSucc) (u j.succ) = 1 ∧
      M.bondsBetween (v j.castSucc) (v j.succ) = 1 ∧
      (M.Directed (u j.castSucc) (u j.succ) ↔ M.Directed (v j.succ) (v j.castSucc)))

def SourceLadderSet (M : Molecule V D) (S : Finset V) : Prop :=
  ∃ m : ℕ, ∃ u v : Fin (m + 1) → V, SourceLadder M u v ∧ Molecule.ladderAtoms u v = S

noncomputable def sourceMaximalLadders (M : Molecule V D) : Finset (Finset V) := by
  classical
  exact M.atoms.powerset.filter fun S => SourceLadderSet M S ∧
    ∀ S' : Finset V, SourceLadderSet M S' → S ⊆ S' → S' = S

/-- Literal product from defcounta2 over the source-reading maximal ladders. -/
noncomputable def sourceLadderProduct (M : Molecule V D) (L γ δ : ℝ) (P : Finset V → ℝ) : ℝ :=
  ∏ S ∈ sourceMaximalLadders M, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S

theorem sourceLadderSet_atoms_subset (M : Molecule V D) {S : Finset V}
    (h : SourceLadderSet M S) : S ⊆ M.atoms := by
  obtain ⟨m, u, v, h, rfl⟩ := h
  intro x hx
  obtain hx | hx := mem_union.mp hx
  · obtain ⟨j, _, rfl⟩ := mem_image.mp hx
    exact (h.2.2.1 j).1
  · obtain ⟨j, _, rfl⟩ := mem_image.mp hx
    exact (h.2.2.1 j).2

end WaveTurbulence.Degen
