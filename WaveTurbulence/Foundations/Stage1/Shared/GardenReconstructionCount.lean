/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.GardenReconstructionEncoding
public import WaveTurbulence.Foundations.Stage1.Shared.ReconstructionArithmetic
import Mathlib.Tactic

/-!
# DH21-2 Proposition 6.4: reconstruction count

An explicit universal C0=20736 suffices. The proof counts the actual plain
gardens with a molecule isomorphic to M as a directed multigraph, not
isomorphisms or a weakened combinatorial family. Trivial trees are included.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- DH21-2 Proposition 6.4, with the full trivial-tree reconstruction:
the width-w fiber over an actual molecule has factorial/exponential size. -/
theorem card_gardensWithMolecule (hM : M.IsMolecule) (w : ℕ) :
    Nat.card (GardensWithMolecule M w) ≤ (9*w).factorial*20736^M.atoms.card := by
  calc
    _ ≤ 4^(Fintype.card D)*(4*M.atoms.card+w)^w*2^w := card_gardensWithMolecule_raw M w
    _ ≤ 256^M.atoms.card*(4*M.atoms.card+w)^w*2^w := by
      apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul_right
      have h := card_position_codes_le M hM
      rw [card_position_codes] at h
      exact h
    _ ≤ _ := reconstruction_arithmetic M.atoms.card w

/-- TARGET `propcplmol` and DH21-2 Proposition 6.4 in exactly the source
width convention: the same universal constant appears in both factors. -/
theorem garden_reconstruction_bound (hM : M.IsMolecule) (R : ℕ) :
    Nat.card (GardensWithMolecule M (2*R)) ≤ (20736*R).factorial*20736^M.atoms.card := by
  calc
    _ ≤ (9*(2*R)).factorial*20736^M.atoms.card := card_gardensWithMolecule M hM (2*R)
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.factorial_le (by omega))

omit [DecidableEq V] [Fintype D] in
/-- The order is automatically the atom count for every actual garden
whose molecule is isomorphic to M. -/
theorem garden_iso_order {w : ℕ} {G : Garden w} (f : GardenMoleculeIso G M) :
    G.order = M.atoms.card := by
  have h := Fintype.card_congr f.branches
  simpa only [card_gbranch,Fintype.card_coe,Garden.order] using h

/-- DH21-2 Proposition 6.4 with both fixed order n and fixed width 2R,
including the empty fiber when n differs from the atom count of M. -/
theorem garden_reconstruction_bound_fixed_order (hM : M.IsMolecule) (n R : ℕ) :
    Nat.card {G : Garden (2*R) // G.IsPlain ∧ G.order = n ∧ Nonempty (GardenMoleculeIso G M)} ≤
      (20736*R).factorial*20736^n := by
  classical
  let A := {G : Garden (2*R) // G.IsPlain ∧ G.order = n ∧ Nonempty (GardenMoleculeIso G M)}
  let F : A → GardensWithMolecule M (2*R) := fun G => ⟨G.1,G.2.1,G.2.2.2⟩
  have hi : Function.Injective F := fun G H he => Subtype.ext (congrArg (fun K : GardensWithMolecule M (2*R) => K.1) he)
  have : Finite (GardensWithMolecule M (2*R)) := finite_gardensWithMolecule M (2*R)
  have hc := Nat.card_le_card_of_injective F hi
  rcases isEmpty_or_nonempty A with he | he
  · have hz : Nat.card A = 0 := Nat.card_eq_zero.mpr (Or.inl he)
    change Nat.card A ≤ _
    rw [hz]
    exact Nat.zero_le _
  · obtain ⟨G⟩ := he
    have hn := garden_iso_order M (Classical.choice G.2.2.2)
    rw [G.2.2.1] at hn
    have hbound := garden_reconstruction_bound M hM R
    rw [← hn] at hbound
    exact hc.trans hbound

end WaveTurbulence.Mole
