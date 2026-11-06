/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Local
import Mathlib.Tactic
/-! Presentation families of the maximal ladders, their signatures, and transport of gaps. -/
@[expose] public section
open WaveTurbulence.Induct
open Finset
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
variable {w d : ℕ} (G : Garden w)

/-- The maximal ladders as a type. -/
abbrev LQ := {S // S ∈ G.molecule.maximalLadders}

/-- One presentation of each maximal ladder. -/
structure PF where
  m : LQ G → ℕ
  u : ∀ S, Fin (m S + 1) → GBranch G.tree
  v : ∀ S, Fin (m S + 1) → GBranch G.tree
  ladder : ∀ S, G.molecule.IsLadder (u S) (v S)
  atoms : ∀ S, Molecule.ladderAtoms (u S) (v S) = S.1

/-- The signature: the first two atoms of the upper row. -/
def PF.sig (π : PF G) : ∀ S : LQ G, GBranch G.tree × GBranch G.tree :=
  fun S => (rowN (π.u S) 0, rowN (π.u S) 1)

theorem ladderAtoms_card {V : Type*} [DecidableEq V] {m : ℕ} {u v : Fin (m + 1) → V}
    (h : Function.Injective (Sum.elim u v)) : (Molecule.ladderAtoms u v).card = 2 * (m + 1) := by
  have : Molecule.ladderAtoms u v = Finset.univ.image (Sum.elim u v) := by
    ext x; simp [Molecule.ladderAtoms]
  rw [this, Finset.card_image_of_injective _ h]
  simp; ring

theorem PF.m_eq (π π' : PF G) (S : LQ G) : π.m S = π'.m S := by
  have h1 := ladderAtoms_card (π.ladder S).2.1
  have h2 := ladderAtoms_card (π'.ladder S).2.1
  rw [π.atoms S] at h1; rw [π'.atoms S] at h2
  omega

theorem ladder_eq_of_two_gen {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) {m m' : ℕ} (hmm : m = m')
    {u v : Fin (m + 1) → V} {u' v' : Fin (m' + 1) → V} (hL : M.IsLadder u v) (hL' : M.IsLadder u' v')
    (h0 : rowN u 0 = rowN u' 0) (h1 : rowN u 1 = rowN u' 1) :
    ∀ i : ℕ, i ≤ m → rowN u i = rowN u' i ∧ rowN v i = rowN v' i := by
  subst hmm
  exact ladder_eq_of_two M hM hL hL' h0 h1

theorem PF.rows_eq (π π' : PF G) (h : π.sig = π'.sig) (S : LQ G) {i : ℕ} (hi : i ≤ π.m S) :
    rowN (π.u S) i = rowN (π'.u S) i ∧ rowN (π.v S) i = rowN (π'.v S) i := by
  have hM : ∀ x ∈ G.molecule.atoms, G.molecule.deg x ≤ 4 := fun x _ =>
    WaveTurbulence.Mole.garden_molecule_deg_le_four G x
  have hs := congrFun h S
  simp only [PF.sig, Prod.mk.injEq] at hs
  exact ladder_eq_of_two_gen G.molecule hM (π.m_eq G π' S) (π.ladder S) (π'.ladder S) hs.1 hs.2 i hi

theorem IsLadderGap_transport {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
    (M : Molecule V D) {m : ℕ} {u v u' v' : Fin (m + 1) → V}
    (h : ∀ i ≤ m, rowN u i = rowN u' i ∧ rowN v i = rowN v' i) (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (hm : 1 ≤ m) (r : Mom d) :
    M.IsLadderGap L w κ u v hm r ↔ M.IsLadderGap L w κ u' v' hm r := by
  have h0 := h 0 (Nat.zero_le _)
  have h1 := h 1 hm
  rw [rowN_of_le u (Nat.zero_le _), rowN_of_le u' (Nat.zero_le _), rowN_of_le v (Nat.zero_le _),
    rowN_of_le v' (Nat.zero_le _)] at h0
  rw [rowN_of_le u hm, rowN_of_le u' hm, rowN_of_le v hm, rowN_of_le v' hm] at h1
  have a0 : u 0 = u' 0 := h0.1
  have b0 : v 0 = v' 0 := h0.2
  unfold Molecule.IsLadderGap
  simp only [a0, b0, h1.1, h1.2]

end WaveTurbulence.Ladder
