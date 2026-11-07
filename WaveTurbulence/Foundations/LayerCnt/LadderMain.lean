/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.Ladder
public import WaveTurbulence.Foundations.Molecule.VineCoherence

/-! # A ladder of a molecule: interior rung sequence, incoherency index, bond exponent (TARGET layerlad)

For `IsLadder u v` (rungs `0..m`) the interior rungs `1..m-1` form a `FullRungSequence`; the four end atoms
are treated as free ("disregarding the atoms at both ends of `𝕃`", L1505).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
  {m : ℕ} {u v : Fin (m + 1) → V}

/-- Extension of a ladder sequence to `ℕ` (constant after the end). -/
@[expose] def lad {α : Type*} (u : Fin (m + 1) → α) (i : ℕ) : α := u ⟨min i m, by omega⟩

theorem lad_of_le {α : Type*} (u : Fin (m + 1) → α) {i : ℕ} (h : i ≤ m) :
    lad u i = u ⟨i, by omega⟩ := by
  unfold lad; congr 1; apply Fin.ext; simp [Nat.min_eq_left h]

/-- The interior rungs `1..m-1` of a ladder, as a full rung sequence. -/
@[expose] noncomputable def ladderRungSeq (hL : M.IsLadder u v) : FullRungSequence M (m - 1) where
  u := lad u
  v := lad v
  distinct := by
    intro a b hab
    have hm := ladder_pos M hL
    rcases a with a | a <;> rcases b with b | b
    · have := ladder_inj M hL (a₁ := Sum.inl ⟨a.1 + 1, by omega⟩) (a₂ := Sum.inl ⟨b.1 + 1, by omega⟩)
        (by simpa [lad_of_le u (show a.1 + 1 ≤ m by omega), lad_of_le u (show b.1 + 1 ≤ m by omega)] using hab)
      simp at this; exact congrArg Sum.inl (Fin.ext this)
    · exfalso
      have := ladder_inj M hL (a₁ := Sum.inl ⟨a.1 + 1, by omega⟩) (a₂ := Sum.inr ⟨b.1 + 1, by omega⟩)
        (by simpa [lad_of_le u (show a.1 + 1 ≤ m by omega), lad_of_le v (show b.1 + 1 ≤ m by omega)] using hab)
      simp at this
    · exfalso
      have := ladder_inj M hL (a₁ := Sum.inr ⟨a.1 + 1, by omega⟩) (a₂ := Sum.inl ⟨b.1 + 1, by omega⟩)
        (by simpa [lad_of_le v (show a.1 + 1 ≤ m by omega), lad_of_le u (show b.1 + 1 ≤ m by omega)] using hab)
      simp at this
    · have := ladder_inj M hL (a₁ := Sum.inr ⟨a.1 + 1, by omega⟩) (a₂ := Sum.inr ⟨b.1 + 1, by omega⟩)
        (by simpa [lad_of_le v (show a.1 + 1 ≤ m by omega), lad_of_le v (show b.1 + 1 ≤ m by omega)] using hab)
      simp at this; exact congrArg Sum.inr (Fin.ext this)
  upper := by
    intro i hi1 hi2
    have hm := ladder_pos M hL
    have := ladder_upper_incidences M hL ⟨i, by omega⟩ ⟨i - 1, by omega⟩ ⟨i + 1, by omega⟩
      (by simp; omega) (by simp; omega) (by simp)
    rw [lad_of_le u (show i ≤ m by omega), lad_of_le v (show i ≤ m by omega),
      lad_of_le u (show i - 1 ≤ m by omega), lad_of_le u (show i + 1 ≤ m by omega)]
    exact Classical.choice this
  lower := by
    intro i hi1 hi2
    have hm := ladder_pos M hL
    have := ladder_lower_incidences M hL ⟨i, by omega⟩ ⟨i - 1, by omega⟩ ⟨i + 1, by omega⟩
      (by simp; omega) (by simp; omega) (by simp)
    rw [lad_of_le v (show i ≤ m by omega), lad_of_le u (show i ≤ m by omega),
      lad_of_le v (show i - 1 ≤ m by omega), lad_of_le v (show i + 1 ≤ m by omega)]
    exact Classical.choice this

theorem ladderRungSeq_u (hL : M.IsLadder u v) : (ladderRungSeq M hL).u = lad u := rfl

theorem ladderRungSeq_v (hL : M.IsLadder u v) : (ladderRungSeq M hL).v = lad v := rfl

omit [Fintype D] [DecidableEq D] in
theorem incoherencyIndex_ladderGroups {α : Type*} (layer : α → ℕ) (u v : Fin (m + 1) → α) :
    incoherencyIndex layer (ladderGroups u v) =
      ∑ j : Fin (m + 1), (if layer (u j) = layer (v j) then 0 else 1) := by
  have key : ∀ l : List (Fin (m + 1)), incoherencyIndex layer (l.map fun j => [u j, v j]) =
      (l.map fun j => if layer (u j) = layer (v j) then 0 else 1).sum := by
    intro l
    induction l with
    | nil => simp [incoherencyIndex]
    | cons a l ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, ← ih,
        show ([u a, v a] :: List.map (fun j => [u j, v j]) l) = [[u a, v a]] ++ List.map (fun j => [u j, v j]) l from rfl,
        incoherencyIndex_append, incoherencyIndex_rung]
  unfold ladderGroups
  rw [key, Fin.sum_univ_def]

end WaveTurbulence.LayerCnt
