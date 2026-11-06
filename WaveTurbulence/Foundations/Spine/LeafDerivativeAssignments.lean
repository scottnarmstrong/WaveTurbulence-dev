/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SingleLeafDerivative
public import WaveTurbulence.Foundations.Spine.LeafCostProduct
/-! Explicit finite choices assigning each coordinate derivative to one original input leaf. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

@[expose] def LeafDerivativeChoices {w : ℕ} (G : Garden w) : ℕ → Type
  | 0 => PUnit
  | n + 1 => ActualInputLeaves G × LeafDerivativeChoices G n

noncomputable instance instFintypeLeafDerivativeChoices {w : ℕ} (G : Garden w) (n : ℕ) :
    Fintype (LeafDerivativeChoices G n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (ActualInputLeaves G × LeafDerivativeChoices G n))

noncomputable def leafDerivativeProfiles {w d : ℕ} (G : Garden w) (H : LeafProfiles w d) :
    (word : List (Fin d)) → LeafDerivativeChoices G word.length → LeafProfiles w d
  | [], _ => H
  | j :: word, c => singleLeafDerivative G (leafDerivativeProfiles G H word c.2) c.1 j

noncomputable def assignedDerivativeWord {w d : ℕ} (G : Garden w) :
    (word : List (Fin d)) → LeafDerivativeChoices G word.length →
      ActualInputLeaves G → List (Fin d)
  | [], _, _ => []
  | j :: word, c, l =>
    if l = c.1 then j :: assignedDerivativeWord G word c.2 l else assignedDerivativeWord G word c.2 l

theorem assignedDerivativeWord_length {w d : ℕ} (G : Garden w) (word : List (Fin d))
    (c : LeafDerivativeChoices G word.length) (l : ActualInputLeaves G) :
    (assignedDerivativeWord G word c l).length ≤ word.length := by
  induction word with
  | nil => exact le_rfl
  | cons j word ih =>
    simp only [assignedDerivativeWord]
    split_ifs
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (ih c.2)
    · exact (ih c.2).trans (Nat.le_succ _)

theorem card_leafDerivativeChoices {w : ℕ} (G : Garden w) (n : ℕ) :
    Fintype.card (LeafDerivativeChoices G n) = (inputLeaves G).card ^ n := by
  induction n with
  | zero => exact rfl
  | succ n ih =>
    change Fintype.card (ActualInputLeaves G × LeafDerivativeChoices G n) = _
    rw [Fintype.card_prod, Fintype.card_coe, ih, pow_succ, Nat.mul_comm]

end WaveTurbulence.LGSpine
