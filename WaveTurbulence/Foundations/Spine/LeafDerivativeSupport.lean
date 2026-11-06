/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafDerivativeProfileBounds
/-! The assigned derivative budget is exactly conserved across input leaves. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem sum_assignedDerivativeWord_length {w d : ℕ} (G : Garden w) (word : List (Fin d))
    (c : LeafDerivativeChoices G word.length) :
    (∑ l : ActualInputLeaves G, (assignedDerivativeWord G word c l).length) = word.length := by
  classical
  induction word with
  | nil => simp only [assignedDerivativeWord, List.length_nil, sum_const_zero]
  | cons j word ih =>
    have he : (fun l : ActualInputLeaves G => (assignedDerivativeWord G (j :: word) c l).length) =
        fun l => (assignedDerivativeWord G word c.2 l).length + if l = c.1 then 1 else 0 := by
      funext l
      by_cases hl : l = c.1 <;>
        simp only [assignedDerivativeWord, hl, ite_true, ite_false, List.length_cons, Nat.add_zero]
    rw [show (∑ l : ActualInputLeaves G, (assignedDerivativeWord G (j :: word) c l).length) =
      ∑ l : ActualInputLeaves G,
        ((assignedDerivativeWord G word c.2 l).length + if l = c.1 then 1 else 0) from
      congrArg (fun f : ActualInputLeaves G → ℕ => ∑ l, f l) he]
    rw [sum_add_distrib, ih c.2]
    simp only [sum_ite_eq', mem_univ, ite_true, List.length_cons]

noncomputable def assignedDerivativeSupport {w d : ℕ} (G : Garden w)
    (word : List (Fin d)) (c : LeafDerivativeChoices G word.length) : Finset (ActualInputLeaves G) := by
  classical
  exact univ.filter (fun l => (assignedDerivativeWord G word c l).length ≠ 0)

theorem card_assignedDerivativeSupport {w d : ℕ} (G : Garden w)
    (word : List (Fin d)) (c : LeafDerivativeChoices G word.length) :
    (assignedDerivativeSupport G word c).card ≤ word.length := by
  have h := card_modified_le_total_derivatives (univ : Finset (ActualInputLeaves G))
    (fun l => (assignedDerivativeWord G word c l).length)
  exact h.trans_eq (sum_assignedDerivativeWord_length G word c)

theorem leafDerivativeProfiles_eq_of_unselected {w d : ℕ} (G : Garden w)
    (H : LeafProfiles w d) (word : List (Fin d)) (c : LeafDerivativeChoices G word.length)
    (l : ActualInputLeaves G) (hl : l ∉ assignedDerivativeSupport G word c) :
    leafDerivativeProfiles G H word c l.1.1 = H l.1.1 := by
  classical
  have hlen : (assignedDerivativeWord G word c l).length = 0 := by
    by_contra hn
    apply hl
    exact mem_filter.mpr ⟨mem_univ _, hn⟩
  have he : assignedDerivativeWord G word c l = [] := List.length_eq_zero_iff.mp hlen
  rw [leafDerivativeProfiles_input, he]
  rfl

end WaveTurbulence.LGSpine
