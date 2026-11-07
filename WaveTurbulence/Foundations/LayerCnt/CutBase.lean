/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.CutFold
import Mathlib.Tactic

/-! # The base-template cut checks (TARGET layervine, L1531)

For every base template a labelling is computed by breadth-first search from the joint `0` (avoiding a blocked
group, or avoiding two exempt slot bonds); the checks that it is a cut labelling and compatible with all slots are
decidable and discharged by kernel evaluation.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence.Vine

instance (σ : ℕ → ℕ) (e : ℕ × ℕ) : Decidable (Crosses σ e) := by unfold Crosses; infer_instance

instance (σ : ℕ → ℕ) (S : List ℕ) : Decidable (Sides2 σ S) := by unfold Sides2; infer_instance

/-- One breadth-first step from the list `l` of reached atoms. -/
@[expose] def bfsStep (es : List (ℕ × ℕ)) (blocked : ℕ → Bool) (excl : List (ℕ × ℕ)) (l : List ℕ) : List ℕ :=
  (l ++ es.flatMap (fun e => if excl.contains e then [] else
      (if l.contains e.1 && !blocked e.2 then [e.2] else []) ++
      (if l.contains e.2 && !blocked e.1 then [e.1] else []))).eraseDups

/-- `n` breadth-first steps. -/
@[expose] def bfs (es : List (ℕ × ℕ)) (blocked : ℕ → Bool) (excl : List (ℕ × ℕ)) : ℕ → List ℕ → List ℕ
  | 0, l => l
  | n + 1, l => bfs es blocked excl n (bfsStep es blocked excl l)

/-- The computed labelling: `1` on the blocked atoms, `0` on those reached from the joint `0`, `2` elsewhere. -/
@[expose] def sigmaOf (T : VineTemplate) (blocked : ℕ → Bool) (excl : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
  if blocked v then 1 else if (bfs T.bonds blocked excl T.n [0]).contains v then 0 else 2

theorem sigmaOf_le (T : VineTemplate) (blocked : ℕ → Bool) (excl : List (ℕ × ℕ)) (v : ℕ) :
    sigmaOf T blocked excl v ≤ 2 := by
  unfold sigmaOf; split_ifs <;> omega

/-- `g` is a cut group of the base template (and stays one after any insertion at any slot). -/
@[expose] def CutG (T : VineTemplate) (g : List ℕ) : Prop :=
  let σ := sigmaOf T (fun v => g.contains v) []
  σ 0 = 0 ∧ σ 1 = 2 ∧ (∀ e ∈ T.bonds, ¬ Crosses σ e) ∧ (∀ s ∈ T.slots, Sides2 σ (slotEnds s)) ∧
    ∀ v ∈ g, v < T.n

/-- The slot `s` is a cut of the template: its two bonds separate the joints, its two ends lie on one side each. -/
@[expose] def CutS (T : VineTemplate) (j : ℕ) (s : (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  let τ := sigmaOf T (fun _ => false) [s.1, s.2]
  τ 0 = 0 ∧ τ 1 = 2 ∧ (∀ v < T.n, τ v ≠ 1) ∧
    (∀ e ∈ T.bonds, e ∉ [s.1, s.2] → ¬ Crosses τ e) ∧
    τ s.1.1 = τ s.2.1 ∧ τ s.1.2 = τ s.2.2 ∧ τ s.1.1 ≠ τ s.1.2 ∧
    ∀ j' < T.slots.length, j' ≠ j → ∀ s', T.slots[j']? = some s' → Sides2 τ (slotEnds s')

end WaveTurbulence.LayerCnt
