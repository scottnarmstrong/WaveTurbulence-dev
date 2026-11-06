/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.VineDelInvariant
import Mathlib.Tactic
/-! # Base templates: deletion connectivity by a checked reachability computation -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Vine

/-- One breadth-first step. -/
@[expose] def stepL (es : List (ℕ × ℕ)) (f : ℕ × ℕ → Bool) (Pb : ℕ → Bool) (n : ℕ)
    (l : List ℕ) : List ℕ :=
  l ++ (List.range n).filter (fun v => Pb v && l.any (fun u =>
    (es.contains (u, v) && f (u, v)) || (es.contains (v, u) && f (v, u))))

/-- Breadth-first reachability from a root. -/
@[expose] def reachL (es : List (ℕ × ℕ)) (f : ℕ × ℕ → Bool) (Pb : ℕ → Bool) (n r : ℕ) :
    ℕ → List ℕ
  | 0 => [r]
  | k + 1 => stepL es f Pb n (reachL es f Pb n r k)

theorem reachL_sound (es : List (ℕ × ℕ)) (f : ℕ × ℕ → Bool) (Pb : ℕ → Bool) (n r : ℕ)
    (hr : Pb r = true) : ∀ k v, v ∈ reachL es f Pb n r k →
    Pb v = true ∧ Relation.EqvGen (FAdj (fun x => Pb x = true) f es) r v := by
  intro k
  induction k with
  | zero =>
    intro v hv
    have : v = r := by simpa [reachL] using hv
    subst this
    exact ⟨hr, Relation.EqvGen.refl _⟩
  | succ k ih =>
    intro v hv
    simp only [reachL, stepL, List.mem_append, List.mem_filter] at hv
    rcases hv with hv | ⟨_, hv⟩
    · exact ih v hv
    · simp only [Bool.and_eq_true, List.any_eq_true] at hv
      obtain ⟨hPv, u, hu, hedge⟩ := hv
      obtain ⟨hPu, hpu⟩ := ih u hu
      refine ⟨hPv, Relation.EqvGen.trans _ _ _ hpu (Relation.EqvGen.rel _ _ ⟨hPu, hPv, ?_⟩)⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at hedge
      rcases hedge with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩

/-- Checked connectivity of the `Pb`-vertices below `n`. -/
@[expose] def connCheck (es : List (ℕ × ℕ)) (f : ℕ × ℕ → Bool) (Pb : ℕ → Bool) (n r : ℕ) : Bool :=
  (List.range n).all (fun p => !Pb p || (reachL es f Pb n r n).contains p)

theorem connCheck_sound (es : List (ℕ × ℕ)) (f : ℕ × ℕ → Bool) (Pb : ℕ → Bool) (n r : ℕ)
    (hr : Pb r = true) (h : connCheck es f Pb n r = true) :
    ∀ p q, p < n → q < n → Pb p = true → Pb q = true →
      Relation.EqvGen (FAdj (fun x => Pb x = true) f es) p q := by
  have key : ∀ p, p < n → Pb p = true → Relation.EqvGen (FAdj (fun x => Pb x = true) f es) r p := by
    intro p hp hP
    simp only [connCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      Bool.not_eq_true', List.contains_iff_mem] at h
    rcases h p hp with h | h
    · rw [hP] at h; exact absurd h (by decide)
    · exact (reachL_sound es f Pb n r hr _ p h).2
  intro p q hp hq hPp hPq
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (key p hp hPp)) (key q hq hPq)

/-- The decidable checks on a base template. -/
@[expose] def delCheck (T : VineTemplate) : Bool :=
  (List.range T.n).all (fun w => decide (w < 2) ||
    connCheck T.bonds (fun _ => true) (fun v => decide (v ≠ w)) T.n 0)

@[expose] def avoidCheck (T : VineTemplate) : Bool :=
  T.slots.all (fun s =>
    connCheck T.bonds (fun e => decide (e ≠ s.1)) (fun v => decide (v < T.n)) T.n 0 &&
    connCheck T.bonds (fun e => decide (e ≠ s.2)) (fun v => decide (v < T.n)) T.n 0)

@[expose] def slotCheck (T : VineTemplate) : Bool :=
  T.slots.all (fun s => decide (s.1.1 < T.n ∧ s.1.2 < T.n ∧ s.2.1 < T.n ∧ s.2.2 < T.n ∧
    s.1.1 ≠ s.1.2 ∧ s.2.1 ≠ s.2.2))

theorem template_checks (X : VineType) :
    delCheck X.template = true ∧ avoidCheck X.template = true ∧ slotCheck X.template = true := by
  cases X <;> exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

end WaveTurbulence.LGSpine
