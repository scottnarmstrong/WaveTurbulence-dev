/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Check
public import WaveTurbulence.Foundations.TVine.Checker.SizeBound2

/-!
# Soundness of the per-instance check: basics and F3

* `mem_maskOf`, `inside` lemmas;
* `JointsAt φ j₁ j₂ J`: the isomorphism sends the joints to `J, J + 1` (in some order);
* `rtg_pullback`: paths of the instance inside a set pull back to `AdjIn`-paths of `G`;
* `interior_sound`: `interiorConnB = true` gives `ConnOn G (Core.interior G j₁ j₂)` (M4 §8 F3).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine Core

theorem mem_foldl_mask (v : ℕ) : ∀ (es : Edges) (acc : ℕ),
    mem v (es.foldl (fun acc e => acc ||| bit e.1 ||| bit e.2) acc) = true ↔ mem v acc = true ∨ InEnds es v
  | [], acc => by simp [InEnds]
  | e :: es, acc => by
    rw [List.foldl_cons, mem_foldl_mask v es]
    have key : InEnds (e :: es) v ↔ (e.1 = v ∨ e.2 = v) ∨ InEnds es v := by
      simp only [InEnds, List.mem_cons]
      constructor
      · rintro ⟨e', he' | he', h⟩
        · subst he'; exact Or.inl h
        · exact Or.inr ⟨e', he', h⟩
      · rintro (h | ⟨e', he', h⟩)
        · exact ⟨e, Or.inl rfl, h⟩
        · exact ⟨e', Or.inr he', h⟩
    rw [key]
    simp only [mem_or, mem_bit, Bool.or_eq_true, decide_eq_true_eq]
    tauto

theorem mem_maskOf {es : Edges} {v : ℕ} : mem v (maskOf es) = true ↔ InEnds es v := by
  rw [maskOf, mem_foldl_mask]; simp

theorem mult_inside_le (W : ℕ) (es : Edges) (u v : ℕ) : mult (inside W es) u v ≤ mult es u v := by
  induction es with
  | nil => simp [inside]
  | cons e es ih =>
    simp only [inside, List.filter_cons] at ih ⊢
    split
    · rw [mult_cons, mult_cons]; omega
    · rw [mult_cons]; omega

theorem mult_inside_of_mem {W : ℕ} {es : Edges} {u v : ℕ} (hu : mem u W = true) (hv : mem v W = true) :
    mult (inside W es) u v = mult es u v := by
  unfold inside mult
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro e _
  by_cases h : isPair u v e = true
  · rcases (isPair_iff u v e).mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h, h1, h2, hu, hv]
  · simp [h]

theorem adj_inside {W : ℕ} {es : Edges} {u v : ℕ} (h : Adj (inside W es) u v) :
    mem u W = true ∧ mem v W = true ∧ Adj es u v := by
  unfold Adj at h
  obtain ⟨e, he⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero h)
  rw [List.mem_filter] at he
  have he1 := List.mem_filter.mp he.1
  simp only [Bool.and_eq_true] at he1
  rcases (isPair_iff u v e).mp he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨h1 ▸ he1.2.1, h2 ▸ he1.2.2, ?_⟩
    have := mult_inside_le W es u v; unfold Adj; omega
  · refine ⟨h2 ▸ he1.2.2, h1 ▸ he1.2.1, ?_⟩
    have := mult_inside_le W es u v; unfold Adj; omega

variable {V : Type*} [DecidableEq V]

/-- The isomorphism sends the joints to `J, J + 1` (in some order). -/
def JointsAt {G : UMultigraph V} {es : Edges} (φ : Iso G es) (j₁ j₂ : V) (J : ℕ) : Prop :=
  (φ.f j₁ = J ∧ φ.f j₂ = J + 1) ∨ (φ.f j₁ = J + 1 ∧ φ.f j₂ = J)

/-- The interior on the instance side. -/
theorem mem_interior_iff {G : UMultigraph V} {es : Edges} (φ : Iso G es) {j₁ j₂ : V} {J : ℕ}
    (hJ : JointsAt φ j₁ j₂ J) (hj₁ : j₁ ∈ G.verts) (hj₂ : j₂ ∈ G.verts) :
    (∀ v ∈ Core.interior G j₁ j₂, mem (φ.f v) (sdiff (maskOf es) (bit J ||| bit (J + 1))) = true) ∧
    (∀ z, InEnds es z → mem z (sdiff (maskOf es) (bit J ||| bit (J + 1))) = true → φ.g z ∈ Core.interior G j₁ j₂) := by
  constructor
  · intro v hv
    simp only [Core.interior, Finset.mem_erase] at hv
    obtain ⟨h2, h1, hv⟩ := hv
    have hf1 : φ.f v ≠ φ.f j₁ := fun h => h1 (φ.f_injOn hv hj₁ h)
    have hf2 : φ.f v ≠ φ.f j₂ := fun h => h2 (φ.f_injOn hv hj₂ h)
    simp only [mem_sdiff, mem_or, mem_bit, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
      decide_eq_false_iff_not]
    refine ⟨mem_maskOf.mpr (φ.fv v hv), ?_, ?_⟩ <;> rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> omega
  · intro z hz hzW
    simp only [mem_sdiff, mem_or, mem_bit, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
      decide_eq_false_iff_not] at hzW
    simp only [Core.interior, Finset.mem_erase]
    refine ⟨fun h => ?_, fun h => ?_, φ.gv z hz⟩
    · have := congrArg φ.f h; rw [φ.fg z hz] at this
      rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> omega
    · have := congrArg φ.f h; rw [φ.fg z hz] at this
      rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> omega

end WaveTurbulence.TVine.Checker
