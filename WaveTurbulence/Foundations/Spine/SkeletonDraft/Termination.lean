/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.Order

/-! # Existence of a terminal prime reduction, before the confluence theorem

DH21 Proposition 4.13 and DH21-2 Proposition 4.4: the existence part is
strict descent by two in branching order. Uniqueness is a separate obligation.
-/

public section
namespace WaveTurbulence.Reg.Skeleton

/-- Source expansion guards retain all matching typing data at the predecessor. -/
theorem Expand.source_valid {w : ℕ} {S R : Raw w} (h : Expand S R) : S.Valid := by
  cases h <;> assumption

/-- The signature is unchanged by either elementary operation. -/
theorem Expand.sig_eq {w : ℕ} {S R : Raw w} (h : Expand S R) : R.sig = S.sig := by
  cases h <;> rfl

/-- Finite source reconstruction cannot decrease branching order. -/
theorem Reconstructs.order_le {w : ℕ} {S R : Raw w} (h : Reconstructs S R) : S.order ≤ R.order := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hstep ih => have ho := hstep.order; omega

/-- An expansion history retains the original root signs. -/
theorem Reconstructs.sig_eq {w : ℕ} {S R : Raw w} (h : Reconstructs S R) : R.sig = S.sig := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact hstep.sig_eq.trans ih

/-- DH21 Proposition 4.13 / DH21-2 Proposition 4.4, existence part:
every valid source forest has a prime predecessor reached by actual inverse moves. -/
theorem exists_prime_predecessor {w : ℕ} (R : Raw w) (hR : R.Valid) :
    ∃ S : Raw w, Prime S ∧ Reconstructs S R := by
  classical
  generalize hsize : R.order = N
  induction N using Nat.strong_induction_on generalizing R with
  | h N ih =>
    by_cases hc : ∃ S, Expand S R
    · obtain ⟨S,hS⟩ := hc
      have hs := hS.order
      obtain ⟨P,hP,hPS⟩ := ih S.order (by omega) S hS.source_valid rfl
      exact ⟨P,hP,Relation.ReflTransGen.tail hPS hS⟩
    · exact ⟨R,⟨hR,fun S hS => hc ⟨S,hS⟩⟩,Relation.ReflTransGen.refl⟩

end WaveTurbulence.Reg.Skeleton
