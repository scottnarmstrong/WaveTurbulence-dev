/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ShapeFacts
import Mathlib.Tactic

/-!
# The acyclic predecessor structure in the exact sumint datum

A concrete natural-number rank increases with the draft lexicographic
order. Edge differences therefore determine all alternative localization
labels uniquely, including every root with predecessor `none`.
-/

public section

open Finset

namespace WaveTurbulence.Sumint

/-- Every block size is bounded by the total input size. -/
theorem block_size_le_size (S : SumintShape) (i : Fin S.I) : S.n i ≤ S.M := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- A simple injective ranking compatible with the source block/slot order. -/
@[expose] def lexRank (S : SumintShape) (v : S.VIdx) : ℕ :=
  (v.1 : ℕ) * (S.M + 1) + (v.2 : ℕ)

/-- The rank strictly increases in the exact draft lexicographic relation. -/
theorem lexRank_lt {S : SumintShape} {v w : S.VIdx} (h : S.LexLt v w) :
    lexRank S v < lexRank S w := by
  have hv : (v.2 : ℕ) < S.M := v.2.isLt.trans_le (block_size_le_size S v.1)
  rcases h with h | ⟨h, hslot⟩
  · have hf : (v.1 : ℕ) + 1 ≤ (w.1 : ℕ) := Nat.succ_le_of_lt h
    have hm := Nat.mul_le_mul_right (S.M + 1) hf
    unfold lexRank
    nlinarith
  · have hf : (v.1 : ℕ) = (w.1 : ℕ) := congrArg Fin.val h
    unfold lexRank
    rw [hf]
    omega

/-- The actual admissibility premise makes every predecessor rank smaller. -/
theorem predecessor_rank_lt {d : ℕ} (D : SumintDatum d) {A L γ η : ℝ} {Dsteps : ℕ}
    (hD : D.Admissible A L γ η Dsteps) {v w : D.S.VIdx} (hw : D.prev v = some w) :
    lexRank D.S w < lexRank D.S v := by
  obtain ⟨_, _, _, hp, _, _⟩ := hD.1 v
  exact lexRank_lt (hp w hw)

/-- Differences along the predecessor forest, with zero at roots. -/
@[expose] def edgeDifference {ι G : Type*} [AddGroup G] (prev : ι → Option ι)
    (a : ι → G) (v : ι) : G := a v - (prev v).elim 0 a

/-- An acyclic predecessor system has no unconstrained additive offset. -/
theorem edgeDifference_injective {ι G : Type*} [AddGroup G]
    (prev : ι → Option ι) (rank : ι → ℕ)
    (hp : ∀ v w, prev v = some w → rank w < rank v) : Function.Injective (edgeDifference (G := G) prev) := by
  intro a b hab
  funext v
  have h : ∀ k, ∀ v, rank v = k → a v = b v := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hv
      have he := congrFun hab v
      change a v - (prev v).elim 0 a = b v - (prev v).elim 0 b at he
      cases hprev : prev v with
      | none => simpa only [hprev, Option.elim_none, sub_zero] using he
      | some w =>
        have hw : a w = b w := ih (rank w) (by simpa only [hv] using hp v w hprev) w rfl
        simpa only [hprev, Option.elim_some, hw, sub_left_inj] using he
  exact h (rank v) v rfl

end WaveTurbulence.Sumint
