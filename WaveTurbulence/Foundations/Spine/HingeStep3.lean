/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.HingeStep2
/-! # One-atom removal step (S3c) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine Finset
open scoped Classical

variable {w : ℕ} {G : Garden w}

/-- The rung ranges of a ladder with rung `k` deleted (ranges of at least two rungs only). -/
def rangesAvoiding (m k : ℕ) : List (ℕ × ℕ) :=
  (if 2 ≤ k then [(0, k - 1)] else []) ++ (if k + 2 ≤ m then [(k + 1, m - k - 1)] else [])

theorem rangesAvoiding_props (m k : ℕ) (hk : k ≤ m) :
    (∀ p ∈ rangesAvoiding m k, p.1 + p.2 ≤ m ∧ 1 ≤ p.2 ∧ ((p.1 + p.2 < k) ∨ k < p.1)) ∧
    (rangesAvoiding m k).Pairwise (fun p q => p.1 + p.2 < q.1) := by
  unfold rangesAvoiding
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [List.mem_append] at hp
    rcases hp with hp | hp
    · split_ifs at hp with h
      · simp at hp; subst hp; simp; omega
      · simp at hp
    · split_ifs at hp with h
      · simp at hp; subst hp; simp; omega
      · simp at hp
  · rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · split_ifs <;> simp
    · split_ifs <;> simp
    · intro p hp q hq
      split_ifs at hp hq with h1 h2 <;> simp at hp hq
      subst hp; subst hq; simp

theorem pieces_numbers (layer : GBranch G.tree → ℕ) (ℓ : Lad G) (_hL : ℓ.IsL) (k : ℕ) (hk : k ≤ ℓ.1) :
    ℓ.1 * 2 + 2 ≤ Lad.TS (ℓ.pieces (rangesAvoiding ℓ.1 k)) + 6 ∧
    ℓ.inc layer ≤ Lad.IS layer (ℓ.pieces (rangesAvoiding ℓ.1 k)) + 3 ∧
    (rangesAvoiding ℓ.1 k).length ≤ 2 := by
  have hps := rangesAvoiding_props ℓ.1 k hk
  have hdecomp : ℓ.inc layer = (∑ i ∈ Finset.Ico 0 k, ℓ.rungInc layer i) + ℓ.rungInc layer k +
      ∑ i ∈ Finset.Ico (k + 1) (ℓ.1 + 1), ℓ.rungInc layer i := by
    rw [Lad.inc_eq_sum, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) (by omega : k ≤ ℓ.1 + 1),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : k < ℓ.1 + 1)]
    ring
  have hA : ∑ i ∈ Finset.Ico 0 k, ℓ.rungInc layer i ≤ k := by
    calc _ ≤ ∑ _i ∈ Finset.Ico 0 k, 1 := Finset.sum_le_sum (fun i _ => Lad.rungInc_le_one layer ℓ i)
      _ = k := by simp
  have hB : ∑ i ∈ Finset.Ico (k + 1) (ℓ.1 + 1), ℓ.rungInc layer i ≤ ℓ.1 - k := by
    calc _ ≤ ∑ _i ∈ Finset.Ico (k + 1) (ℓ.1 + 1), 1 := Finset.sum_le_sum (fun i _ => Lad.rungInc_le_one layer ℓ i)
      _ = ℓ.1 - k := by simp
  have hr : ℓ.rungInc layer k ≤ 1 := Lad.rungInc_le_one layer ℓ k
  unfold rangesAvoiding
  by_cases h1 : 2 ≤ k <;> by_cases h2 : k + 2 ≤ ℓ.1
  · simp only [h1, h2, ite_true, Lad.pieces, Lad.TS, Lad.IS, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, List.length_append, List.length_cons,
      List.length_nil]
    rw [Lad.sub_inc layer ℓ 0 (k - 1) (by omega), Lad.sub_inc layer ℓ (k + 1) (ℓ.1 - k - 1) (by omega)]
    have e1 : (Finset.Ico 0 (0 + (k - 1) + 1)) = Finset.Ico 0 k := by congr 1; omega
    have e2 : (Finset.Ico (k + 1) (k + 1 + (ℓ.1 - k - 1) + 1)) = Finset.Ico (k + 1) (ℓ.1 + 1) := by
      congr 1; omega
    rw [e1, e2]
    refine ⟨?_, ?_, ?_⟩ <;> (try simp only [Lad.sub]) <;> omega
  · simp only [h1, h2, ite_true, ite_false, Lad.pieces, Lad.TS, Lad.IS, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, List.append_nil,
      List.length_cons, List.length_nil]
    rw [Lad.sub_inc layer ℓ 0 (k - 1) (by omega)]
    have e1 : (Finset.Ico 0 (0 + (k - 1) + 1)) = Finset.Ico 0 k := by congr 1; omega
    rw [e1]
    refine ⟨?_, ?_, ?_⟩ <;> (try simp only [Lad.sub]) <;> omega
  · simp only [h1, h2, ite_true, ite_false, Lad.pieces, Lad.TS, Lad.IS, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, List.nil_append,
      List.length_cons, List.length_nil]
    rw [Lad.sub_inc layer ℓ (k + 1) (ℓ.1 - k - 1) (by omega)]
    have e2 : (Finset.Ico (k + 1) (k + 1 + (ℓ.1 - k - 1) + 1)) = Finset.Ico (k + 1) (ℓ.1 + 1) := by
      congr 1; omega
    rw [e2]
    refine ⟨?_, ?_, ?_⟩ <;> (try simp only [Lad.sub]) <;> omega
  · simp only [h1, h2, ite_false, Lad.pieces, Lad.TS, Lad.IS, List.map_nil, List.sum_nil, List.append_nil,
      List.length_nil]
    refine ⟨?_, ?_, ?_⟩ <;> omega

end WaveTurbulence.CoarseSpliced
