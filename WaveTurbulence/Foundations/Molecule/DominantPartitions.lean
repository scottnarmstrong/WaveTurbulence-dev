/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.ChainPartitionIndices

/-! # Dominant partitions: exactly the successive disjoint adjacent pairs -/

@[expose] public section
namespace WaveTurbulence.Reg.PairPartition

/-- Every pair has adjacent endpoints in the literal ordered index set. -/
def Adjacent {n : ℕ} (P : PairPartition n) : Prop :=
  ∀ i : Fin n, (P.pair i).val = i.val+1 ∨ i.val = (P.pair i).val+1

/-- The source dominant partition `{0,1},{2,3},...`, in zero-based indexing. -/
def Dominant {n : ℕ} (P : PairPartition n) : Prop :=
  ∀ i : Fin n, if Even i.val then (P.pair i).val = i.val+1 else (P.pair i).val+1 = i.val

/-- Adjacent partners at even labels necessarily point to the next label. -/
theorem adjacent_even_partner {n : ℕ} (P : PairPartition n) (hP : P.Adjacent) (i : Fin n)
    (he : Even i.val) : (P.pair i).val = i.val+1 := by
  generalize hv : i.val = v
  induction v using Nat.strong_induction_on generalizing i with
  | h v ih =>
    rw [← hv]
    rcases hP i with hr | hl
    · exact hr
    · by_cases hsmall : i.val < 2
      · obtain ⟨k,hk⟩ := he
        have hi0 : i.val = 0 := by omega
        omega
      · let j : Fin n := ⟨i.val-2,by have := i.isLt; omega⟩
        have hj : Even j.val := by
          obtain ⟨k,hk⟩ := he
          refine ⟨k-1,?_⟩
          change i.val-2 = (k-1)+(k-1)
          omega
        have hprev := ih j.val (by change i.val-2 < v; omega) j hj rfl
        have hEq : P.pair j = P.pair i := Fin.ext (by change (P.pair j).val = i.val-2+1 at hprev; omega)
        have hji := congrArg Fin.val (P.pair_injective hEq)
        change i.val-2 = i.val at hji
        omega

/-- Pairwise adjacency is exactly the source's unique consecutive-pair dominant partition. -/
theorem dominant_iff_adjacent {n : ℕ} (P : PairPartition n) : P.Dominant ↔ P.Adjacent := by
  constructor
  · intro h i
    by_cases he : Even i.val
    · exact Or.inl (by simpa only [Dominant,he,ite_true] using h i)
    · have hh : (P.pair i).val+1 = i.val := by simpa only [Dominant,he,ite_false] using h i
      exact Or.inr hh.symm
  · intro h i
    by_cases he : Even i.val
    · rw [ite_eq_left he]
      exact P.adjacent_even_partner h i he
    · rw [ite_eq_right he]
      rcases h i with hr | hl
      · have hjEven : Even (P.pair i).val := by
          rcases Nat.even_or_odd i.val with hE | hO
          · exact (he hE).elim
          · obtain ⟨k,hk⟩ := hO
            exact ⟨k+1,by omega⟩
        have hp := P.adjacent_even_partner h (P.pair i) hjEven
        rw [P.involutive] at hp
        omega
      · exact hl.symm

/-- Concatenation preserves adjacency exactly on its two original index blocks. -/
theorem append_adjacent_iff {n m : ℕ} (P : PairPartition n) (Q : PairPartition m) :
    (P.append Q).Adjacent ↔ P.Adjacent ∧ Q.Adjacent := by
  constructor
  · intro h
    constructor
    · intro i
      have hh := h (Fin.castAdd m i)
      rw [append_pair_left] at hh
      simpa only [Fin.val_castAdd] using hh
    · intro j
      have hh := h (Fin.natAdd n j)
      rw [append_pair_right] at hh
      simp only [Fin.val_natAdd] at hh
      omega
  · rintro ⟨hP,hQ⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [append_pair_left]
      exact hP j
    · rw [append_pair_right]
      have hh := hQ j
      change n+(Q.pair j).val = (n+j.val)+1 ∨ n+j.val = (n+(Q.pair j).val)+1
      omega

/-- A source outer pair is adjacent only for the empty enclosed partition. -/
theorem enclose_adjacent_iff {n : ℕ} (P : PairPartition n) : P.enclose.Adjacent ↔ n = 0 := by
  constructor
  · intro h
    have hh := h 0
    change (enclosePartner P 0).val = 1 ∨ 0 = (enclosePartner P 0).val+1 at hh
    rw [enclosePartner_zero] at hh
    change n+1 = 1 ∨ 0 = (n+1)+1 at hh
    omega
  · rintro rfl i
    fin_cases i
    · left
      change (enclosePartner P 0).val = 1
      rw [enclosePartner_zero]
      rfl
    · right
      change 1 = (enclosePartner P (Fin.last 1)).val+1
      rw [enclosePartner_last]
      rfl

end WaveTurbulence.Reg.PairPartition
