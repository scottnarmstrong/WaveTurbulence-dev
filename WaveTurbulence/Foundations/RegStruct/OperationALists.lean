/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.PairSubstitution
public import WaveTurbulence.Foundations.RegStruct.DecodedPairProperties

/-! # Literal pairing-list fidelity of operation A (DH21 Proposition 4.8)

A source history removes one pair and appends three new pairs. Code substitution
splices those three pairs in place. No duplicates occur, so these lists differ
only by permutation. Normalization retains the full pair list up to permutation.
-/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Splicing at a pair not present leaves the entire list unchanged. -/
theorem splicePairs_of_not_mem {α : Type*} [DecidableEq α]
    (P : List α) (t : α) (S : List α) (ht : t ∉ P) : splicePairs P t S = P := by
  cases P with
  | nil => rfl
  | cons a l =>
    have ha : a ≠ t := fun he => ht (he ▸ List.mem_cons_self)
    have hl : t ∉ l := fun h => ht (List.mem_cons_of_mem a h)
    simp only [splicePairs,List.flatMap_cons,ha,ite_false,List.singleton_append]
    exact congrArg (List.cons a) (splicePairs_of_not_mem l t S hl)
termination_by structural P

/-- One literal step of list splicing. -/
theorem splicePairs_cons {α : Type*} [DecidableEq α]
    (a : α) (P : List α) (t : α) (S : List α) :
    splicePairs (a :: P) t S = (if a = t then S else [a]) ++ splicePairs P t S := rfl

/-- For a duplicate-free list, splicing one pair agrees with erasing then appending it. -/
theorem splicePairs_perm_erase_append {α : Type*} [DecidableEq α] [BEq α] [LawfulBEq α]
    (P : List α) (t : α) (S : List α) (hP : P.Nodup) (ht : t ∈ P) :
    (splicePairs P t S).Perm (P.erase t ++ S) := by
  cases P with
  | nil => exact (List.not_mem_nil ht).elim
  | cons a l =>
    obtain ⟨hna,hnl⟩ := List.nodup_cons.mp hP
    by_cases he : a = t
    · subst a
      rw [splicePairs_cons,ite_eq_left rfl]
      rw [splicePairs_of_not_mem l t S hna,List.erase_cons_head]
      exact List.perm_append_comm
    · have htl : t ∈ l := (List.mem_cons.mp ht).resolve_left (Ne.symm he)
      have herase : (a :: l).erase t = a :: l.erase t :=
        List.erase_cons_tail (by simpa only [beq_iff_eq] using he)
      rw [herase,List.cons_append]
      rw [splicePairs_cons,ite_eq_right he,List.singleton_append]
      exact (splicePairs_perm_erase_append l t S hnl htl).cons a
termination_by structural P

/-- The mini-couple inserted by source operation A. -/
def miniCoupleCode (c : MiniCplCode) : RegCpl := .type1 c .triv .triv .triv

/-- Source operation A on structure data, with the final uniqueness conditions enforced. -/
def operationA (Q : RegCpl) (x y : Fin 2 × Path) (c : MiniCplCode) : RegCpl :=
  normalizeCouple (substituteCouplePair Q (0,[]) (1,[]) x y (miniCoupleCode c))

/-- Source operation A adds exactly two listed leaf pairs. -/
theorem raw_opA_pairs_length (R : RawCpl) (x y : Fin 2 × Path) (c : MiniCplCode)
    (h : (x,y) ∈ R.2) : (R.opA x y c).2.length = R.2.length + 2 := by
  have he := List.length_erase_add_one h
  change (R.2.erase (x,y) ++ [_,_,_]).length = _
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega

/-- The new code and the source A-step retain exactly the same literal oriented pair list. -/
theorem operationA_pairs_perm (Q : RegCpl) (x y : Fin 2 × Path) (c : MiniCplCode)
    (h : (x,y) ∈ Q.raw.2) :
    (operationA Q x y c).raw.2.Perm (Q.raw.opA x y c).2 := by
  apply (normalizeCouple_pairs_perm _).trans
  change ((substituteCouplePair Q (0,[]) (1,[]) x y (miniCoupleCode c)).pairsAt (0,[]) (1,[])).Perm _
  rw [substituteCouplePair_pairsAt]
  have hp := splicePairs_perm_erase_append Q.raw.2 (x,y) ((miniCoupleCode c).pairsAt x y)
    (decodedPair_nodup Q) h
  simpa only [miniCoupleCode,RegCpl.pairsAt,RawCpl.opA,RegCpl.raw,
    List.singleton_append,List.cons_append,List.nil_append] using hp

/-- Operation A on a genuine listed pair adds exactly two branching nodes. -/
theorem operationA_size (Q : RegCpl) (x y : Fin 2 × Path) (c : MiniCplCode)
    (h : (x,y) ∈ Q.raw.2) : (operationA Q x y c).size = Q.size + 2 := by
  have hl := (operationA_pairs_perm Q x y c h).length_eq
  rw [raw_opA_pairs_length Q.raw x y c h] at hl
  change ((operationA Q x y c).pairsAt (0,[]) (1,[])).length =
    (Q.pairsAt (0,[]) (1,[])).length + 2 at hl
  rw [couple_pairsAt_length,couple_pairsAt_length] at hl
  omega

/-- Operation A returns well-formed structure data without any normalization premise. -/
theorem operationA_wf (Q : RegCpl) (x y : Fin 2 × Path) (c : MiniCplCode) :
    (operationA Q x y c).wf = true := normalizeCouple_wf _

end WaveTurbulence.Reg
