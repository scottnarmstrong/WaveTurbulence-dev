/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CodeWordLengths
public import WaveTurbulence.Foundations.RegStruct.FiniteCodes

/-! # Exponential bound for the drafted structure data (DH21 Corollary 4.9)

This counts codes. Transferring the bound to source regular objects additionally
requires the range and uniqueness theorems; neither is assumed here.
-/

@[expose] public section

namespace WaveTurbulence.Reg

/-- A bounded word is embedded into a fixed finite product, with `none` padding. -/
def wordSlots {α : Type*} (N : ℕ) (l : {l : List α // l.length ≤ N}) : Fin N → Option α :=
  fun i => l.1[i.val]?

theorem wordSlots_injective {α : Type*} (N : ℕ) : Function.Injective (wordSlots (α := α) N) := by
  intro a b h
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases hi : i < N
  · exact congrFun h ⟨i,hi⟩
  · rw [List.getElem?_eq_none (by have := a.2; omega),
      List.getElem?_eq_none (by have := b.2; omega)]

/-- Couple-code words of order `2m`, as bounded words. -/
def boundedCoupleWord (m : ℕ) (Q : {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * m}) :
    {l : List (Fin 11) // l.length ≤ 8 * m + 1} :=
  ⟨coupleWord Q.1, by have h := coupleWord_length Q.1 Q.2.1; rw [Q.2.2] at h; omega⟩

/-- Tree-code words of order `2m`, as bounded words. -/
def boundedChainWord (m : ℕ) (X : {X : RegChain // X.wf = true ∧ X.size = 2 * m}) :
    {l : List (Fin 11) // l.length ≤ 8 * m + 1} :=
  ⟨chainWord X.1, by have h := (chainWord_length X.1 X.2.1).1; rw [X.2.2] at h; omega⟩

theorem boundedCoupleWord_injective (m : ℕ) : Function.Injective (boundedCoupleWord m) := by
  intro Q R h
  exact Subtype.ext (coupleWord_injective (congrArg Subtype.val h))

theorem boundedChainWord_injective (m : ℕ) : Function.Injective (boundedChainWord m) := by
  intro X Y h
  exact Subtype.ext (chainWord_injective (congrArg Subtype.val h))

/-- Number of well-formed couple codes of order `2m`. -/
noncomputable def coupleCodeCount (m : ℕ) : ℕ := Nat.card {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * m}

/-- Number of well-formed tree codes of order `2m` (root sign is a separate datum). -/
noncomputable def chainCodeCount (m : ℕ) : ℕ := Nat.card {X : RegChain // X.wf = true ∧ X.size = 2 * m}

/-- Finite-product counting bound for couple structure data. -/
theorem coupleCodeCount_le (m : ℕ) : coupleCodeCount m ≤ 12 ^ (8 * m + 1) := by
  have h := Nat.card_le_card_of_injective
    (fun Q => wordSlots (8*m+1) (boundedCoupleWord m Q))
    ((wordSlots_injective _).comp (boundedCoupleWord_injective m))
  simpa only [coupleCodeCount, Nat.card_fun, Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_option, Fintype.card_fin] using h

/-- Finite-product counting bound for paired-tree structure data. -/
theorem chainCodeCount_le (m : ℕ) : chainCodeCount m ≤ 12 ^ (8 * m + 1) := by
  have h := Nat.card_le_card_of_injective
    (fun X => wordSlots (8*m+1) (boundedChainWord m X))
    ((wordSlots_injective _).comp (boundedChainWord_injective m))
  simpa only [chainCodeCount, Nat.card_fun, Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_option, Fintype.card_fin] using h

/-- A well-formed zero-order couple code is trivial. -/
theorem eq_triv_of_wf_size_zero (Q : RegCpl) (hw : Q.wf = true) (hs : Q.size = 0) :
    Q = .triv := by
  cases Q with
  | triv => rfl
  | type1 c a b d => simp only [RegCpl.size] at hs; omega
  | type2 x y q =>
    simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hw
    simp only [RegCpl.size] at hs
    rcases Bool.and_eq_false_iff.mp hw.2 with hx | hy
    · have := chain_size_pos_of_not_isNil hx; omega
    · have := chain_size_pos_of_not_isNil hy; omega

/-- A zero-order chain code is empty, independently of well-formedness. -/
theorem eq_nil_of_size_zero (X : RegChain) (hs : X.size = 0) : X = .nil := by
  cases X with
  | nil => rfl
  | pair m r g i s => simp only [RegChain.size] at hs; omega

@[simp] theorem coupleCodeCount_zero : coupleCodeCount 0 = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨.triv, rfl, rfl⟩, fun Q => Subtype.ext ?_⟩
  exact eq_triv_of_wf_size_zero Q.1 Q.2.1 Q.2.2

@[simp] theorem chainCodeCount_zero : chainCodeCount 0 = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨.nil, rfl, rfl⟩, fun X => Subtype.ext ?_⟩
  exact eq_nil_of_size_zero X.1 X.2.2

/-- A single absolute exponential base works for all couple-code orders, including zero. -/
theorem coupleCodeCount_le_pow (m : ℕ) : coupleCodeCount m ≤ (12 ^ 9) ^ m := by
  by_cases hm : m = 0
  · subst m; simp
  · calc
      coupleCodeCount m ≤ 12 ^ (8*m+1) := coupleCodeCount_le m
      _ ≤ 12 ^ (9*m) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = (12^9)^m := pow_mul _ _ _

/-- The same absolute exponential bound holds for tree codes of either fixed root sign. -/
theorem chainCodeCount_le_pow (m : ℕ) : chainCodeCount m ≤ (12 ^ 9) ^ m := by
  by_cases hm : m = 0
  · subst m; simp
  · calc
      chainCodeCount m ≤ 12 ^ (8*m+1) := chainCodeCount_le m
      _ ≤ 12 ^ (9*m) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = (12^9)^m := pow_mul _ _ _

end WaveTurbulence.Reg
