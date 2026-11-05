/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.MiniPorts

/-! # Completeness of the two A and six B mini tables

The three internal bonds at a parent-free vertex reverse conservation signs.
Their completed four-port permutation must be exactly one of the eight pinned
mini patterns. This finite lemma checks the full literal port tables.
-/

public section
namespace WaveTurbulence.Reg.Skeleton

/-- Finite scalar table, with all four function values explicit. -/
theorem mini_table_finite (s t : Bool) (a : Fin 4) : ∀ b c d : Fin 4,
    Function.Injective (![a,b,c,d] : Fin 4 → Fin 4) →
    (∀ i : Fin 3, slotSign (if s then (1 : ℤˣ) else -1) i =
      -portSign (if t then (1 : ℤˣ) else -1) (![a,b,c,d] i.succ)) →
    ((∃ k : MiniCplCode, (![a,b,c,d] : Fin 4 → Fin 4) = miniAMap k ∧
      (if t then (1 : ℤˣ) else -1) = -(if s then (1 : ℤˣ) else -1)) ∨
     ∃ m : MiniTreeCode, (![a,b,c,d] : Fin 4 → Fin 4) = miniBMap m ∧
      (if t then (1 : ℤˣ) else -1) = slotSign (if s then (1 : ℤˣ) else -1) m.c) := by
  cases s <;> cases t <;> fin_cases a <;> decide

/-- Exactly the source's two mini couples or six mini trees are compatible with
all three internal source signs. No arbitrary port permutation is admitted. -/
theorem mini_port_classification (ζ η : ℤˣ) (p : Equiv.Perm (Fin 4))
    (h : ∀ i : Fin 3, slotSign ζ i = -portSign η (p i.succ)) :
    (∃ c : MiniCplCode, p = miniAPerm c ∧ η = -ζ) ∨
      ∃ m : MiniTreeCode, p = miniBPerm m ∧ η = slotSign ζ m.c := by
  obtain ⟨s,hs⟩ : ∃ s : Bool, (if s then (1 : ℤˣ) else -1) = ζ := by
    rcases Int.units_eq_one_or ζ with he | he
    · exact ⟨true,he.symm⟩
    · exact ⟨false,he.symm⟩
  obtain ⟨t,ht⟩ : ∃ t : Bool, (if t then (1 : ℤˣ) else -1) = η := by
    rcases Int.units_eq_one_or η with he | he
    · exact ⟨true,he.symm⟩
    · exact ⟨false,he.symm⟩
  have hv : (fun i => p i) = (![p 0,p 1,p 2,p 3] : Fin 4 → Fin 4) := by
    funext i
    fin_cases i <;> rfl
  have hi : Function.Injective (![p 0,p 1,p 2,p 3] : Fin 4 → Fin 4) := by
    rw [← hv]
    exact p.injective
  have hh : ∀ i : Fin 3, slotSign (if s then (1 : ℤˣ) else -1) i =
      -portSign (if t then (1 : ℤˣ) else -1) (![p 0,p 1,p 2,p 3] i.succ) := by
    rw [hs,ht,← hv]
    exact h
  have hc := mini_table_finite s t (p 0) (p 1) (p 2) (p 3) hi hh
  rw [hs,ht] at hc
  rcases hc with ⟨c,hc,hsign⟩ | ⟨m,hm,hsign⟩
  · refine Or.inl ⟨c,?_,hsign⟩
    apply Equiv.ext
    intro i
    exact congrFun (hv.trans hc) i
  · refine Or.inr ⟨m,?_,hsign⟩
    apply Equiv.ext
    intro i
    exact congrFun (hv.trans hm) i

end WaveTurbulence.Reg.Skeleton
