/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw

/-! # The exact two A and six B ordered port permutations

These are the pinned B2 mini-couple/mini-tree tables expressed in four ports.
The free attachment ports complete the three internal bonds to a permutation.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Conservation signs at a branch: parent, left, middle, right. -/
def portSign (ζ : ℤˣ) : Fin 4 → ℤˣ := Fin.cases (-ζ) (slotSign ζ)

/-- The two mini-couple tables, including the artificial parent-to-parent attachment pair. -/
def miniAMap (c : MiniCplCode) : Fin 4 → Fin 4 := Fin.cases 0 (fun i => (c.partner i).succ)

theorem miniAMap_involutive (c : MiniCplCode) : Function.Involutive (miniAMap c) := by
  intro i
  fin_cases c <;> fin_cases i <;> decide

def miniAPerm (c : MiniCplCode) : Equiv.Perm (Fin 4) :=
  ⟨miniAMap c,miniAMap c,miniAMap_involutive c,miniAMap_involutive c⟩

/-- Upper parent -> lower lone slot; upper continuing child -> lower parent;
red and green child slots -> their pinned lower partners. -/
def miniBMap (m : MiniTreeCode) : Fin 4 → Fin 4 :=
  Fin.cases m.lone.succ (fun i =>
    if i = m.c then 0 else if i = m.red.1 then m.red.2.succ else m.green.2.succ)

def miniBInv (m : MiniTreeCode) : Fin 4 → Fin 4 :=
  Fin.cases m.c.succ (fun i =>
    if i = m.lone then 0 else if i = m.red.2 then m.red.1.succ else m.green.1.succ)

theorem miniBInv_left (m : MiniTreeCode) : Function.LeftInverse (miniBInv m) (miniBMap m) := by
  obtain ⟨c,b⟩ := m
  intro i
  fin_cases c <;> fin_cases b <;> fin_cases i <;> decide

theorem miniBInv_right (m : MiniTreeCode) : Function.RightInverse (miniBInv m) (miniBMap m) := by
  obtain ⟨c,b⟩ := m
  intro i
  fin_cases c <;> fin_cases b <;> fin_cases i <;> decide

def miniBPerm (m : MiniTreeCode) : Equiv.Perm (Fin 4) :=
  ⟨miniBMap m,miniBInv m,miniBInv_left m,miniBInv_right m⟩

/-- Every completed A port pair has opposite conservation signs. -/
theorem miniA_port_sign (c : MiniCplCode) (ζ : ℤˣ) (i : Fin 4) :
    portSign ζ i = -portSign (-ζ) (miniAPerm c i) := by
  rcases Int.units_eq_one_or ζ with rfl | rfl <;> fin_cases c <;> fin_cases i <;> decide

/-- Every completed B port pair has opposite conservation signs, including the free attachment pair. -/
theorem miniB_port_sign (m : MiniTreeCode) (ζ : ℤˣ) (i : Fin 4) :
    portSign ζ i = -portSign (slotSign ζ m.c) (miniBPerm m i) := by
  obtain ⟨c,b⟩ := m
  rcases Int.units_eq_one_or ζ with rfl | rfl <;> fin_cases c <;> fin_cases b <;> fin_cases i <;> decide

end WaveTurbulence.Reg.Skeleton
