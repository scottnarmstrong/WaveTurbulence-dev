/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VinePrependSequence
public import WaveTurbulence.Foundations.Molecule.VineReverseSequence
import Mathlib.Tactic

/-! # Complete-frame distinctness under adjoining and reversing external ports -/

public section
namespace WaveTurbulence.Vine

/-- An external atom can be prepended to a distinct finite rail. -/
theorem prependRail_injective {V : Type*} (f : ℕ → V) (p : V) (n : ℕ)
    (hf : Function.Injective (fun i : Fin (n+2) => f i.1))
    (hp : ∀ i,i ≤ n+1 → p ≠ f i) :
    Function.Injective (fun i : Fin (n+3) => prependRail f p i.1) := by
  intro i j he
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j => exact False.elim ((hp j.1 (by omega)) he)
  | succ i =>
    cases j using Fin.cases with
    | zero => exact False.elim ((hp i.1 (by omega)) he.symm)
    | succ j =>
      exact congrArg Fin.succ (hf he)

/-- Distinct external ports remain separate after both rails are prepended. -/
theorem prependRail_pair_injective {V : Type*} (u v : ℕ → V) (p q : V) (n : ℕ)
    (hd : Function.Injective (Sum.elim (fun i : Fin (n+2) => u i.1)
      (fun i : Fin (n+2) => v i.1)))
    (hp : ∀ i,i ≤ n+1 → p ≠ u i ∧ p ≠ v i)
    (hq : ∀ i,i ≤ n+1 → q ≠ u i ∧ q ≠ v i) (hpq : p ≠ q) :
    Function.Injective (Sum.elim (fun i : Fin (n+3) => prependRail u p i.1)
      (fun i : Fin (n+3) => prependRail v q i.1)) := by
  obtain ⟨hu,hv,huv⟩ := Sum.elim_injective.mp hd
  apply Sum.elim_injective.mpr
  refine ⟨prependRail_injective u p n hu (fun i hi => (hp i hi).1),
    prependRail_injective v q n hv (fun i hi => (hq i hi).2),?_⟩
  intro i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact hpq
    | succ j => exact (hp j.1 (by omega)).2
  | succ i =>
    cases j using Fin.cases with
    | zero => exact Ne.symm (hq i.1 (by omega)).1
    | succ j => exact huv i j

/-- Reversing the order of a complete finite frame preserves distinctness. -/
theorem reverseRail_pair_injective {V : Type*} (u v : ℕ → V) (n : ℕ)
    (hd : Function.Injective (Sum.elim (fun i : Fin (n+2) => u i.1)
      (fun i : Fin (n+2) => v i.1))) :
    Function.Injective (Sum.elim (fun i : Fin (n+2) => u (n+1-i.1))
      (fun i : Fin (n+2) => v (n+1-i.1))) := by
  let e : Fin (n+2) ⊕ Fin (n+2) → Fin (n+2) ⊕ Fin (n+2) := Sum.map Fin.rev Fin.rev
  have he : Function.Injective e := Sum.map_injective.mpr
    ⟨Fin.rev_injective,Fin.rev_injective⟩
  have hh := hd.comp he
  convert hh using 1
  funext i
  cases i <;> simp only [e,Sum.map_inl,Sum.map_inr,Sum.elim_inl,Sum.elim_inr,
    Function.comp_apply,Fin.val_rev] <;> congr 1 <;> omega


/-- A separated atom stays outside a frame after two external ports are added. -/
theorem prependRail_separation {V : Type*} (u v : ℕ → V) (p q c : V) (n : ℕ)
    (hc : ∀ i,i ≤ n+1 → c ≠ u i ∧ c ≠ v i) (hp : c ≠ p) (hq : c ≠ q) :
    ∀ i,i ≤ n+2 → c ≠ prependRail u p i ∧ c ≠ prependRail v q i := by
  intro i hi
  cases i with
  | zero => exact ⟨hp,hq⟩
  | succ i => exact hc i (by omega)

end WaveTurbulence.Vine
