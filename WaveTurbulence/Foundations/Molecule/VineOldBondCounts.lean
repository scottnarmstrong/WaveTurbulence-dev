/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRestrictInsertion
import Mathlib.Tactic

/-! # Rung insertion never increases multiplicity between old atom labels -/

public section
namespace WaveTurbulence.Vine

/-- Erasing one list occurrence can only lower every encoded bond count. -/
theorem erase_count_le (es : List (ℕ×ℕ)) (e f : ℕ×ℕ) : (es.erase f).count e ≤ es.count e := by
  by_cases hf : f ∈ es
  · have hh := List.Perm.count_eq (List.perm_cons_erase hf) e
    simp only [List.count_cons] at hh
    omega
  · rw [List.erase_of_not_mem hf]

/-- A nonempty rail of fresh labels cannot contain a bond with two old endpoints. -/
theorem old_pair_not_mem_rail (N a b u v : ℕ) (ws : List ℕ) (hu : u<N) (hv : v<N)
    (hws : ws ≠ []) (hw : ∀ w ∈ ws,N ≤ w) : (u,v) ∉ railBonds a ws b := by
  cases ws with
  | nil => exact False.elim (hws rfl)
  | cons w ws =>
    intro he
    change (u,v) ∈ (a,w)::railBonds w ws b at he
    rcases List.mem_cons.mp he with he | he
    · have hvw := congrArg Prod.snd he
      have hn := hw w List.mem_cons_self
      simp only at hvw
      omega
    · have hf := (List.of_mem_zip he).1
      change u ∈ w::ws at hf
      have hnu : N ≤ u := by
        rcases List.mem_cons.mp hf with he | he
        · exact he ▸ hw w List.mem_cons_self
        · exact hw u (List.mem_cons_of_mem _ he)
      omega

/-- A single insertion adds no old-to-old encoded bond occurrence. The
selected old rail occurrences may be erased but cannot be replenished. -/
theorem insertRungs_old_count_le (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k u v : ℕ)
    (hu : u<T.n) (hv : v<T.n) : (insertRungs T s k).bonds.count (u,v) ≤ T.bonds.count (u,v) := by
  by_cases hk : k=0
  · rw [hk,insertRungs_zero]
  · have hws (N : ℕ) : (List.range k).map (N+·) ≠ [] := by
      intro he
      have hh := congrArg List.length he
      simp only [List.length_map,List.length_range,List.length_nil] at hh
      exact hk hh
    have hU : ∀ w ∈ (List.range k).map (T.n+·),T.n ≤ w := by
      intro w hw
      obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hw
      omega
    have hV : ∀ w ∈ (List.range k).map (T.n+k+·),T.n ≤ w := by
      intro w hw
      obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hw
      omega
    have hcU := List.count_eq_zero_of_not_mem (old_pair_not_mem_rail T.n s.1.1 s.1.2 u v _ hu hv (hws _) hU)
    have hcV := List.count_eq_zero_of_not_mem (old_pair_not_mem_rail T.n s.2.1 s.2.2 u v _ hu hv (hws _) hV)
    have hcR : (allocatedRungs T.n (T.n+k) k).count (u,v)=0 := by
      apply List.count_eq_zero_of_not_mem
      intro he
      obtain ⟨i,_hi,hei⟩ := allocatedRungs_mem he
      have huu := congrArg Prod.fst hei
      simp only at huu
      omega
    simp only [insertRungs,hk,ite_false,← allocatedRungs_eq_zip,List.count_append,hcU,hcV,hcR,Nat.add_zero]
    exact (erase_count_le (T.bonds.erase s.1) (u,v) s.2).trans (erase_count_le T.bonds (u,v) s.1)

/-- Every old bond multiplicity is nonincreasing through a finite insertion fold. -/
theorem fold_insertRungs_old_count_le (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (T : VineTemplate)
    (u v : ℕ) (hu : u<T.n) (hv : v<T.n) :
    (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds.count (u,v) ≤ T.bonds.count (u,v) := by
  induction xs generalizing T with
  | nil => exact le_rfl
  | cons sk xs ih =>
    rw [List.foldl_cons]
    have hu' : u<(insertRungs T sk.1 sk.2).n := by rw [insertRungs_atoms]; omega
    have hv' : v<(insertRungs T sk.1 sk.2).n := by rw [insertRungs_atoms]; omega
    exact (ih _ hu' hv').trans (insertRungs_old_count_le T sk.1 sk.2 u v hu hv)

/-- Arbitrary rung expansion never increases any old-core pair multiplicity. -/
theorem expand_old_count_le (X : VineType) (ks : List ℕ) (u v : ℕ)
    (hu : u<X.template.n) (hv : v<X.template.n) :
    (X.expand ks).bonds.count (u,v) ≤ X.template.bonds.count (u,v) :=
  fold_insertRungs_old_count_le _ _ u v hu hv

end WaveTurbulence.Vine
