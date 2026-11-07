/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
/-! # VINE-COUNT part 6: counting coordinates that are constrained block by block.

The chart coordinates `x : Fin n → A` split into a joint block, `m` pair blocks and a core block; if each block lies in a
finite set the number of coordinate tuples is at most the product of the block counts. -/
@[expose] public section
set_option autoImplicit false
open Finset Set
namespace WaveTurbulence.VineCount

/-- Block-wise counting: the coordinate tuple is determined by its blocks. -/
theorem ncard_blocks_le {A : Type*} {n m k : ℕ} (e0 : Fin n) (xs ys : Fin m → Fin n) (us : Fin k → Fin n)
    (hcov : ∀ i : Fin n, i = e0 ∨ (∃ j, i = xs j ∨ i = ys j) ∨ ∃ c, i = us c)
    (X : Set (Fin n → A)) (B : Set A) (hB : B.Finite) (P : Fin m → Set (A × A)) (hP : ∀ j, (P j).Finite)
    (U : Set (Fin k → A)) (hU : U.Finite)
    (h0 : ∀ x ∈ X, x e0 ∈ B) (hp : ∀ x ∈ X, ∀ j, (x (xs j), x (ys j)) ∈ P j)
    (hu : ∀ x ∈ X, (fun c => x (us c)) ∈ U) :
    X.Finite ∧ X.ncard ≤ B.ncard * (∏ j, (P j).ncard) * U.ncard := by
  classical
  let T : Finset (A × (Fin m → A × A) × (Fin k → A)) :=
    hB.toFinset ×ˢ (Fintype.piFinset fun j => (hP j).toFinset) ×ˢ hU.toFinset
  let Ψ : (Fin n → A) → A × (Fin m → A × A) × (Fin k → A) :=
    fun x => (x e0, fun j => (x (xs j), x (ys j)), fun c => x (us c))
  have hinj : Function.Injective Ψ := by
    intro x x' h
    have h1 : x e0 = x' e0 := congrArg Prod.fst h
    have h2 : (fun j => (x (xs j), x (ys j))) = fun j => (x' (xs j), x' (ys j)) := congrArg (fun t => t.2.1) h
    have h3 : (fun c => x (us c)) = fun c => x' (us c) := congrArg (fun t => t.2.2) h
    funext i
    rcases hcov i with rfl | ⟨j, rfl | rfl⟩ | ⟨c, rfl⟩
    · exact h1
    · exact congrArg Prod.fst (congrFun h2 j)
    · exact congrArg Prod.snd (congrFun h2 j)
    · exact congrFun h3 c
  have hmaps : ∀ x ∈ X, Ψ x ∈ (T : Set _) := by
    intro x hx
    simp only [T, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Set.Finite.mem_toFinset,
      Fintype.mem_piFinset]
    exact ⟨h0 x hx, fun j => hp x hx j, hu x hx⟩
  have hfin : X.Finite := (T.finite_toSet.preimage hinj.injOn).subset fun x hx => hmaps x hx
  refine ⟨hfin, ?_⟩
  have h1 := Set.ncard_le_ncard_of_injOn Ψ hmaps hinj.injOn T.finite_toSet
  rw [Set.ncard_coe_finset] at h1
  refine h1.trans ?_
  simp only [T, Finset.card_product, Fintype.card_piFinset, Set.ncard_eq_toFinset_card _ hB,
    Set.ncard_eq_toFinset_card _ hU]
  have : ∀ j, ((hP j).toFinset).card = (P j).ncard := fun j => (Set.ncard_eq_toFinset_card _ (hP j)).symm
  simp only [this, mul_assoc]
  exact le_rfl

/-- The real-valued version of `ncard_blocks_le`. -/
theorem ncard_blocks_le_real {A : Type*} {n m k : ℕ} (e0 : Fin n) (xs ys : Fin m → Fin n) (us : Fin k → Fin n)
    (hcov : ∀ i : Fin n, i = e0 ∨ (∃ j, i = xs j ∨ i = ys j) ∨ ∃ c, i = us c)
    (X : Set (Fin n → A)) (B : Set A) (hB : B.Finite) (P : Fin m → Set (A × A)) (hP : ∀ j, (P j).Finite)
    (U : Set (Fin k → A)) (hU : U.Finite)
    (h0 : ∀ x ∈ X, x e0 ∈ B) (hp : ∀ x ∈ X, ∀ j, (x (xs j), x (ys j)) ∈ P j)
    (hu : ∀ x ∈ X, (fun c => x (us c)) ∈ U) (bB : ℝ) (hbB : (B.ncard : ℝ) ≤ bB) (bP : Fin m → ℝ)
    (hbP : ∀ j, ((P j).ncard : ℝ) ≤ bP j) (bU : ℝ) (hbU : (U.ncard : ℝ) ≤ bU) :
    X.Finite ∧ (X.ncard : ℝ) ≤ bB * (∏ j, bP j) * bU := by
  obtain ⟨hfin, hle⟩ := ncard_blocks_le e0 xs ys us hcov X B hB P hP U hU h0 hp hu
  refine ⟨hfin, ?_⟩
  calc (X.ncard : ℝ) ≤ ((B.ncard * (∏ j, (P j).ncard) * U.ncard : ℕ) : ℝ) := by exact_mod_cast hle
    _ = (B.ncard : ℝ) * (∏ j, ((P j).ncard : ℝ)) * (U.ncard : ℝ) := by push_cast; rfl
    _ ≤ bB * (∏ j, bP j) * bU := by
        have h1 : (∏ j, ((P j).ncard : ℝ)) ≤ ∏ j, bP j :=
          Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => hbP j)
        have hpos : 0 ≤ ∏ j, ((P j).ncard : ℝ) := Finset.prod_nonneg fun j _ => Nat.cast_nonneg _
        have hbB0 : 0 ≤ bB := (Nat.cast_nonneg _).trans hbB
        have hbP0 : 0 ≤ ∏ j, bP j := hpos.trans h1
        exact mul_le_mul (mul_le_mul hbB h1 hpos hbB0) hbU (Nat.cast_nonneg _) (mul_nonneg hbB0 hbP0)

/-- Counting a set through an injection into a union of fibres over a finite index set. -/
theorem ncard_fibre_bound {α β γ : Type*} [DecidableEq α] (R : Finset α) (Xr : α → Set β) (B : ℝ)
    (hX : ∀ r ∈ R, (Xr r).Finite ∧ ((Xr r).ncard : ℝ) ≤ B)
    (f : Set γ) (Ψ : γ → α × β) (hmaps : ∀ k ∈ f, (Ψ k).1 ∈ R ∧ (Ψ k).2 ∈ Xr (Ψ k).1)
    (hinj : Set.InjOn Ψ f) : f.Finite ∧ (f.ncard : ℝ) ≤ R.card * B := by
  let T : Set (α × β) := ⋃ r ∈ R, (Prod.mk r) '' Xr r
  have hTfin : T.Finite := Set.Finite.biUnion R.finite_toSet fun r hr => (hX r hr).1.image _
  have hmem : ∀ k ∈ f, Ψ k ∈ T := by
    intro k hk
    obtain ⟨h1, h2⟩ := hmaps k hk
    exact Set.mem_iUnion₂.mpr ⟨(Ψ k).1, h1, (Ψ k).2, h2, rfl⟩
  have hffin : f.Finite := Set.Finite.of_injOn hmem hinj hTfin
  refine ⟨hffin, ?_⟩
  have h1 : f.ncard ≤ T.ncard := Set.ncard_le_ncard_of_injOn Ψ hmem hinj hTfin
  have h2 : T.ncard ≤ ∑ r ∈ R, ((Prod.mk r) '' Xr r).ncard := Finset.set_ncard_biUnion_le R _
  have h3 : ∀ r ∈ R, (((Prod.mk r) '' Xr r).ncard : ℝ) ≤ B := fun r hr =>
    le_trans (by exact_mod_cast Set.ncard_image_le (hX r hr).1) (hX r hr).2
  calc (f.ncard : ℝ) ≤ (T.ncard : ℝ) := by exact_mod_cast h1
    _ ≤ ((∑ r ∈ R, ((Prod.mk r) '' Xr r).ncard : ℕ) : ℝ) := by exact_mod_cast h2
    _ = ∑ r ∈ R, (((Prod.mk r) '' Xr r).ncard : ℝ) := by push_cast; rfl
    _ ≤ ∑ r ∈ R, B := Finset.sum_le_sum h3
    _ = R.card * B := by simp

end WaveTurbulence.VineCount
