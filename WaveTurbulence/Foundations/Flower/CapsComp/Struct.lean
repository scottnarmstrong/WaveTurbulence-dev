/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsComp.Carrier
/-! # A3b CAPS-COMP: structures (component partition and order labels) and the component equivalence `σ_x`

A *raw structure* `x : RawStr w N` is a map `x.1 : Fin (2w) → Fin (2w)` (the least tree of the component of each
capped tree) and order labels `x.2 : Fin w → Fin (N+1)` (the order of the component whose least tree is the
original tree `j`; `0` if `j` is not least). `Fintype.card (RawStr w N) = (2w)^(2w) (N+1)^w`.

For a valid raw structure (`ValidStr`) the components are indexed by `Fin x.m` (the least trees, in increasing
order), component `c` has `2 * x.R c` trees and order `x.n c`, and `sigmaX x hx sgn :
(Σ c : Fin x.m, Fin (2 * x.R c)) ≃ Fin (2w)` lists the trees of each component; a width-2 component is listed
with its `+` tree first (for the signature `sgn`), as `IsCanonGC` requires for couples. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsComp
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue WaveTurbulence.Flower.CapsId

/-- Raw structures. -/
abbrev RawStr (w N : ℕ) := (Fin (2 * w) → Fin (2 * w)) × (Fin w → Fin (N + 1))

theorem card_rawStr (w N : ℕ) : Fintype.card (RawStr w N) = (2 * w) ^ (2 * w) * (N + 1) ^ w := by
  simp [Fintype.card_prod]

/-- The original tree of a capped tree (`j ↦ j`, `w + j ↦ j`). -/
def origIdx {w : ℕ} (i : Fin (2 * w)) : Fin w := ⟨(i : ℕ) % w, Nat.mod_lt _ (by have := i.isLt; omega)⟩

@[simp] theorem origIdx_inl {w : ℕ} (j : Fin w) : origIdx (capσ w (.inl j)) = j := by
  ext; simp [origIdx, Nat.mod_eq_of_lt j.2]

@[simp] theorem origIdx_inr {w : ℕ} (j : Fin w) : origIdx (capσ w (.inr j)) = j := by
  ext; simp [origIdx, Nat.add_mod_left, Nat.mod_eq_of_lt j.2]

namespace RawStr

variable {w N : ℕ} (x : RawStr w N)

/-- The least trees of the components. -/
def reps : Finset (Fin (2 * w)) := univ.filter fun i => x.1 i = i

/-- The number of components. -/
def m : ℕ := x.reps.card

/-- The least tree of component `c` (increasing order). -/
def repAt (c : Fin x.m) : Fin (2 * w) := (x.reps.orderIsoOfFin rfl c : Fin (2 * w))

theorem repAt_mem (c : Fin x.m) : x.1 (x.repAt c) = x.repAt c := by
  have := (x.reps.orderIsoOfFin rfl c).2
  exact (mem_filter.1 this).2

theorem repAt_injective : Function.Injective x.repAt := fun c c' h => by
  have := Subtype.ext h
  exact (x.reps.orderIsoOfFin rfl).injective this

/-- The trees of component `c`. -/
def blk (c : Fin x.m) : Finset (Fin (2 * w)) := univ.filter fun i => x.1 i = x.repAt c

/-- Half the width of component `c`. -/
def R (c : Fin x.m) : ℕ := (x.blk c).card / 2

/-- The order label of component `c`. -/
def n (c : Fin x.m) : ℕ := (x.2 (origIdx (x.repAt c)) : ℕ)

end RawStr

/-- Validity of a raw structure. -/
structure ValidStr {w N : ℕ} (x : RawStr w N) : Prop where
  idem : ∀ i, x.1 (x.1 i) = x.1 i
  le : ∀ i, x.1 i ≤ i
  mate : ∀ j : Fin w, x.1 (capσ w (.inl j)) = x.1 (capσ w (.inr j))

namespace RawStr

variable {w N : ℕ} (x : RawStr w N)

/-- The component index of a tree. -/
def compIdx (hx : ValidStr x) (i : Fin (2 * w)) : Fin x.m :=
  (x.reps.orderIsoOfFin rfl).symm ⟨x.1 i, by simp [reps, hx.idem i]⟩

theorem repAt_compIdx (hx : ValidStr x) (i : Fin (2 * w)) : x.repAt (x.compIdx hx i) = x.1 i := by
  unfold repAt compIdx
  simp

theorem compIdx_eq_iff (hx : ValidStr x) (i : Fin (2 * w)) (c : Fin x.m) :
    x.compIdx hx i = c ↔ x.1 i = x.repAt c := by
  constructor
  · rintro rfl; exact (x.repAt_compIdx hx i).symm
  · intro h
    apply x.repAt_injective
    rw [x.repAt_compIdx hx i, h]

theorem mem_blk (c : Fin x.m) (i : Fin (2 * w)) : i ∈ x.blk c ↔ x.1 i = x.repAt c := by simp [blk]

theorem card_fiber (hx : ValidStr x) (c : Fin x.m) :
    Fintype.card {i // x.compIdx hx i = c} = (x.blk c).card := by
  rw [Fintype.card_subtype]
  congr 1
  ext i
  simp [compIdx_eq_iff, mem_blk]

/-- The caps of a component are the mates of its original trees, so a component has even size. -/
theorem card_blk_eq (hx : ValidStr x) (c : Fin x.m) :
    (x.blk c).card = 2 * ((x.blk c).filter fun i : Fin (2 * w) => (i : ℕ) < w).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := x.blk c) (fun i : Fin (2 * w) => (i : ℕ) < w)
  have hbij : ((x.blk c).filter fun i : Fin (2 * w) => ¬ (i : ℕ) < w).card =
      ((x.blk c).filter fun i : Fin (2 * w) => (i : ℕ) < w).card := by
    apply Finset.card_bij (fun i _ => capσ w (.inl (origIdx i)))
    · intro i hi
      simp only [mem_filter, mem_blk] at hi ⊢
      refine ⟨?_, by simp⟩
      obtain ⟨s, rfl⟩ := (capσ w).surjective i
      rcases s with j | j
      · exact absurd (by simp) hi.2
      · rw [origIdx_inr, hx.mate]; exact hi.1
    · intro i hi i' hi' e
      simp only [mem_filter] at hi hi'
      obtain ⟨s, rfl⟩ := (capσ w).surjective i
      obtain ⟨s', rfl⟩ := (capσ w).surjective i'
      rcases s with j | j
      · exact absurd (by simp) hi.2
      rcases s' with j' | j'
      · exact absurd (by simp) hi'.2
      simp only [origIdx_inr] at e
      rw [Sum.inl_injective ((capσ w).injective e)]
    · intro i hi
      simp only [mem_filter, mem_blk] at hi
      obtain ⟨s, rfl⟩ := (capσ w).surjective i
      rcases s with j | j
      · refine ⟨capσ w (.inr j), ?_, by simp⟩
        simp only [mem_filter, mem_blk]
        refine ⟨by rw [← hx.mate]; exact hi.1, by simp⟩
      · exact absurd hi.2 (by simp)
  omega

theorem two_R (hx : ValidStr x) (c : Fin x.m) : 2 * x.R c = (x.blk c).card := by
  unfold R
  rw [x.card_blk_eq hx c]
  omega

/-- The basic listing of component `c`. -/
def e0 (hx : ValidStr x) (c : Fin x.m) : Fin (2 * x.R c) ≃ {i // x.compIdx hx i = c} :=
  (Fintype.equivFinOfCardEq ((x.card_fiber hx c).trans (x.two_R hx c).symm)).symm

/-- The listing of component `c`, with the `+` tree first when the width is 2. -/
def eC (hx : ValidStr x) (sgn : Fin (2 * w) → ℤˣ) (c : Fin x.m) : Fin (2 * x.R c) ≃ {i // x.compIdx hx i = c} :=
  if hR : x.R c = 1 then
    (if sgn (x.e0 hx c ⟨0, by omega⟩).1 = 1 then x.e0 hx c
      else (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩).trans (x.e0 hx c))
  else x.e0 hx c

/-- **The component equivalence** `σ_x`. -/
def sigmaX (hx : ValidStr x) (sgn : Fin (2 * w) → ℤˣ) : (Σ c : Fin x.m, Fin (2 * x.R c)) ≃ Fin (2 * w) :=
  (Equiv.sigmaCongrRight (x.eC hx sgn)).trans (Equiv.sigmaFiberEquiv (x.compIdx hx))

theorem sigmaX_apply (hx : ValidStr x) (sgn : Fin (2 * w) → ℤˣ) (c : Fin x.m) (k : Fin (2 * x.R c)) :
    x.sigmaX hx sgn ⟨c, k⟩ = (x.eC hx sgn c k).1 := rfl

theorem compIdx_sigmaX (hx : ValidStr x) (sgn : Fin (2 * w) → ℤˣ) (c : Fin x.m) (k : Fin (2 * x.R c)) :
    x.compIdx hx (x.sigmaX hx sgn ⟨c, k⟩) = c := (x.eC hx sgn c k).2

theorem rep_sigmaX (hx : ValidStr x) (sgn : Fin (2 * w) → ℤˣ) (c : Fin x.m) (k : Fin (2 * x.R c)) :
    x.1 (x.sigmaX hx sgn ⟨c, k⟩) = x.repAt c :=
  (x.compIdx_eq_iff hx _ c).1 (x.compIdx_sigmaX hx sgn c k)

theorem sigmaX_symm_fst (hx : ValidStr x) (sgn : Fin (2 * w) → ℤˣ) (i : Fin (2 * w)) :
    ((x.sigmaX hx sgn).symm i).1 = x.compIdx hx i := by
  have := x.compIdx_sigmaX hx sgn ((x.sigmaX hx sgn).symm i).1 ((x.sigmaX hx sgn).symm i).2
  rw [show (⟨((x.sigmaX hx sgn).symm i).1, ((x.sigmaX hx sgn).symm i).2⟩ : Σ c : Fin x.m, Fin (2 * x.R c)) =
    (x.sigmaX hx sgn).symm i from rfl, Equiv.apply_symm_apply] at this
  exact this.symm

theorem blockOf_sigmaX (hx : ValidStr x) (sgn : Fin (2 * w) → ℤˣ) (c : Fin x.m) :
    blockOf (x.sigmaX hx sgn) c = x.blk c := by
  ext i
  rw [mem_blockOf, sigmaX_symm_fst, compIdx_eq_iff, mem_blk]

/-- In a width-2 component containing a `+` tree, position `0` is a `+` tree. -/
theorem sgn_sigmaX_zero (hx : ValidStr x) (sgn : Fin (2 * w) → ℤˣ) (c : Fin x.m) (hR : x.R c = 1)
    (hpm : ∀ k k' : Fin (2 * x.R c), k ≠ k' → sgn (x.sigmaX hx sgn ⟨c, k⟩) = -sgn (x.sigmaX hx sgn ⟨c, k'⟩)) :
    sgn (x.sigmaX hx sgn ⟨c, ⟨0, by omega⟩⟩) = 1 := by
  rw [sigmaX_apply]
  unfold eC
  rw [dite_eq_left_of_eq_true (eq_true hR)]
  by_cases h0 : sgn (x.e0 hx c ⟨0, by omega⟩).1 = 1
  · rw [ite_eq_left h0]; exact h0
  · rw [ite_eq_right h0]
    have h01 : (⟨0, by omega⟩ : Fin (2 * x.R c)) ≠ ⟨1, by omega⟩ := by simp
    have := hpm ⟨0, by omega⟩ ⟨1, by omega⟩ h01
    rw [sigmaX_apply, sigmaX_apply] at this
    unfold eC at this
    rw [dite_eq_left_of_eq_true (eq_true hR), ite_eq_right h0] at this
    simp only [Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at this ⊢
    rcases Int.units_eq_one_or (sgn (x.e0 hx c ⟨0, by omega⟩).1) with h | h
    · exact absurd h h0
    · rw [h] at this
      have := congrArg Neg.neg this
      simpa using this

end RawStr

end WaveTurbulence.Flower.CapsComp
