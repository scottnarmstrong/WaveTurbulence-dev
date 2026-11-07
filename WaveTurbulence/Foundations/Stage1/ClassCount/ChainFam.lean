/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.ProdRestr2
public import WaveTurbulence.Foundations.Stage1.ClassCount.ChainSum
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode3
public import WaveTurbulence.Foundations.LayerCnt.BondExp
import Mathlib.Tactic

/-!
# CLASSCOUNT: the layering sum over a vine chain, by induction on `Chain`

`bw M B S f` is the product over the bonds inside `S` of `B ^ |f v - f v'|`.  For a family `𝓗` of layerings that is
distinct on a chain `U`, the sum `Σ_{f ∈ 𝓗, f b = z} bw U f` is bounded by the row vector `chainV L 1 z` of the transfer
matrices `Msum` of the ingredient vines (concatenation of blocks splits the bonds: `group_split`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.LayerCnt

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The weight of the bonds inside `S`. -/
noncomputable def bw (M : Molecule V D) (B : ℝ) (S : Finset V) (f : V → ℕ) : ℝ :=
  ∏ x ∈ bondsIn M S, B ^ dst (f (M.atom x)) (f (M.atom (M.mate x)))

theorem bw_nonneg (M : Molecule V D) {B : ℝ} (hB : 0 ≤ B) (S : Finset V) (f : V → ℕ) : 0 ≤ bw M B S f :=
  Finset.prod_nonneg fun _ _ => pow_nonneg hB _

theorem bw_congr (M : Molecule V D) (B : ℝ) {S : Finset V} {f f' : V → ℕ} (h : ∀ v ∈ S, f v = f' v) :
    bw M B S f = bw M B S f' := by
  unfold bw
  refine Finset.prod_congr rfl fun x hx => ?_
  have hx' := (Finset.mem_filter.mp hx).2
  rw [h _ hx'.1, h _ hx'.2]

theorem bw_restr (M : Molecule V D) (B : ℝ) (S : Finset V) (f : V → ℕ) : bw M B S (restr S f) = bw M B S f :=
  bw_congr M B fun v hv => restr_apply_of_mem f hv

theorem bw_union (M : Molecule V D) (hM : M.IsMolecule) (B : ℝ) {S T : Finset V} {a b c : V}
    (hS : M.IsBlock S a b) (hT : M.IsBlock T b c) (hU : M.IsBlock (S ∪ T) a c) (hi : S ∩ T = {b})
    (f : V → ℕ) : bw M B (S ∪ T) f = bw M B S f * bw M B T f := by
  classical
  unfold bw
  have hdisj : Disjoint (bondsIn M S) (bondsIn M T) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have h1' := (Finset.mem_filter.mp h1).2
    have h2' := (Finset.mem_filter.mp h2).2
    rcases group_split M hM hS hT hU hi x ⟨Finset.mem_union_left _ h1'.1, Finset.mem_union_left _ h1'.2⟩ with h | h
    · exact h.2 ⟨h2'.1, h2'.2⟩
    · exact h.2 ⟨h1'.1, h1'.2⟩
  have heq : bondsIn M (S ∪ T) = bondsIn M S ∪ bondsIn M T := by
    ext x
    simp only [bondsIn, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hb, hx⟩
      rcases group_split M hM hS hT hU hi x ⟨Finset.mem_union.mpr hx.1, Finset.mem_union.mpr hx.2⟩ with h | h
      · exact Or.inl ⟨hb, h.1.1, h.1.2⟩
      · exact Or.inr ⟨hb, h.1.1, h.1.2⟩
    · rintro (⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩)
      · exact ⟨hb, Or.inl h1, Or.inl h2⟩
      · exact ⟨hb, Or.inr h1, Or.inr h2⟩
  rw [heq, Finset.prod_union hdisj]

/-- Distinct on `A`. -/
def DistinctOn (A : Finset V) (𝓗 : Finset (V → ℕ)) : Prop :=
  ∀ f ∈ 𝓗, ∀ f' ∈ 𝓗, (∀ x ∈ A, f x = f' x) → f = f'

theorem distinctOn_iff_injOn (A : Finset V) (𝓗 : Finset (V → ℕ)) :
    DistinctOn A 𝓗 ↔ Set.InjOn (restr A) (𝓗 : Set (V → ℕ)) := by
  constructor
  · intro h f hf f' hf' he
    refine h f hf f' hf' fun x hx => ?_
    have := congrFun he x
    simpa [restr, hx] using this
  · intro h f hf f' hf' he
    refine h hf hf' ?_
    funext x
    by_cases hx : x ∈ A
    · simpa [restr, hx] using he x hx
    · simp [restr, hx]

theorem DistinctOn.subset {A : Finset V} {𝓗 𝓗' : Finset (V → ℕ)} (h : DistinctOn A 𝓗) (hs : 𝓗' ⊆ 𝓗) :
    DistinctOn A 𝓗' := fun f hf f' hf' he => h f (hs hf) f' (hs hf') he

theorem DistinctOn.of_union_left {A B : Finset V} {𝓗 : Finset (V → ℕ)} (h : DistinctOn (A ∪ B) 𝓗) :
    ∀ f ∈ 𝓗, ∀ f' ∈ 𝓗, (∀ x ∈ A, f x = f' x) → (∀ x ∈ B, f x = f' x) → f = f' :=
  fun f hf f' hf' h1 h2 => h f hf f' hf' fun x hx => (Finset.mem_union.mp hx).elim (h1 x) (h2 x)

/-- A transversal of the restrictions to `A`. -/
theorem exists_transversal (A : Finset V) (𝓗 : Finset (V → ℕ)) :
    ∃ 𝓣 ⊆ 𝓗, DistinctOn A 𝓣 ∧ 𝓣.image (restr A) = 𝓗.image (restr A) := by
  classical
  let rep : (V → ℕ) → (V → ℕ) := fun y => if h : ∃ f ∈ 𝓗, restr A f = y then h.choose else y
  have hrep : ∀ y ∈ 𝓗.image (restr A), rep y ∈ 𝓗 ∧ restr A (rep y) = y := by
    intro y hy
    have h : ∃ f ∈ 𝓗, restr A f = y := by
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨f, hf, rfl⟩
    simp only [rep, dif_pos h]
    exact h.choose_spec
  refine ⟨(𝓗.image (restr A)).image rep, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hf
    exact (hrep y hy).1
  · rw [distinctOn_iff_injOn]
    intro f hf f' hf' he
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hf)
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hf')
    have : y = y' := by rw [← (hrep y hy).2, ← (hrep y' hy').2]; exact he
    rw [this]
  · ext y
    constructor
    · intro hy
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hf
      exact Finset.mem_image_of_mem _ (hrep y' hy').1
    · intro hy
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨rep (restr A f),
        Finset.mem_image.mpr ⟨restr A f, Finset.mem_image_of_mem _ hf, rfl⟩,
        (hrep _ (Finset.mem_image_of_mem _ hf)).2⟩

theorem sum_bw_eq_image (M : Molecule V D) (B : ℝ) (U : Finset V) {𝓗 : Finset (V → ℕ)} (h : DistinctOn U 𝓗) :
    ∑ f ∈ 𝓗, bw M B U f = ∑ r ∈ 𝓗.image (restr U), bw M B U r := by
  rw [Finset.sum_image ((distinctOn_iff_injOn U 𝓗).mp h)]
  exact Finset.sum_congr rfl fun f _ => (bw_restr M B U f).symm

/-- The transfer matrix of the ingredient `T` with joints `x, y`: the sum over the restrictions to `T` of the
members with joint layers `(s, t)`. -/
noncomputable def Msum (M : Molecule V D) (B : ℝ) (T : Finset V) (x y : V) (𝓗 : Finset (V → ℕ)) (s t : ℕ) : ℝ :=
  ∑ r ∈ (𝓗.filter (fun f => f x = s ∧ f y = t)).image (restr T), bw M B T r

/-- The link of an ingredient with classification data `e = (good, c, T)`. -/
noncomputable def linkOf (M : Molecule V D) (B : ℝ) (T : Finset V) (x y : V) (𝓗 : Finset (V → ℕ))
    (e : Bool × ℝ × ℝ) : Link :=
  ⟨e.1, e.2.1, e.2.2, Msum M B T x y 𝓗⟩

def Link.proj (l : Link) : Bool × ℝ × ℝ := (l.good, l.c, l.T)

theorem chainV_append (𝔇 : ℕ) (L : List Link) (l : Link) (v : ℕ → ℝ) :
    chainV 𝔇 (L ++ [l]) v = prop 𝔇 (chainV 𝔇 L v) l.M := by
  induction L generalizing v with
  | nil => rfl
  | cons l' L ih => exact ih _

end WaveTurbulence.ClassCount
