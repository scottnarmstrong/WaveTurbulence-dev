/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.ChainLower
import Mathlib.Tactic

/-! # Good groups: base cut groups and rungs of base cut slots (TARGET layervine, L1531)

Every group of an expanded template is a base group or one rung (`rungGroup`) of one slot; it is *good* if it is a
cut group (`CutG`) or a rung of a cut slot (`CutS`).  Atoms of good groups lie in layers at least `f b`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence WaveTurbulence.Vine Finset

/-- The `i`-th rung group (`1 ≤ i ≤ k`) of the slot `c` of the expansion with counts `ks`. -/
@[expose] def rungGroup (X : VineType) (ks : List ℕ) (c i : ℕ) : List ℕ :=
  [X.template.n + 2 * (ks.take c).sum + (i - 1), X.template.n + 2 * (ks.take c).sum + ks.getD c 0 + (i - 1)]

theorem fold_groups_cases (xs : List (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)) :
    ∀ (T : VineTemplate) (g : List ℕ),
      g ∈ (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).groups →
        g ∈ T.groups ∨ ∃ j, ∃ hj : j < xs.length, ∃ i, 1 ≤ i ∧ i ≤ (xs[j]'hj).2 ∧
          g = [T.n + 2 * ((xs.take j).map Prod.snd).sum + (i - 1),
            T.n + 2 * ((xs.take j).map Prod.snd).sum + (xs[j]'hj).2 + (i - 1)] := by
  induction xs with
  | nil => intro T g h; exact Or.inl h
  | cons sk xs ih =>
    intro T g h
    simp only [List.foldl_cons] at h
    rcases ih _ g h with h1 | ⟨j, hj, i, hi1, hi2, hg⟩
    · by_cases hk : sk.2 = 0
      · left; simpa [insertRungs, hk] using h1
      · simp only [insertRungs, hk, ite_false, List.mem_append] at h1
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · right
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h1
          rw [List.zip_map'] at hp
          obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hp
          have := List.mem_range.mp hi'
          refine ⟨0, by simp, i' + 1, by omega, by simp; omega, ?_⟩
          simp
    · right
      refine ⟨j + 1, by simp; omega, i, hi1, by simpa using hi2, ?_⟩
      rw [hg, insertRungs_atoms]
      simp [List.take_succ_cons, add_assoc]
      omega

theorem expand_groups_cases (X : VineType) (ks : List ℕ) (hk : ks.length = X.template.slots.length)
    {g : List ℕ} (hg : g ∈ (X.expand ks).groups) :
    g ∈ X.template.groups ∨ ∃ c, ∃ hc : c < X.template.slots.length, ∃ i, 1 ≤ i ∧ i ≤ ks.getD c 0 ∧
      g = rungGroup X ks c i := by
  rcases fold_groups_cases (X.template.slots.zip ks) X.template g hg with h | ⟨j, hj, i, hi1, hi2, rfl⟩
  · exact Or.inl h
  · right
    have hjs : j < X.template.slots.length := by
      simp [List.length_zip, hk] at hj; omega
    have hjk : j < ks.length := by omega
    refine ⟨j, hjs, i, hi1, ?_, ?_⟩
    · simpa [List.getElem_zip, List.getD_eq_getElem?_getD, hjk] using hi2
    · have : ((X.template.slots.zip ks).take j).map Prod.snd = ks.take j := by
        rw [List.map_take, List.map_snd_zip (by omega)]
      simp only [rungGroup, this]
      simp [List.getElem_zip, List.getD_eq_getElem?_getD, hjk]

/-- A group is *good* if it is a base cut group or a rung of a base cut slot. -/
@[expose] def GoodGroup (X : VineType) (ks : List ℕ) (g : List ℕ) : Prop :=
  (g ∈ X.template.groups ∧ CutG X.template g) ∨
    ∃ c, ∃ hc : c < X.template.slots.length, CutS X.template c (X.template.slots[c]'hc) ∧
      ∃ i, 1 ≤ i ∧ i ≤ ks.getD c 0 ∧ g = rungGroup X ks c i

end WaveTurbulence.LayerCnt

namespace WaveTurbulence.LayerCnt
open WaveTurbulence WaveTurbulence.Vine Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {X : VineType}
  {S : Finset V} {a b : V}

/-- **Atoms of good groups lie above `b`.** -/
theorem lower_of_good (R : VineRealization M X S a b) {f : V → ℕ} (hcoh : Coherent f (realizedGroups R))
    (hch : Relation.ReflTransGen (StepF M S f) b a) {g : List ℕ} (hg : g ∈ (X.expand R.k).groups)
    (hgood : GoodGroup X R.k g) {x : V} (hx : x ∈ S) (hxg : R.f x ∈ g) : f b ≤ f x := by
  rcases hgood with ⟨hgb, hcut⟩ | ⟨c, hc, hS, i, hi1, hi2, rfl⟩
  · obtain ⟨σ, hσ, h1⟩ := expand_certG X R.k R.length_eq g hcut
    exact lower_of_cert R hσ hg (fun v hv => hv) hcoh hch hx (h1 _ hxg)
  · have hck : c < R.k.length := by rw [R.length_eq]; exact hc
    have hgd : R.k.getD c 0 = R.k[c] := by simp [List.getD_eq_getElem?_getD, hck]
    rw [hgd] at hi2
    obtain ⟨σ, hσ, h1, h2⟩ := expand_certS X R.k R.length_eq c hc hS i hi1 hi2
    refine lower_of_cert R hσ hg (fun v hv => ?_) hcoh hch hx ?_
    · unfold rungGroup; rw [hgd]; simpa using hv
    · unfold rungGroup at hxg; rw [hgd] at hxg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hxg
      rcases hxg with h | h <;> rw [h] <;> assumption

end WaveTurbulence.LayerCnt
