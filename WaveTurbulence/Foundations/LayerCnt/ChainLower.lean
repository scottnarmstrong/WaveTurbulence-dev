/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.CutMain
public import WaveTurbulence.Foundations.Molecule.VineRealizationGroups
import Mathlib.Tactic

/-! # A layer-monotone chain between the joints meets every certified cut group (TARGET layervine, L1531)

If `b = x_0, x_1, …, x_r = a` is a path of bonds of the vine `S` along which the layer `f` is non-decreasing
(the parent chain of the source), and `A` is the level-`1` set of a cut labelling of the expanded template that is
(contained in) a single group of the template, then `f x ≥ f b` for every atom `x ∈ S` mapped into `A`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence WaveTurbulence.Vine Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {X : VineType}
  {S : Finset V} {a b : V}

/-- One chain step: `x` and `y` are joined by a bond of `S`, and the layer does not decrease. -/
@[expose] def StepF (M : Molecule V D) (S : Finset V) (f : V → ℕ) (x y : V) : Prop :=
  x ∈ S ∧ y ∈ S ∧ s(x, y) ∈ M.groupBonds S ∧ f x ≤ f y

theorem mem_groupBonds_of_inGroup (S : Finset V) (d : D) (h : M.InGroup S d) :
    M.ends d ∈ M.groupBonds S := by
  unfold Molecule.groupBonds
  rw [Multiset.mem_map]
  by_cases ho : M.out d = true
  · exact ⟨d, by simpa [Finset.mem_val, ho] using h, rfl⟩
  · have ho' : M.out (M.mate d) = true := by
      rw [M.out_mate]; simpa using ho
    refine ⟨M.mate d, ?_, ?_⟩
    · simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨ho', ?_⟩
      unfold Molecule.InGroup at h ⊢
      rw [M.mate_mate]; exact ⟨h.2, h.1⟩
    · unfold Molecule.ends
      rw [M.mate_mate, Sym2.eq_swap]

theorem step_notCross (R : VineRealization M X S a b) {σ : ℕ → ℕ}
    (hσ : CutOn (X.expand R.k).bonds [] σ) {x y : V} (h : s(x, y) ∈ M.groupBonds S) :
    ¬ ((σ (R.f x) = 0 ∧ σ (R.f y) = 2) ∨ (σ (R.f x) = 2 ∧ σ (R.f y) = 0)) := by
  have hm : Sym2.map R.f s(x, y) ∈ (M.groupBonds S).map (Sym2.map R.f) := Multiset.mem_map_of_mem _ h
  rw [R.bonds_eq, Multiset.mem_coe, List.mem_map] at hm
  obtain ⟨p, hp, hpe⟩ := hm
  have hnc := hσ p hp (by simp)
  have hmp : Sym2.map R.f s(x, y) = s(R.f x, R.f y) := rfl
  rw [hmp] at hpe
  rcases Sym2.eq_iff.mp hpe with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · unfold Crosses at hnc; rw [h1, h2] at hnc; exact hnc
  · unfold Crosses at hnc; rw [h1, h2] at hnc
    intro h; apply hnc; tauto

theorem rtg_layer_mono {f : V → ℕ} {u v : V} (h : Relation.ReflTransGen (StepF M S f) u v) : f u ≤ f v := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact ih.trans hs.2.2.2

theorem exists_level1 (R : VineRealization M X S a b) {f : V → ℕ} {σ : ℕ → ℕ}
    (hσ : CutOn (X.expand R.k).bonds [] σ) (hσ2 : ∀ v, σ v ≤ 2)
    (hba : (σ (R.f b) = 0 ∧ σ (R.f a) = 2) ∨ (σ (R.f b) = 2 ∧ σ (R.f a) = 0))
    (hch : Relation.ReflTransGen (StepF M S f) b a) :
    ∃ y, Relation.ReflTransGen (StepF M S f) b y ∧ y ∈ S ∧ σ (R.f y) = 1 := by
  have hbv : σ (R.f b) = 0 ∨ σ (R.f b) = 2 := by omega
  have key : ∀ c, Relation.ReflTransGen (StepF M S f) b c →
      σ (R.f c) = 2 - σ (R.f b) → ∃ y, Relation.ReflTransGen (StepF M S f) b y ∧ y ∈ S ∧ σ (R.f y) = 1 := by
    intro c hc
    induction hc with
    | refl => intro h; omega
    | @tail c d hbc hcd ih =>
      intro hd
      have hnc := step_notCross R hσ hcd.2.2.1
      have hcb := hσ2 (R.f c)
      by_cases h1 : σ (R.f c) = 1
      · exact ⟨c, hbc, hcd.1, h1⟩
      · by_cases h2 : σ (R.f c) = 2 - σ (R.f b)
        · exact ih h2
        · exfalso
          have hc3 : σ (R.f c) = 0 ∨ σ (R.f c) = 1 ∨ σ (R.f c) = 2 := by omega
          rcases hbv with hbv | hbv <;> rw [hbv] at h2 hd <;> rcases hc3 with h | h | h <;>
            simp_all
  have := key a hch (by omega)
  exact this

/-- **The chain lemma**: every atom of the level-`1` set of a certified cut lies in a layer at least that of `b`. -/
theorem lower_of_cert (R : VineRealization M X S a b) {f : V → ℕ} {A : ℕ → Prop} {σ : ℕ → ℕ}
    (hσ : CertAt (X.expand R.k) A σ) {g : List ℕ} (hg : g ∈ (X.expand R.k).groups)
    (hAg : ∀ v, A v → v ∈ g) (hcoh : Coherent f (realizedGroups R))
    (hch : Relation.ReflTransGen (StepF M S f) b a) {x : V} (hx : x ∈ S) (hx1 : σ (R.f x) = 1) :
    f b ≤ f x := by
  obtain ⟨hle, h01, hcut, hA⟩ := hσ
  have hjt := R.joints_eq
  have hfa : R.f a = 0 ∧ R.f b = 1 ∨ R.f a = 1 ∧ R.f b = 0 := by
    have h1 : R.f a ∈ ({R.f a, R.f b} : Finset ℕ) := by simp
    have h2 : R.f b ∈ ({R.f a, R.f b} : Finset ℕ) := by simp
    rw [hjt] at h1 h2
    have hne : R.f a ≠ R.f b := by
      intro h; rw [h] at hjt; simp at hjt
      have := congrArg Finset.card hjt; simp at this
    simp at h1 h2; omega
  have hba : (σ (R.f b) = 0 ∧ σ (R.f a) = 2) ∨ (σ (R.f b) = 2 ∧ σ (R.f a) = 0) := by
    rcases hfa with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> omega
  obtain ⟨y, hy, hyS, hy1⟩ := exists_level1 R hcut hle hba hch
  have hfy := rtg_layer_mono hy
  have hmem : ∀ z, z ∈ S → σ (R.f z) = 1 → z ∈ S.toList.filter (fun v => R.f v ∈ g) := by
    intro z hz hz1
    have hzn : R.f z < (X.expand R.k).n := by
      have : R.f z ∈ S.image R.f := Finset.mem_image_of_mem _ hz
      rw [R.image_eq] at this; simpa using this
    simp only [List.mem_filter, Finset.mem_toList, decide_eq_true_eq]
    exact ⟨hz, hAg _ (hA _ hzn hz1)⟩
  have hgrp : S.toList.filter (fun v => R.f v ∈ g) ∈ realizedGroups R := by
    unfold realizedGroups
    exact List.mem_map.mpr ⟨g, hg, rfl⟩
  have := hcoh _ hgrp x (hmem x hx hx1) y (hmem y hyS hy1)
  rw [this]; exact hfy

end WaveTurbulence.LayerCnt
