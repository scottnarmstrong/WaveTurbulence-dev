/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGroupSet
public import WaveTurbulenceVineParam.VineParamSkipEquiv
public import WaveTurbulenceVineParam.VineParamExpandDecomp
import Mathlib.Tactic

/-! # Group sets of the expanded templates: one rung more or less

Label-level bookkeeping for the group-preserving induction. The groups of `insertRungs T s k`
are the groups of `T` together with the `k` fresh doubled pairs `{T.n+i, T.n+k+i}`.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset

theorem listGroupSet_append (l₁ l₂ : List (List ℕ)) :
    listGroupSet (l₁ ++ l₂) = listGroupSet l₁ ∪ listGroupSet l₂ := by
  simp [listGroupSet, List.map_append, List.toFinset_append]

theorem mem_listGroupSet {gs : List (List ℕ)} {s : Finset ℕ} :
    s ∈ listGroupSet gs ↔ ∃ g ∈ gs, g.toFinset = s := by
  simp [listGroupSet]

/-- The groups of an insertion of `k` rungs. -/
theorem insertRungs_groupSet (T : VineTemplate) (sl : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) :
    listGroupSet (insertRungs T sl k).groups =
      listGroupSet T.groups ∪ (range k).image (fun i => ({T.n+i, T.n+k+i} : Finset ℕ)) := by
  by_cases hk : k = 0
  · subst hk; simp [insertRungs]
  · simp only [insertRungs, hk, ite_false]
    rw [listGroupSet_append]
    congr 1
    ext s
    rw [mem_listGroupSet]
    simp only [mem_image, mem_range]
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
      obtain ⟨i, hi, rfl⟩ : ∃ i, i < k ∧ p = (T.n + i, T.n + k + i) := by
        have hz := hp
        rw [List.zip_map' ] at hz
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
        exact ⟨i, List.mem_range.mp hi, rfl⟩
      exact ⟨i, hi, by simp⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨[T.n + i, T.n + k + i], List.mem_map.mpr ⟨(T.n + i, T.n + k + i), ?_, rfl⟩, by simp⟩
      rw [List.zip_map']
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩


theorem unskip2_below (f0 f1 v : ℕ) (h : v < f0) (h01 : f0 < f1) : unskip2 f0 f1 v = v := by
  simp only [unskip2]; split_ifs <;> omega

/-- One rung more, contracted at the last rung (cap at the `y` end). -/
theorem groupSet_step_Y (G0 : Finset (Finset ℕ)) (N k : ℕ) (hG0 : ∀ s ∈ G0, ∀ v ∈ s, v < N) :
    G0 ∪ (range (k+1)).image (fun i => ({N+i, N+(k+1)+i} : Finset ℕ)) =
      insert ({N+k, N+(2*k+1)} : Finset ℕ)
        ((G0 ∪ (range k).image (fun i => ({N+i, N+k+i} : Finset ℕ))).image
          (Finset.image (unskip2 (N+k) (N+(2*k+1))))) := by
  have hG : ∀ t ∈ G0, t.image (unskip2 (N+k) (N+(2*k+1))) = t := by
    intro t ht
    conv_rhs => rw [← Finset.image_id (s := t)]
    apply Finset.image_congr
    intro v hv
    exact unskip2_below _ _ _ (by have := hG0 t ht v hv; omega) (by omega)
  have hμ1 : ∀ i, i < k → unskip2 (N+k) (N+(2*k+1)) (N+i) = N+i :=
    fun i hi => unskip2_below _ _ _ (by omega) (by omega)
  have hμ2 : ∀ i, i < k → unskip2 (N+k) (N+(2*k+1)) (N+k+i) = N+(k+1)+i := by
    intro i hi; simp only [unskip2]; split_ifs <;> omega
  ext s
  simp only [mem_union, mem_insert, mem_image, mem_range]
  constructor
  · rintro (hs | ⟨i, hi, rfl⟩)
    · right; exact ⟨s, Or.inl hs, hG s hs⟩
    · by_cases hik : i = k
      · subst hik; left; ext v; simp only [mem_insert, mem_singleton]; constructor <;> intro h <;> omega
      · right
        refine ⟨{N+i, N+k+i}, Or.inr ⟨i, by omega, rfl⟩, ?_⟩
        simp only [Finset.image_insert, Finset.image_singleton, hμ1 i (by omega), hμ2 i (by omega)]
  · rintro (rfl | ⟨t, (ht | ⟨i, hi, rfl⟩), rfl⟩)
    · right; exact ⟨k, by omega, by ext v; simp only [mem_insert, mem_singleton]; constructor <;> intro h <;> omega⟩
    · left; rw [hG t ht]; exact ht
    · right
      refine ⟨i, by omega, ?_⟩
      simp only [Finset.image_insert, Finset.image_singleton, hμ1 i hi, hμ2 i hi]

/-- One rung more, contracted at the first rung (cap at the `x` end). -/
theorem groupSet_step_X (G0 : Finset (Finset ℕ)) (N k : ℕ) (hG0 : ∀ s ∈ G0, ∀ v ∈ s, v < N) :
    G0 ∪ (range (k+1)).image (fun i => ({N+i, N+(k+1)+i} : Finset ℕ)) =
      insert ({N, N+(k+1)} : Finset ℕ)
        ((G0 ∪ (range k).image (fun i => ({N+i, N+k+i} : Finset ℕ))).image
          (Finset.image (unskip2 N (N+(k+1))))) := by
  have hG : ∀ t ∈ G0, t.image (unskip2 N (N+(k+1))) = t := by
    intro t ht
    conv_rhs => rw [← Finset.image_id (s := t)]
    apply Finset.image_congr
    intro v hv
    simp only [unskip2, id]
    have := hG0 t ht v hv
    split_ifs <;> omega
  have hμ1 : ∀ i, i < k → unskip2 N (N+(k+1)) (N+i) = N+(i+1) := by
    intro i hi; simp only [unskip2]; split_ifs <;> omega
  have hμ2 : ∀ i, i < k → unskip2 N (N+(k+1)) (N+k+i) = N+(k+1)+(i+1) := by
    intro i hi; simp only [unskip2]; split_ifs <;> omega
  ext s
  simp only [mem_union, mem_insert, mem_image, mem_range]
  constructor
  · rintro (hs | ⟨i, hi, rfl⟩)
    · right; exact ⟨s, Or.inl hs, hG s hs⟩
    · by_cases hi0 : i = 0
      · subst hi0; left; ext v; simp only [mem_insert, mem_singleton]; constructor <;> intro h <;> omega
      · right
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i-1, by omega⟩
        refine ⟨{N+j, N+k+j}, Or.inr ⟨j, by omega, rfl⟩, ?_⟩
        simp only [Finset.image_insert, Finset.image_singleton, hμ1 j (by omega), hμ2 j (by omega)]
  · rintro (rfl | ⟨t, (ht | ⟨i, hi, rfl⟩), rfl⟩)
    · right; exact ⟨0, by omega, by ext v; simp only [mem_insert, mem_singleton]; constructor <;> intro h <;> omega⟩
    · left; rw [hG t ht]; exact ht
    · right
      refine ⟨i+1, by omega, ?_⟩
      simp only [Finset.image_insert, Finset.image_singleton, hμ1 i hi, hμ2 i hi]


/-- A permutation fixing every fresh label preserves the group set of an insertion. -/
theorem groupSet_inv (G0 : Finset (Finset ℕ)) (N k : ℕ) (ν : ℕ ≃ ℕ)
    (hG0 : G0.image (Finset.image ν) = G0) (hfix : ∀ t, N ≤ t → ν t = t) :
    (G0 ∪ (range k).image (fun i => ({N+i, N+k+i} : Finset ℕ))).image (Finset.image ν) =
      G0 ∪ (range k).image (fun i => ({N+i, N+k+i} : Finset ℕ)) := by
  rw [Finset.image_union, hG0, Finset.image_image]
  congr 1
  apply Finset.image_congr
  intro i _
  simp only [Function.comp_apply, Finset.image_insert, Finset.image_singleton,
    hfix (N+i) (by omega), hfix (N+k+i) (by omega)]

theorem template_groups_lt (X : VineType) : ∀ g ∈ X.template.groups, ∀ v ∈ g, v < X.template.n := by
  intro g hg v hv
  have hp := template_groups_partition X
  have : v ∈ (List.range X.template.n).drop 2 :=
    hp.subset (List.mem_flatten.mpr ⟨g, hg, hv⟩)
  exact List.mem_range.mp (List.mem_of_mem_drop this)

/-- The prefix templates only have the base groups and groups of fresh labels, all in range. -/
theorem prefTemplate_groups (X : VineType) (ks1 : List ℕ) :
    ((∀ g ∈ (prefTemplate X ks1).groups, g ∈ X.template.groups ∨ ∀ v ∈ g, X.template.n ≤ v) ∧
      (∀ g ∈ (prefTemplate X ks1).groups, ∀ v ∈ g, v < (prefTemplate X ks1).n)) ∧
      X.template.n ≤ (prefTemplate X ks1).n := by
  have hbase := template_groups_lt X
  have key : ∀ (l : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (T : VineTemplate),
      ((∀ g ∈ T.groups, g ∈ X.template.groups ∨ ∀ v ∈ g, X.template.n ≤ v) ∧
        (∀ g ∈ T.groups, ∀ v ∈ g, v < T.n)) ∧ X.template.n ≤ T.n →
      ((∀ g ∈ (l.foldl (fun U sk => insertRungs U sk.1 sk.2) T).groups,
          g ∈ X.template.groups ∨ ∀ v ∈ g, X.template.n ≤ v) ∧
        (∀ g ∈ (l.foldl (fun U sk => insertRungs U sk.1 sk.2) T).groups, ∀ v ∈ g,
          v < (l.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n)) ∧
        X.template.n ≤ (l.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n := by
    intro l
    induction l with
    | nil => intro T h; exact h
    | cons sk l ih =>
      intro T h
      rw [List.foldl_cons]
      apply ih
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      obtain ⟨sl, k⟩ := sk
      by_cases hk : k = 0
      · subst hk; rw [insertRungs_zero]; exact ⟨⟨h1, h2⟩, h3⟩
      · have hat := insertRungs_atoms T sl k
        have hg : (insertRungs T sl k).groups =
            T.groups ++ (List.zip ((List.range k).map (T.n + ·))
              ((List.range k).map (T.n + k + ·))).map (fun p => [p.1, p.2]) := by
          simp [insertRungs, hk]
        have hnn : (insertRungs T sl k).n = T.n + 2*k := by simp [insertRungs, hk]
        rw [hg, hnn]
        refine ⟨⟨?_, ?_⟩, by omega⟩
        · intro g hgm
          rcases List.mem_append.mp hgm with hgm | hgm
          · exact h1 g hgm
          · right
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hgm
            rw [List.zip_map'] at hp
            obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
            intro v hv
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            omega
        · intro g hgm v hv
          rcases List.mem_append.mp hgm with hgm | hgm
          · have := h2 g hgm v hv; omega
          · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hgm
            rw [List.zip_map'] at hp
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
            have hi' := List.mem_range.mp hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            omega
  exact key _ X.template ⟨⟨fun g hg => Or.inl hg, hbase⟩, le_rfl⟩


/-- Packaging of the group bookkeeping of a slot contraction, with the cap reflection `ν`
allowed to act on the old labels. -/
theorem group_step_eq (S : Finset (Finset ℕ)) (N k : ℕ) (ν : ℕ ≃ ℕ) (μ : ℕ → ℕ) (f0 f1 : ℕ)
    (hstep : S ∪ (range (k+1)).image (fun i => ({N+i, N+(k+1)+i} : Finset ℕ)) =
      insert ({f0, f1} : Finset ℕ)
        ((S ∪ (range k).image (fun i => ({N+i, N+k+i} : Finset ℕ))).image (Finset.image μ)))
    (hinv : S.image (Finset.image ν) = S) (hfix : ∀ t, N ≤ t → ν t = t) :
    ∀ ψ : ℕ → ℕ, (ψ = id ∨ ψ = ⇑ν) →
      insert ({f0, f1} : Finset ℕ)
        ((S ∪ (range k).image (fun i => ({N+i, N+k+i} : Finset ℕ))).image
          (Finset.image (fun t => μ (ψ t)))) =
        S ∪ (range (k+1)).image (fun i => ({N+i, N+(k+1)+i} : Finset ℕ)) := by
  intro ψ hψ
  rw [hstep]
  rcases hψ with rfl | rfl
  · rfl
  · congr 1
    have h1 : (S ∪ (range k).image (fun i => ({N+i, N+k+i} : Finset ℕ))).image
          (Finset.image (fun t => μ (ν t))) =
        ((S ∪ (range k).image (fun i => ({N+i, N+k+i} : Finset ℕ))).image
          (Finset.image ν)).image (Finset.image μ) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro t _
      rw [Function.comp_apply, Finset.image_image]
      rfl
    rw [h1, groupSet_inv S N k ν hinv hfix]


/-- The cap reflection of a slot preserves each group of the prefix templates. -/
theorem reflection_image_group (X : VineType) (i : Fin X.template.slots.length) (g : List ℕ)
    (hg : g ∈ X.template.groups ∨ ∀ v ∈ g, X.template.n ≤ v) :
    g.toFinset.image (slotReflection X i) = g.toFinset := by
  rcases hg with hg | hg
  · apply Finset.eq_of_subset_of_card_le
    · intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      have hv' := List.mem_toFinset.mp hv
      exact List.mem_toFinset.mpr
        ((slotReflection_groups X i g hg ⟨v, template_groups_lt X g hg v hv'⟩).mpr hv')
    · rw [Finset.card_image_of_injective _ (slotReflection X i).injective]
  · have : ∀ v ∈ g.toFinset, slotReflection X i v = v := by
      intro v hv
      apply slotReflection_outside_all
      intro hm
      have := slotCap_old X i v hm
      have := hg v (List.mem_toFinset.mp hv)
      omega
    conv_rhs => rw [← Finset.image_id (s := g.toFinset)]
    exact Finset.image_congr (fun v hv => by simpa using this v hv)

end WaveTurbulence.Vine.Param
