/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.Peak

/-! # Counting rung configurations of bounded rail variation (TARGET layerlad, L1510)

A family of layerings that are pairwise distinct on the interior rungs and whose two rail sequences have
total variation at most `T` has at most `((𝔇+1)·3^{n+T})²` members.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset

/-- The list `[a s, a (s+1), …, a (s+k-1)]`. -/
@[expose] def seqList (a : ℕ → ℕ) (s : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => a s :: seqList a (s + 1) k

theorem seqList_length (a : ℕ → ℕ) (s k : ℕ) : (seqList a s k).length = k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => simp [seqList, ih]

theorem mem_seqList (a : ℕ → ℕ) {x : ℕ} : ∀ (k s : ℕ), x ∈ seqList a s k ↔ ∃ i, i < k ∧ x = a (s + i) := by
  intro k
  induction k with
  | zero => intro s; simp [seqList]
  | succ k ih =>
    intro s
    simp only [seqList, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by omega, rfl⟩
      · exact ⟨i + 1, by omega, by rw [show s + (i + 1) = s + 1 + i by ring]⟩
    · rintro ⟨i, hi, rfl⟩
      rcases i with _ | i
      · left; rfl
      · right; exact ⟨i, by omega, by rw [show s + (i + 1) = s + 1 + i by ring]⟩

theorem seqList_inj (a b : ℕ → ℕ) : ∀ (k s : ℕ), seqList a s k = seqList b s k → ∀ i, i < k → a (s + i) = b (s + i) := by
  intro k
  induction k with
  | zero => intro s _ i hi; omega
  | succ k ih =>
    intro s h i hi
    simp only [seqList, List.cons.injEq] at h
    rcases i with _ | i
    · simpa using h.1
    · have := ih (s + 1) h.2 i (by omega)
      rwa [show s + (i + 1) = s + 1 + i by ring]

theorem tvL_seqList (a : ℕ → ℕ) : ∀ (k s : ℕ), tvL (seqList a s (k + 1)) = tvF a s (s + k) := by
  intro k
  induction k with
  | zero => intro s; simp [seqList, tvL, tvF]
  | succ k ih =>
    intro s
    have e : seqList a s (k + 1 + 1) = a s :: seqList a (s + 1) (k + 1) := rfl
    rw [e]
    obtain ⟨l, hl⟩ : ∃ l, seqList a (s + 1) (k + 1) = a (s + 1) :: l := ⟨_, rfl⟩
    rw [hl]
    have := ih (s + 1)
    rw [hl] at this
    simp only [tvL]
    rw [this]
    unfold tvF
    rw [show s + (k + 1) = (s + 1) + k by ring, Finset.sum_eq_sum_Ico_succ_bot (by omega : s < s + 1 + k)]

theorem seqList_mem_bseqs (a : ℕ → ℕ) (s k 𝔇 : ℕ) (h : ∀ i, i < k → a (s + i) ≤ 𝔇) :
    seqList a s k ∈ bseqs 𝔇 k := by
  rw [mem_bseqs]
  refine ⟨seqList_length a s k, ?_⟩
  intro x hx
  obtain ⟨i, hi, rfl⟩ := (mem_seqList a k s).mp hx
  exact h i hi

theorem card_S_le (𝔇 n T : ℕ) :
    ((bseqs 𝔇 n).filter (fun l => tvL l ≤ T)).card ≤ (𝔇 + 1) * 3 ^ (n + T) := by
  rcases n with _ | k
  · calc _ ≤ (bseqs 𝔇 0).card := card_filter_le _ _
      _ = 1 := by simp [bseqs]
      _ ≤ (𝔇 + 1) * 3 ^ (0 + T) := Nat.mul_pos (by omega) (by positivity)
  · calc _ ≤ (𝔇 + 1) * 3 ^ (k + T) := card_tv_all 𝔇 k T
      _ ≤ (𝔇 + 1) * 3 ^ (k + 1 + T) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- Family counting. -/
theorem card_configs_le {ι : Type*} [DecidableEq ι] (𝓕 : Finset ι) (A B : ι → ℕ → ℕ) (n 𝔇 T : ℕ)
    (hbd : ∀ f ∈ 𝓕, ∀ i, 1 ≤ i → i ≤ n → A f i ≤ 𝔇 ∧ B f i ≤ 𝔇)
    (htv : ∀ f ∈ 𝓕, tvF (A f) 1 n ≤ T ∧ tvF (B f) 1 n ≤ T)
    (hinj : ∀ f ∈ 𝓕, ∀ g ∈ 𝓕, (∀ i, 1 ≤ i → i ≤ n → A f i = A g i ∧ B f i = B g i) → f = g) :
    𝓕.card ≤ ((𝔇 + 1) * 3 ^ (n + T)) ^ 2 := by
  classical
  set S := (bseqs 𝔇 n).filter (fun l => tvL l ≤ T) with hS
  have hmap : ∀ f ∈ 𝓕, (seqList (A f) 1 n, seqList (B f) 1 n) ∈ S ×ˢ S := by
    intro f hf
    have tvle : ∀ a : ℕ → ℕ, tvF a 1 n ≤ T → tvL (seqList a 1 n) ≤ T := by
      intro a ha
      rcases n with _ | k
      · simp [seqList, tvL]
      · rw [tvL_seqList]; rw [show 1 + k = k + 1 by ring]; exact ha
    simp only [mem_product, hS, mem_filter]
    refine ⟨⟨seqList_mem_bseqs _ _ _ _ (fun i hi => (hbd f hf (1 + i) (by omega) (by omega)).1),
      tvle _ (htv f hf).1⟩, ⟨seqList_mem_bseqs _ _ _ _ (fun i hi => (hbd f hf (1 + i) (by omega) (by omega)).2),
      tvle _ (htv f hf).2⟩⟩
  have hinjOn : Set.InjOn (fun f => (seqList (A f) 1 n, seqList (B f) 1 n)) 𝓕 := by
    intro f hf g hg h
    simp only [Prod.mk.injEq] at h
    apply hinj f hf g hg
    intro i hi1 hi2
    have h1 := seqList_inj _ _ n 1 h.1 (i - 1) (by omega)
    have h2 := seqList_inj _ _ n 1 h.2 (i - 1) (by omega)
    rw [show 1 + (i - 1) = i by omega] at h1 h2
    exact ⟨h1, h2⟩
  calc 𝓕.card ≤ (S ×ˢ S).card := Finset.card_le_card_of_injOn _ hmap hinjOn
    _ = S.card ^ 2 := by rw [card_product]; ring
    _ ≤ _ := Nat.pow_le_pow_left (card_S_le 𝔇 n T) 2

/-- Family counting with an extra finite datum (the end atoms). -/
theorem card_configs_le' {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (𝓕 : Finset ι) (A B : ι → ℕ → ℕ)
    (X : Finset κ) (E : ι → κ) (hE : ∀ f ∈ 𝓕, E f ∈ X) (n 𝔇 T : ℕ)
    (hbd : ∀ f ∈ 𝓕, ∀ i, 1 ≤ i → i ≤ n → A f i ≤ 𝔇 ∧ B f i ≤ 𝔇)
    (htv : ∀ f ∈ 𝓕, tvF (A f) 1 n ≤ T ∧ tvF (B f) 1 n ≤ T)
    (hinj : ∀ f ∈ 𝓕, ∀ g ∈ 𝓕, (∀ i, 1 ≤ i → i ≤ n → A f i = A g i ∧ B f i = B g i) → E f = E g → f = g) :
    𝓕.card ≤ X.card * ((𝔇 + 1) * 3 ^ (n + T)) ^ 2 := by
  classical
  set S := (bseqs 𝔇 n).filter (fun l => tvL l ≤ T) with hS
  have hmap : ∀ f ∈ 𝓕, ((seqList (A f) 1 n, seqList (B f) 1 n), E f) ∈ (S ×ˢ S) ×ˢ X := by
    intro f hf
    have tvle : ∀ a : ℕ → ℕ, tvF a 1 n ≤ T → tvL (seqList a 1 n) ≤ T := by
      intro a ha
      rcases n with _ | k
      · simp [seqList, tvL]
      · rw [tvL_seqList]; rw [show 1 + k = k + 1 by ring]; exact ha
    simp only [mem_product, hS, mem_filter]
    refine ⟨⟨⟨seqList_mem_bseqs _ _ _ _ (fun i hi => (hbd f hf (1 + i) (by omega) (by omega)).1),
      tvle _ (htv f hf).1⟩, ⟨seqList_mem_bseqs _ _ _ _ (fun i hi => (hbd f hf (1 + i) (by omega) (by omega)).2),
      tvle _ (htv f hf).2⟩⟩, hE f hf⟩
  have hinjOn : Set.InjOn (fun f => ((seqList (A f) 1 n, seqList (B f) 1 n), E f)) 𝓕 := by
    intro f hf g hg h
    simp only [Prod.mk.injEq] at h
    apply hinj f hf g hg _ h.2
    intro i hi1 hi2
    have h1 := seqList_inj _ _ n 1 h.1.1 (i - 1) (by omega)
    have h2 := seqList_inj _ _ n 1 h.1.2 (i - 1) (by omega)
    rw [show 1 + (i - 1) = i by omega] at h1 h2
    exact ⟨h1, h2⟩
  calc 𝓕.card ≤ ((S ×ˢ S) ×ˢ X).card := Finset.card_le_card_of_injOn _ hmap hinjOn
    _ = S.card ^ 2 * X.card := by rw [card_product, card_product]; ring
    _ ≤ ((𝔇 + 1) * 3 ^ (n + T)) ^ 2 * X.card := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (card_S_le 𝔇 n T) 2)
    _ = _ := by ring

/-- Family counting for several rung sequences with an extra finite datum. -/
theorem multi_card_le {ι κ φ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq φ] [DecidableEq κ]
    (𝓕 : Finset φ) (A B : ι → φ → ℕ → ℕ) (k : ι → ℕ) (Xr : Finset κ) (E : φ → κ)
    (hE : ∀ f ∈ 𝓕, E f ∈ Xr) (𝔇 T : ℕ)
    (hbd : ∀ f ∈ 𝓕, ∀ c i, 1 ≤ i → i ≤ k c → A c f i ≤ 𝔇 ∧ B c f i ≤ 𝔇)
    (htv : ∀ f ∈ 𝓕, ∀ c, tvF (A c f) 1 (k c) ≤ T ∧ tvF (B c f) 1 (k c) ≤ T)
    (hinj : ∀ f ∈ 𝓕, ∀ g ∈ 𝓕, (∀ c i, 1 ≤ i → i ≤ k c → A c f i = A c g i ∧ B c f i = B c g i) →
      E f = E g → f = g) :
    𝓕.card ≤ Xr.card * ∏ c, ((𝔇 + 1) * 3 ^ (k c + T)) ^ 2 := by
  classical
  set Sc : ι → Finset (List ℕ) := fun c => (bseqs 𝔇 (k c)).filter (fun l => tvL l ≤ T) with hSc
  have tvle : ∀ (a : ℕ → ℕ) (n : ℕ), tvF a 1 n ≤ T → tvL (seqList a 1 n) ≤ T := by
    intro a n ha
    rcases n with _ | k'
    · simp [seqList, tvL]
    · rw [tvL_seqList]; rw [show 1 + k' = k' + 1 by ring]; exact ha
  let T' : Finset ((∀ c : ι, List ℕ × List ℕ) × κ) :=
    (Fintype.piFinset (fun c => Sc c ×ˢ Sc c)) ×ˢ Xr
  let F : φ → (∀ c : ι, List ℕ × List ℕ) × κ :=
    fun f => ((fun c => (seqList (A c f) 1 (k c), seqList (B c f) 1 (k c))), E f)
  have hmap : ∀ f ∈ 𝓕, F f ∈ T' := by
    intro f hf
    simp only [T', F, mem_product, Fintype.mem_piFinset, hSc, mem_filter]
    refine ⟨fun c => ⟨⟨seqList_mem_bseqs _ _ _ _ (fun i hi => (hbd f hf c (1 + i) (by omega) (by omega)).1),
      tvle _ _ (htv f hf c).1⟩, ⟨seqList_mem_bseqs _ _ _ _ (fun i hi => (hbd f hf c (1 + i) (by omega) (by omega)).2),
      tvle _ _ (htv f hf c).2⟩⟩, hE f hf⟩
  have hinjOn : Set.InjOn F 𝓕 := by
    intro f hf g hg h
    simp only [F, Prod.mk.injEq] at h
    apply hinj f hf g hg _ h.2
    intro c i hi1 hi2
    have h1 := seqList_inj _ _ (k c) 1 (congrArg Prod.fst (congrFun h.1 c)) (i - 1) (by omega)
    have h2 := seqList_inj _ _ (k c) 1 (congrArg Prod.snd (congrFun h.1 c)) (i - 1) (by omega)
    rw [show 1 + (i - 1) = i by omega] at h1 h2
    exact ⟨h1, h2⟩
  calc 𝓕.card ≤ T'.card := Finset.card_le_card_of_injOn F hmap hinjOn
    _ = (∏ c, (Sc c).card ^ 2) * Xr.card := by
        simp only [T', card_product, Fintype.card_piFinset, sq]
    _ ≤ (∏ c, ((𝔇 + 1) * 3 ^ (k c + T)) ^ 2) * Xr.card := by
        apply Nat.mul_le_mul_right
        apply Finset.prod_le_prod' 
        intro c _
        exact Nat.pow_le_pow_left (card_S_le 𝔇 (k c) T) 2
    _ = _ := by ring

end WaveTurbulence.LayerCnt
