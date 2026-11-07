/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.TVCount

/-! # Total variation of peak-free rung layer sequences (TARGET layerlad, unimodality step)

A configuration `(a, b)` assigns to rung `i` the layers `a i` (of `u_i`) and `b i` (of `v_i`).
It is *peak-free* when no coherent stretch of rungs has a strict increase followed by a later strict
decrease. TARGET's parent-chain claim ("`q_j ≤ ⋯ ≤ q_{j'}` and `q_j ≤ ⋯ ≤ q_{j''}` impossible",
L1507) says exactly that the layers of a coherent ladder segment are non-increasing and then
non-decreasing. Here we prove the consequence needed for the count: the total variation of the
rail layers is at most `8𝔇(g+1)` where `g` is the number of incoherent rungs.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset

/-- Rail variation of the sequence `a` on the rungs `s, …, e`. -/
@[expose] def tvF (a : ℕ → ℕ) (s e : ℕ) : ℕ := ∑ i ∈ Ico s e, dst (a i) (a (i + 1))

/-- Rail variation of both rails on the rungs `s, …, e`. -/
@[expose] def tvab (a b : ℕ → ℕ) (s e : ℕ) : ℕ :=
  ∑ i ∈ Ico s e, (dst (a i) (a (i + 1)) + dst (b i) (b (i + 1)))

/-- Number of incoherent rungs among `s, …, e`. -/
@[expose] def incCnt (a b : ℕ → ℕ) (s e : ℕ) : ℕ :=
  ∑ i ∈ Ico s (e + 1), (if a i = b i then 0 else 1)

/-- Peak-freeness: no coherent stretch of rungs `p, …, r+1` (`1 ≤ p`, `p+1 ≤ r`, `r+1 ≤ n`) has a strict
increase `a p < a (p+1)` and a later strict decrease `a (r+1) < a r`. -/
@[expose] def NoPeak (a b : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ p r : ℕ, 1 ≤ p → p + 1 ≤ r → r + 1 ≤ n → (∀ i, p ≤ i → i ≤ r + 1 → a i = b i) →
    ¬ (a p < a (p + 1) ∧ a (r + 1) < a r)

theorem tvF_mono (a : ℕ → ℕ) (s : ℕ) : ∀ d : ℕ, (∀ i, s ≤ i → i < s + d → a i ≤ a (i + 1)) →
    tvF a s (s + d) + a s = a (s + d) := by
  intro d
  induction d with
  | zero => intro _; simp [tvF]
  | succ d ih =>
    intro h
    have h1 := ih (fun i hi hi' => h i hi (by omega))
    have h2 := h (s + d) (by omega) (by omega)
    unfold tvF at *
    rw [show s + (d + 1) = (s + d) + 1 by omega, Finset.sum_Ico_succ_top (by omega), add_assoc,
      add_comm (dst _ _), ← add_assoc, h1]
    have : dst (a (s + d)) (a (s + d + 1)) = a (s + d + 1) - a (s + d) := by unfold dst; omega
    rw [this]
    omega

theorem tvF_nopeak (a : ℕ → ℕ) : ∀ d s : ℕ,
    (∀ p r, s ≤ p → p + 1 ≤ r → r + 1 ≤ s + d → ¬ (a p < a (p + 1) ∧ a (r + 1) < a r)) →
    tvF a s (s + d) ≤ a s + a (s + d) := by
  intro d
  induction d with
  | zero => intro s _; simp [tvF]
  | succ d ih =>
    intro s h
    have e : tvF a s (s + (d + 1)) = dst (a s) (a (s + 1)) + tvF a (s + 1) (s + 1 + d) := by
      unfold tvF
      rw [show s + (d + 1) = s + 1 + d by omega,
        Finset.sum_eq_sum_Ico_succ_bot (by omega : s < s + 1 + d)]
    have ih' := ih (s + 1) (fun p r hp hpr hr => h p r (by omega) hpr (by omega))
    rw [e, show s + (d + 1) = s + 1 + d by omega]
    by_cases hc : a (s + 1) ≤ a s
    · have : dst (a s) (a (s + 1)) = a s - a (s + 1) := by unfold dst; omega
      omega
    · have hup : a s < a (s + 1) := by omega
      have hmono : ∀ i, s + 1 ≤ i → i < s + 1 + d → a i ≤ a (i + 1) := by
        intro i hi hi'
        by_contra hlt
        exact h s i le_rfl (by omega) (by omega) ⟨hup, by omega⟩
      have := tvF_mono a (s + 1) d hmono
      have : dst (a s) (a (s + 1)) = a (s + 1) - a s := by unfold dst; omega
      omega

/-- A coherent window of a peak-free configuration. -/
theorem tvab_coherent {a b : ℕ → ℕ} {n 𝔇 : ℕ} (hnp : NoPeak a b n) {s e : ℕ} (hs : 1 ≤ s) (hse : s ≤ e)
    (he : e ≤ n) (hcoh : ∀ i, s ≤ i → i ≤ e → a i = b i) (hbd : ∀ i, s ≤ i → i ≤ e → a i ≤ 𝔇) :
    tvab a b s e ≤ 4 * 𝔇 := by
  have h1 : tvF a s (s + (e - s)) ≤ a s + a (s + (e - s)) := by
    apply tvF_nopeak
    intro p r hp hpr hr
    exact hnp p r (by omega) hpr (by omega) (fun i hi hi' => hcoh i (by omega) (by omega))
  rw [show s + (e - s) = e by omega] at h1
  have h2 : tvab a b s e = 2 * tvF a s e := by
    unfold tvab tvF
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [← hcoh i hi.1 (by omega), ← hcoh (i + 1) (by omega) (by omega)]
    ring
  have := hbd s le_rfl hse
  have := hbd e hse le_rfl
  omega

theorem dst_le {x y 𝔇 : ℕ} (hx : x ≤ 𝔇) (hy : y ≤ 𝔇) : dst x y ≤ 𝔇 := by unfold dst; omega

theorem incCnt_succ_le {a b : ℕ → ℕ} {s t e : ℕ} (hst : s ≤ t) (hte : t ≤ e) (hne : a t ≠ b t) :
    incCnt a b (t + 1) e + 1 ≤ incCnt a b s e := by
  unfold incCnt
  have h1 : ∑ i ∈ Ico s (e + 1), (if a i = b i then 0 else 1) =
      ∑ i ∈ Ico s t, (if a i = b i then 0 else 1) + ∑ i ∈ Ico t (e + 1), (if a i = b i then 0 else 1) :=
    (Finset.sum_Ico_consecutive _ hst (by omega)).symm
  have h2 : ∑ i ∈ Ico t (e + 1), (if a i = b i then 0 else 1) =
      (if a t = b t then 0 else 1) + ∑ i ∈ Ico (t + 1) (e + 1), (if a i = b i then 0 else 1) :=
    Finset.sum_eq_sum_Ico_succ_bot (by omega) _
  rw [h1, h2, if_neg hne]
  omega

theorem tvab_split {a b : ℕ → ℕ} {s t e : ℕ} (hst : s ≤ t) (hte : t ≤ e) :
    tvab a b s e = tvab a b s t + tvab a b t e :=
  (Finset.sum_Ico_consecutive _ hst hte).symm

theorem tvab_le {a b : ℕ → ℕ} {n 𝔇 : ℕ} (hnp : NoPeak a b n) :
    ∀ k s e : ℕ, 1 ≤ s → e ≤ n → incCnt a b s e ≤ k →
      (∀ i, s ≤ i → i ≤ e → a i ≤ 𝔇 ∧ b i ≤ 𝔇) → tvab a b s e ≤ 8 * 𝔇 * (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro s e hs he hk hbd
    by_cases hse : s ≤ e
    · have hcoh : ∀ i, s ≤ i → i ≤ e → a i = b i := by
        intro i hi hi'
        by_contra hne
        have : 1 ≤ incCnt a b s e := by
          unfold incCnt
          calc 1 = (if a i = b i then 0 else 1) := by simp [hne]
            _ ≤ _ := Finset.single_le_sum (f := fun i => if a i = b i then 0 else 1)
                (fun _ _ => Nat.zero_le _) (Finset.mem_Ico.mpr ⟨hi, by omega⟩)
        omega
      have := tvab_coherent hnp hs hse he hcoh (fun i hi hi' => (hbd i hi hi').1) (𝔇 := 𝔇)
      omega
    · have : tvab a b s e = 0 := by
        unfold tvab; rw [Finset.Ico_eq_empty (by omega)]; simp
      omega
  | succ k ih =>
    intro s e hs he hk hbd
    by_cases hse : s ≤ e
    swap
    · have : tvab a b s e = 0 := by
        unfold tvab; rw [Finset.Ico_eq_empty (by omega)]; simp
      omega
    by_cases hex : ∃ t, s ≤ t ∧ t ≤ e ∧ a t ≠ b t
    · classical
      obtain ⟨t, ⟨hst, hte, hne⟩, hmin⟩ : ∃ t, (s ≤ t ∧ t ≤ e ∧ a t ≠ b t) ∧
          ∀ i, s ≤ i → i < t → a i = b i := by
        refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
        intro i hi hit
        by_contra hh
        exact Nat.find_min hex hit ⟨hi, by have := (Nat.find_spec hex).2.1; omega, hh⟩
      have hcnt := incCnt_succ_le hst hte hne
      have hk' : incCnt a b (t + 1) e ≤ k := by omega
      have hsplit := tvab_split (a := a) (b := b) hst hte
      -- left part
      have hleft : tvab a b s t ≤ 6 * 𝔇 := by
        by_cases hts : t = s
        · have : tvab a b s t = 0 := by
            unfold tvab; rw [hts, Finset.Ico_self]; simp
          omega
        · have hsplit2 := tvab_split (a := a) (b := b) (s := s) (t := t - 1) (e := t) (by omega) (by omega)
          have hcoh : ∀ i, s ≤ i → i ≤ t - 1 → a i = b i := fun i hi hi' => hmin i hi (by omega)
          have h1 := tvab_coherent hnp hs (by omega : s ≤ t - 1) (by omega : t - 1 ≤ n) hcoh
            (fun i hi hi' => (hbd i hi (by omega)).1) (𝔇 := 𝔇)
          have h2 : tvab a b (t - 1) t ≤ 2 * 𝔇 := by
            obtain ⟨u, hu⟩ : ∃ u, u = t - 1 := ⟨_, rfl⟩
            have htu : t = u + 1 := by omega
            rw [← hu, htu]
            unfold tvab
            rw [Nat.Ico_succ_singleton]
            simp only [Finset.sum_singleton]
            have := dst_le (𝔇 := 𝔇) (hbd u (by omega) (by omega)).1 (hbd (u+1) (by omega) (by omega)).1
            have := dst_le (𝔇 := 𝔇) (hbd u (by omega) (by omega)).2 (hbd (u+1) (by omega) (by omega)).2
            omega
          omega
      have hright : tvab a b t e ≤ 2 * 𝔇 + 8 * 𝔇 * (k + 1) := by
        by_cases hte' : t = e
        · have : tvab a b t e = 0 := by
            unfold tvab; rw [hte', Finset.Ico_self]; simp
          omega
        · have hsplit3 := tvab_split (a := a) (b := b) (s := t) (t := t + 1) (e := e) (by omega) (by omega)
          have h1 : tvab a b t (t + 1) ≤ 2 * 𝔇 := by
            unfold tvab
            rw [Nat.Ico_succ_singleton]
            simp only [Finset.sum_singleton]
            have := dst_le (𝔇 := 𝔇) (hbd t hst hte).1 (hbd (t+1) (by omega) (by omega)).1
            have := dst_le (𝔇 := 𝔇) (hbd t hst hte).2 (hbd (t+1) (by omega) (by omega)).2
            omega
          have h2 := ih (t + 1) e (by omega) he hk' (fun i hi hi' => hbd i (by omega) hi')
          omega
      rw [hsplit]
      calc tvab a b s t + tvab a b t e ≤ 6 * 𝔇 + (2 * 𝔇 + 8 * 𝔇 * (k + 1)) := add_le_add hleft hright
        _ = 8 * 𝔇 * (k + 1 + 1) := by ring
    · push_neg at hex
      have hcoh : ∀ i, s ≤ i → i ≤ e → a i = b i := fun i hi hi' => hex i hi hi'
      have := tvab_coherent hnp hs hse he hcoh (fun i hi hi' => (hbd i hi hi').1) (𝔇 := 𝔇)
      nlinarith

end WaveTurbulence.LayerCnt
