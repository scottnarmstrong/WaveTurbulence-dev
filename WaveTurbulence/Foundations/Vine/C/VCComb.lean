/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.C.VCUnit

/-! # VINE-C: class combinatorics for several units (twists at disjoint chains commute, S1 `OpsCommute`)

* `batch_partition`: a nodup batch `M` is the batch over the members of `M` with `P i` first, then the batch over the
  others (S1's `familyBatch_moveRight`, i.e. `opsCommute_all`).
* `batch_diamond`: two batches over disjoint member lists from one state can be completed to a commuting square (V5's
  `diamond_ind`, i.e. S1's `diamond_all`).
* `eq_of_sigStar_batch`: over a prime start, a state reached by a nodup batch is determined by the signatures `sigStar`
  of the members of the batch (V5's `zp_eq_of_sigStar`, `sigStar_batch`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineC
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg.Skeleton TTree

variable {w p : ℕ} {kind : Bool} {ι : Type*}

/-- **A nodup batch splits into the members with `P` first and the others afterwards.** -/
theorem batch_partition (P : ι → Bool) : ∀ (M : List ι), M.Nodup → ∀ {A B : FamilyReconstruction w ι},
    FamilyBatch p kind M A B →
      ∃ Y, FamilyBatch p kind (M.filter P) A Y ∧ FamilyBatch p kind (M.filter (fun i => !P i)) Y B := by
  intro M
  induction M with
  | nil =>
    intro _ A B h
    cases h
    exact ⟨A, .nil A, .nil A⟩
  | cons i M ih =>
    intro hM A B h
    obtain ⟨hiM, hM'⟩ := List.nodup_cons.mp hM
    obtain ⟨X, h1, h2⟩ : ∃ X, FamilyBatch p kind [i] A X ∧ FamilyBatch p kind M X B := by
      cases h with
      | skip _ h' => exact ⟨A, .skip i (.nil A), h'⟩
      | apply op h' => exact ⟨op.output, .apply op (.nil _), h'⟩
    obtain ⟨Y', hY1, hY2⟩ := ih hM' h2
    cases hP : P i
    · have e1 : (i :: M).filter P = M.filter P := by simp [hP]
      have e2 : (i :: M).filter (fun i => !P i) = i :: M.filter (fun i => !P i) := by simp [hP]
      rw [e1, e2]
      have hiK : i ∉ M.filter P := fun hh => hiM (List.mem_of_mem_filter hh)
      have h3 : FamilyBatch p kind (i :: M.filter P) A Y' := Stage1.familyBatch_append h1 hY1
      have h4 := Stage1.familyBatch_moveRight Stage1.opsCommute_all i (M.filter P) hiK h3
      obtain ⟨Y, hA, hB⟩ := Stage1.familyBatch_split h4
      exact ⟨Y, hA, Stage1.familyBatch_append hB hY2⟩
    · have e1 : (i :: M).filter P = i :: M.filter P := by simp [hP]
      have e2 : (i :: M).filter (fun i => !P i) = M.filter (fun i => !P i) := by simp [hP]
      rw [e1, e2]
      exact ⟨Y', Stage1.familyBatch_append h1 hY1, hY2⟩

/-- **Batches over disjoint member lists commute** (completion to a square). -/
theorem batch_diamond : ∀ (N : List ι) {M : List ι} {A X Z : FamilyReconstruction w ι},
    FamilyBatch p kind M A X → FamilyBatch p kind N A Z → (∀ i ∈ N, i ∉ M) →
      ∃ X', FamilyBatch p kind N X X' ∧ FamilyBatch p kind M Z X' := by
  intro N
  induction N with
  | nil =>
    intro M A X Z hM hN _
    cases hN
    exact ⟨X, .nil X, hM⟩
  | cons k N ih =>
    intro M A X Z hM hN hd
    obtain ⟨A1, hk, hN'⟩ := Stage1.familyBatch_split (L1 := [k]) (L2 := N) hN
    obtain ⟨X1, hM1, hk1⟩ := diamond_ind hM (hd k List.mem_cons_self) hk
    obtain ⟨X', h1, h2⟩ := ih hM1 hN' (fun i hi => hd i (List.mem_cons_of_mem _ hi))
    exact ⟨X', Stage1.familyBatch_append hk1 h1, h2⟩

variable [DecidableEq ι]

/-- A batch over a permutation of `i₀ :: M₁` is the operation at `i₀` first, then a batch over a permutation of `M₁`. -/
theorem batch_front {i₀ : ι} {M₁ M' : List ι} (hn : (i₀ :: M₁).Nodup) (hperm : M'.Perm (i₀ :: M₁))
    {A X : FamilyReconstruction w ι} (h : FamilyBatch p kind M' A X) :
    ∃ G N, FamilyBatch p kind [i₀] A G ∧ N.Perm M₁ ∧ FamilyBatch p kind N G X := by
  have hn' : M'.Nodup := hperm.nodup_iff.mpr hn
  obtain ⟨hi₀, _⟩ := List.nodup_cons.mp hn
  obtain ⟨G, h1, h2⟩ := batch_partition (fun i => decide (i = i₀)) M' hn' h
  have p1 := hperm.filter (fun i => decide (i = i₀))
  have p2 := hperm.filter (fun i => !decide (i = i₀))
  have f1 : (i₀ :: M₁).filter (fun i => decide (i = i₀)) = [i₀] := by
    have hnil : M₁.filter (fun i => decide (i = i₀)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx hxe
      have hxe' : x = i₀ := of_decide_eq_true hxe
      exact hi₀ (hxe' ▸ hx)
    simp [hnil]
  have f2 : (i₀ :: M₁).filter (fun i => !decide (i = i₀)) = M₁ := by
    have hall : M₁.filter (fun i => !decide (i = i₀)) = M₁ := by
      rw [List.filter_eq_self]
      intro x hx
      have : x ≠ i₀ := fun he => hi₀ (he ▸ hx)
      simpa using this
    simp [hall]
  rw [f1] at p1
  rw [f2] at p2
  have e1 : M'.filter (fun i => decide (i = i₀)) = [i₀] := List.perm_singleton.mp p1
  rw [e1] at h1
  exact ⟨G, _, h1, p2, h2⟩

/-- **Over a prime start, a state reached by a nodup batch is determined by the signatures of the batch's members.** -/
theorem eq_of_sigStar_batch : ∀ (M : List ι), M.Nodup → ∀ {A X X' : FamilyReconstruction w ι} {L L' : List ι},
    IsPrimeGarden A.skeleton → L.Perm M → L'.Perm M → FamilyBatch p kind L A X → FamilyBatch p kind L' A X' →
      (∀ i ∈ M, sigStar X i = sigStar X' i) → X = X' := by
  intro M
  induction M with
  | nil =>
    intro _ A X X' L L' _ hL hL' h h' _
    rw [List.perm_nil] at hL hL'
    subst hL hL'
    cases h; cases h'
    rfl
  | cons i₀ M₁ ih =>
    intro hn A X X' L L' hA hL hL' h h' hs
    obtain ⟨hi₀, hn₁⟩ := List.nodup_cons.mp hn
    obtain ⟨G, N, hG, hN, hX⟩ := batch_front hn hL h
    obtain ⟨G', N', hG', hN', hX'⟩ := batch_front hn hL' h'
    have hNi : i₀ ∉ N := fun hh => hi₀ (hN.mem_iff.mp hh)
    have hNi' : i₀ ∉ N' := fun hh => hi₀ (hN'.mem_iff.mp hh)
    have hs₀ : sigStar G i₀ = sigStar G' i₀ :=
      (sigStar_batch hX hNi).symm.trans ((hs i₀ List.mem_cons_self).trans (sigStar_batch hX' hNi'))
    have hGG : G = G' := zp_eq_of_sigStar hA hG hG' hs₀
    subst hGG
    exact ih hn₁ (batch_prime hG hA) hN hN' hX hX' (fun i hi => hs i (List.mem_cons_of_mem _ hi))

end WaveTurbulence.VineC
