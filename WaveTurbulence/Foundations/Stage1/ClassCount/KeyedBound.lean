/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.Classes
import Mathlib.Tactic

/-!
# CLASSCOUNT: summing the class bound over the keys

For fixed `(S, D, σ)`, the layered gardens of a family `A` (all with `ḡ = g`) are partitioned by the *key*
`(slot incoherencies, ingredient incoherencies, ladder incoherencies)`; the keys form a set of at most `2^{2g+1+|s_0|}`
functions, and each class is bounded by `class_bound`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.LayerCnt WaveTurbulence.Vine
  WaveTurbulence.Reg.Skeleton

theorem geom_sum_le (M : ℕ) : ∑ m ∈ range M, 2 ^ m ≤ 2 ^ M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have : 2 ^ (M + 1) = 2 ^ M + 2 ^ M := by ring
    omega

variable {R : ℕ}

/-- B2d: the index type of a key (marked set `Mk`). -/
abbrev KeyIdxMk {S : Garden (2 * R)} (σ : Prescription S) (Mk : Set (Stage1.CLVine S))
    (Tss : Fin (unitBlocks S σ Mk).length → List (Trip S)) : Type :=
  ReplacementSlot S ⊕ (TripIMk S σ Mk Tss ⊕ {T // T ∈ (stSt S σ Mk).G.molecule.maximalLadders})

/-- B2d: the key of a layered garden (marked set `Mk`). -/
noncomputable def keyOfMk {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain) (σ : Prescription S)
    (Mk : Set (Stage1.CLVine S)) (Tss : Fin (unitBlocks S σ Mk).length → List (Trip S)) (LG : LayeredGarden (2 * R)) : KeyIdxMk σ Mk Tss → ℕ :=
  Sum.elim (slotInc D hS LG) (Sum.elim (fun i => vineIncoh S (coreOf D hS LG) (tauMk Tss i).1)
    (fun i => incoherencyIndex (coreOf D hS LG ∘ (stSt S σ Mk).M.ob)
      (ladderGroups ((ladderDataOf (stSt S σ Mk).G).upper i) ((ladderDataOf (stSt S σ Mk).G).lower i))))

/-- B2d: the key sum is at most `2 ḡ` (any marked set). -/
theorem sum_key_leMk {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain) (σ : Prescription S)
    (Mk : Set (Stage1.CLVine S)) {Tss : Fin (unitBlocks S σ Mk).length → List (Trip S)}
    (h1 : ∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredient S.molecule ((unitBlocks S σ Mk).get j).atoms
          ((unitBlocks S σ Mk).get j).upper ((unitBlocks S σ Mk).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2)
    (h2 : ∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint)
    (LG : LayeredGarden (2 * R)) {g : ℕ}
    (hg : gbarRHS D hS LG (stSt S σ Mk) (Set.toFinite (unitIngredients S σ Mk)).toFinset = g) :
    ∑ k, keyOfMk D hS σ Mk Tss LG k ≤ 2 * g := by
  classical
  have hfib := sum_le_two_mul_of_fiber (fun i : TripIMk S σ Mk Tss => (tauMk Tss i).1) (fun i => (tauMk Tss i).2.1)
    (fun i => (tau_specMk h1 i).2.1) (fun i => tau_nonemptyMk h1 i) (fun i i' hne => tau_disjointMk h1 h2 hne)
    ((Finset.univ : Finset (TripIMk S σ Mk Tss)).image (fun i => (tauMk Tss i).1))
    (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)) (fun T => vineIncoh S (coreOf D hS LG) T)
  have hsub : ∑ T ∈ (Finset.univ : Finset (TripIMk S σ Mk Tss)).image (fun i => (tauMk Tss i).1),
      vineIncoh S (coreOf D hS LG) T ≤ ∑ T ∈ (Set.toFinite (unitIngredients S σ Mk)).toFinset,
      vineIncoh S (coreOf D hS LG) T := by
    refine Finset.sum_le_sum_of_subset ?_
    intro T hT
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hT
    exact (Set.toFinite _).mem_toFinset.2 (tau_specMk h1 i).2.2.2.2
  unfold gbarRHS at hg
  have : ∑ k, keyOfMk D hS σ Mk Tss LG k = ∑ s, slotInc D hS LG s +
      ∑ i : TripIMk S σ Mk Tss, vineIncoh S (coreOf D hS LG) (tauMk Tss i).1 +
      ∑ i : {T // T ∈ (stSt S σ Mk).G.molecule.maximalLadders},
        incoherencyIndex (coreOf D hS LG ∘ (stSt S σ Mk).M.ob)
          (ladderGroups ((ladderDataOf (stSt S σ Mk).G).upper i) ((ladderDataOf (stSt S σ Mk).G).lower i)) := by
    simp only [keyOfMk, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    ring
  rw [this]
  omega

open Classical in
/-- B2d: **the bound for a family of layered gardens with common `ḡ` over one skeleton, one `σ` and one
marked set `Mk`.** -/
theorem keyed_boundMk : ∃ K0 : ℝ, 2 ≤ K0 ∧ ∀ {R : ℕ} (S : Garden (2 * R)) (hS : S.IsPlain)
    (D : ReconstructionData S) (σ : Prescription S) (Mk : Set (Stage1.CLVine S)) (p g r N : ℕ) (A : Finset (LayeredGarden (2 * R)))
    (hA : ∀ LG ∈ A, IsCanonGC (p + 1) LG ∧ ∃ hd : D.Decodes hS LG.garden,
      gbarRHS D hS LG (stSt S σ Mk) (Set.toFinite (unitIngredients S σ Mk)).toFinset = g)
    (hr : (stSt S σ Mk).G.molecule.rho + (unitBlocks S σ Mk).length ≤ r) (hsize : D.size ≤ N)
    (hn : Fintype.card (GBranch S.tree) ≤ N),
    (A.card : ℝ) ≤ (2 : ℝ) ^ (2 * g + 1 + N + N + r) *
      (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g)) := by
  obtain ⟨K0, hK0, hCB⟩ := class_boundMk
  refine ⟨K0, hK0, ?_⟩
  intro R S hS D σ Mk p g r N A hA hr hsize hn
  obtain ⟨Tss, h1, h2, hmain⟩ := hCB S hS D σ Mk
  have hK1 : 1 ≤ K0 := by linarith
  have hK00 : 0 ≤ K0 := by linarith
  set s0 : Finset (KeyIdxMk σ Mk Tss) :=
    ((Finset.univ : Finset (ReplacementSlot S)).filter (fun s => slotSize D s ≠ 0)).image
        (Sum.inl : ReplacementSlot S → KeyIdxMk σ Mk Tss) ∪
      (Finset.univ : Finset (TripIMk S σ Mk Tss ⊕ {T // T ∈ (stSt S σ Mk).G.molecule.maximalLadders})).image
        (Sum.inr : (TripIMk S σ Mk Tss ⊕ {T // T ∈ (stSt S σ Mk).G.molecule.maximalLadders}) → KeyIdxMk σ Mk Tss)
    with hs0
  have hs0card : s0.card ≤ N + N + r := by
    refine (Finset.card_union_le _ _).trans ?_
    have a1 := Finset.card_image_le (s := (Finset.univ : Finset (ReplacementSlot S)).filter
      (fun s => slotSize D s ≠ 0)) (f := (Sum.inl : ReplacementSlot S → KeyIdxMk σ Mk Tss))
    have a2 := Finset.card_image_le (s := (Finset.univ : Finset (TripIMk S σ Mk Tss ⊕
      {T // T ∈ (stSt S σ Mk).G.molecule.maximalLadders}))) (f := (Sum.inr : (TripIMk S σ Mk Tss ⊕
      {T // T ∈ (stSt S σ Mk).G.molecule.maximalLadders}) → KeyIdxMk σ Mk Tss))
    have a3 := card_slots_nonempty_le D
    have a4 := card_tripI_leMk h1 h2
    have a5 := card_ladders_le_rho (stSt S σ Mk).G
    simp only [Finset.card_univ, Fintype.card_sum] at a2
    omega
  set K : Finset (KeyIdxMk σ Mk Tss → ℕ) := (Finset.range (2 * g + 1)).biUnion (fun m => Finset.piAntidiag s0 m) with hK
  have hKcard : K.card ≤ 2 ^ (2 * g + 1 + s0.card) := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ m ∈ Finset.range (2 * g + 1), (Finset.piAntidiag s0 m).card
        ≤ ∑ m ∈ Finset.range (2 * g + 1), 2 ^ (m + s0.card) :=
          Finset.sum_le_sum fun m _ => card_piAntidiag_le s0 m
      _ = 2 ^ s0.card * ∑ m ∈ Finset.range (2 * g + 1), 2 ^ m := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by rw [pow_add, mul_comm]
      _ ≤ 2 ^ s0.card * 2 ^ (2 * g + 1) := Nat.mul_le_mul_left _ (geom_sum_le _)
      _ = 2 ^ (2 * g + 1 + s0.card) := by rw [← pow_add, add_comm]
  have hkey : ∀ LG ∈ A, keyOfMk D hS σ Mk Tss LG ∈ K := by
    intro LG hLG
    obtain ⟨-, hd, hg⟩ := hA LG hLG
    have hsum := sum_key_leMk D hS σ Mk h1 h2 LG hg
    have hle : s0.sum (keyOfMk D hS σ Mk Tss LG) ≤ 2 * g :=
      (Finset.sum_le_sum_of_subset (Finset.subset_univ s0)).trans hsum
    rw [hK, Finset.mem_biUnion]
    refine ⟨s0.sum (keyOfMk D hS σ Mk Tss LG), Finset.mem_range.2 (by omega), ?_⟩
    rw [Finset.mem_piAntidiag]
    refine ⟨rfl, fun i hi => ?_⟩
    rcases i with s | i
    · rw [hs0, Finset.mem_union]
      left
      rw [Finset.mem_image]
      refine ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun h => hi ?_⟩, rfl⟩
      exact slotInc_eq_zero_of_size D hS LG s h
    · rw [hs0, Finset.mem_union]
      right
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
  have hfib : A.card = ∑ κ ∈ K, (A.filter (fun LG => keyOfMk D hS σ Mk Tss LG = κ)).card :=
    Finset.card_eq_sum_card_fiberwise (fun LG hLG => hkey LG hLG)
  have hclass : ∀ κ ∈ K, ((A.filter (fun LG => keyOfMk D hS σ Mk Tss LG = κ)).card : ℝ) ≤
      2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g) := by
    intro κ hκ
    set Aκ := A.filter (fun LG => keyOfMk D hS σ Mk Tss LG = κ) with hAκ
    have hpos0 : 0 ≤ (2 : ℝ) ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g) := by positivity
    by_cases hemp : Aκ = ∅
    · rw [hemp]; simpa using hpos0
    obtain ⟨LG0, hLG0⟩ := Finset.nonempty_iff_ne_empty.2 hemp
    have key_of : ∀ LG ∈ Aκ, keyOfMk D hS σ Mk Tss LG = κ := fun LG h => (Finset.mem_filter.1 h).2
    have hAm : ∀ LG ∈ Aκ, LG ∈ A := fun LG h => (Finset.mem_filter.1 h).1
    set gs : ReplacementSlot S → ℕ := fun s => κ (Sum.inl s) with hgs
    set γ : {T // T ∈ (stSt S σ Mk).G.molecule.maximalLadders} → ℕ := fun i => κ (Sum.inr (Sum.inr i)) with hγ
    set V : ℕ := ∑ T ∈ (Set.toFinite (unitIngredients S σ Mk)).toFinset, vineIncoh S (coreOf D hS LG0) T with hV
    have hdec : ∀ LG ∈ Aκ, ∑ T ∈ (Set.toFinite (unitIngredients S σ Mk)).toFinset,
        vineIncoh S (coreOf D hS LG) T + ∑ s, gs s + ∑ i, γ i = g := by
      intro LG hLG
      obtain ⟨-, hd, hg⟩ := hA LG (hAm LG hLG)
      unfold gbarRHS at hg
      have e1 : ∀ s, slotInc D hS LG s = gs s := fun s => congrFun (key_of LG hLG) (Sum.inl s)
      have e2 : ∀ i, incoherencyIndex (coreOf D hS LG ∘ (stSt S σ Mk).M.ob)
          (ladderGroups ((ladderDataOf (stSt S σ Mk).G).upper i) ((ladderDataOf (stSt S σ Mk).G).lower i)) = γ i :=
        fun i => congrFun (key_of LG hLG) (Sum.inr (Sum.inr i))
      have e1' : ∑ s, slotInc D hS LG s = ∑ s, gs s := Finset.sum_congr rfl fun s _ => e1 s
      have e2' : ∑ i : {T // T ∈ (stSt S σ Mk).G.molecule.maximalLadders},
          incoherencyIndex (coreOf D hS LG ∘ (stSt S σ Mk).M.ob)
          (ladderGroups ((ladderDataOf (stSt S σ Mk).G).upper i) ((ladderDataOf (stSt S σ Mk).G).lower i)) =
          ∑ i, γ i := Finset.sum_congr rfl fun i _ => e2 i
      linarith
    have hVeq : ∀ LG ∈ Aκ, ∑ T ∈ (Set.toFinite (unitIngredients S σ Mk)).toFinset,
        vineIncoh S (coreOf D hS LG) T = V := by
      intro LG hLG
      have := hdec LG hLG
      have := hdec LG0 hLG0
      omega
    have hbase := hmain p Aκ gs γ V (fun LG hLG => by
        obtain ⟨hc, hd, -⟩ := hA LG (hAm LG hLG)
        exact ⟨hc, hd, fun s => congrFun (key_of LG hLG) (Sum.inl s),
          fun i => congrFun (key_of LG hLG) (Sum.inr (Sum.inr i))⟩)
      (fun LG hLG LG' hLG' i => by
        have a1 := congrFun (key_of LG hLG) (Sum.inr (Sum.inl i))
        have a2 := congrFun (key_of LG' hLG') (Sum.inr (Sum.inl i))
        exact a1.trans a2.symm)
      (fun LG hLG => le_of_eq (hVeq LG hLG))
    have hg0 := hdec LG0 hLG0
    have hexp : 24 * ((stSt S σ Mk).G.molecule.rho + (unitBlocks S σ Mk).length) + 15 * ∑ s, gs s + ∑ i, γ i + 8 * V ≤
        24 * r + 15 * g := by omega
    have hX1 : (1 : ℝ) ≤ K0 ^ (p + 1) := one_le_pow₀ hK1
    calc (Aκ.card : ℝ) ≤ (2 : ℝ) ^ D.size * K0 ^ (4 * Fintype.card (GBranch S.tree)) *
          (K0 ^ (p + 1)) ^ (24 * ((stSt S σ Mk).G.molecule.rho + (unitBlocks S σ Mk).length) + 15 * ∑ s, gs s +
            ∑ i, γ i + 8 * V) := hbase
      _ ≤ (2 : ℝ) ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g) := by
          have b1 : (2 : ℝ) ^ D.size ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hsize
          have b2 : K0 ^ (4 * Fintype.card (GBranch S.tree)) ≤ K0 ^ (4 * N) :=
            pow_le_pow_right₀ hK1 (by omega)
          have b3 := pow_le_pow_right₀ hX1 hexp
          gcongr
  have hKR : (K.card : ℝ) ≤ (2 : ℝ) ^ (2 * g + 1 + N + N + r) := by
    have : K.card ≤ 2 ^ (2 * g + 1 + N + N + r) :=
      hKcard.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact_mod_cast this
  have hpos : 0 ≤ 2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g) := by positivity
  rw [hfib, Nat.cast_sum]
  calc ∑ κ ∈ K, ((A.filter (fun LG => keyOfMk D hS σ Mk Tss LG = κ)).card : ℝ)
      ≤ ∑ κ ∈ K, 2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g) :=
        Finset.sum_le_sum hclass
    _ = (K.card : ℝ) * (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hKR hpos

open Classical in
/-- **The bound for a family of layered gardens with common `ḡ` over one skeleton and one `σ`.** -/
theorem keyed_bound : ∃ K0 : ℝ, 2 ≤ K0 ∧ ∀ {R : ℕ} (S : Garden (2 * R)) (hS : S.IsPlain)
    (D : ReconstructionData S) (σ : Prescription S) (p g r N : ℕ) (A : Finset (LayeredGarden (2 * R)))
    (hA : ∀ LG ∈ A, IsCanonGC (p + 1) LG ∧ ∃ hd : D.Decodes hS LG.garden,
      gbarRHS D hS LG (stSt S σ) (Set.toFinite (unitIngredients S σ)).toFinset = g)
    (hr : (stSt S σ).G.molecule.rho + (unitBlocks S σ).length ≤ r) (hsize : D.size ≤ N)
    (hn : Fintype.card (GBranch S.tree) ≤ N),
    (A.card : ℝ) ≤ (2 : ℝ) ^ (2 * g + 1 + N + N + r) *
      (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g)) :=
  let ⟨K0, hK0, h⟩ := keyed_boundMk
  ⟨K0, hK0, fun S hS D σ => h S hS D σ ∅⟩

end WaveTurbulence.ClassCount
