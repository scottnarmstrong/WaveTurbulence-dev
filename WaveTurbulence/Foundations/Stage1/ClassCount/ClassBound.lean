/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.WeightSum
public import WaveTurbulence.Foundations.Stage1.ClassCount.SRCount
public import WaveTurbulence.Foundations.Stage1.ClassCount.RootDef
import Mathlib.Tactic

/-!
# CLASSCOUNT: the bound for one class of layered gardens

For fixed `(S, D, σ)`, `p`, slot incoherencies `gs`, per-ingredient incoherencies `gfix` and per-ladder incoherencies
`γ`, the number of canonical layered gardens decoded by `D` with these data is at most
`2^{|D|} K0^{4n} (K0^{p+1})^{24 ρ̄ + 17 g}`, `g = Σ gs + V + Σ γ` (TARGET L2248-L2252, with the run/bad accounting of
`ChainSum`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.LayerCnt WaveTurbulence.Vine
  WaveTurbulence.Reg.Skeleton

theorem listSum_filter_eq {α : Type*} (L : List α) (P : α → Prop) [DecidablePred P] (f : α → ℕ) :
    ((L.filter P).map f).sum = ∑ k : Fin L.length, if P (L.get k) then f (L.get k) else 0 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    show _ = ∑ k : Fin (L.length + 1), if P ((a :: L).get k) then f ((a :: L).get k) else 0
    rw [Fin.sum_univ_succ]
    simp only [List.filter_cons]
    by_cases h : P a
    · simp [h, ih]
    · simp [h, ih]

variable {w : ℕ}

/-- B2d: the index of the canonical ingredient triples of all units at the marked set `Mk`. -/
abbrev TripIMk (S : Garden w) (σ : Prescription S) (Mk : Set (Stage1.CLVine S))
    (Tss : Fin (unitBlocks S σ Mk).length → List (Trip S)) : Type :=
  Σ j : Fin (unitBlocks S σ Mk).length, Fin (Tss j).length

/-- B2d: the ingredient triple of an index (marked set `Mk`). -/
def tauMk {S : Garden w} {σ : Prescription S} {Mk : Set (Stage1.CLVine S)}
    (Tss : Fin (unitBlocks S σ Mk).length → List (Trip S))
    (i : TripIMk S σ Mk Tss) : Trip S := (Tss i.1).get i.2

section tripfactsMk
variable {S : Garden w} {σ : Prescription S} {Mk : Set (Stage1.CLVine S)} {Tss : Fin (unitBlocks S σ Mk).length → List (Trip S)}
  (h1 : ∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredient S.molecule ((unitBlocks S σ Mk).get j).atoms
          ((unitBlocks S σ Mk).get j).upper ((unitBlocks S σ Mk).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2)
  (h2 : ∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint)

include h1 in
theorem tau_specMk (i : TripIMk S σ Mk Tss) :
    (tauMk Tss i).1 ⊆ ((unitBlocks S σ Mk).get i.1).atoms ∧ (tauMk Tss i).2.1 ∈ (tauMk Tss i).1 ∧
      (tauMk Tss i).2.2 ∈ (tauMk Tss i).1 ∧ (tauMk Tss i).2.1 ≠ (tauMk Tss i).2.2 ∧
      (tauMk Tss i).1 ∈ unitIngredients S σ Mk := by
  obtain ⟨n, hn⟩ := h1 i.1
  have hi := (hn _ (List.get_mem (Tss i.1) i.2)).1
  have hsp := chainIngredient_spec hi
  obtain ⟨X, hX, -, -⟩ := vmOf_spec hsp.2.1
  refine ⟨hsp.2.2, hX.1.2.1, hX.1.2.2.1, hX.1.2.2.2.1, ?_⟩
  exact ⟨(unitBlocks S σ Mk).get i.1, List.get_mem _ _, _, _, n, _, _, hi⟩

include h1 h2 in
theorem tau_disjointMk {i i' : TripIMk S σ Mk Tss} (hne : i ≠ i') :
    Disjoint ((tauMk Tss i).1.erase (tauMk Tss i).2.1) ((tauMk Tss i').1.erase (tauMk Tss i').2.1) := by
  classical
  obtain ⟨j, k⟩ := i
  obtain ⟨j', k'⟩ := i'
  by_cases hj : j = j'
  · subst hj
    have hk : k ≠ k' := fun h => hne (by rw [h])
    have hp := List.pairwise_iff_get.mp (h2 j)
    rcases lt_or_gt_of_ne hk with h | h
    · have := hp ⟨k.1, by simp⟩ ⟨k'.1, by simp⟩ h
      simpa [tauMk] using this
    · have := hp ⟨k'.1, by simp⟩ ⟨k.1, by simp⟩ h
      simpa [tauMk] using this.symm
  · have hpair := List.pairwise_iff_get.mp (unitBlocks_pairwiseMk (Mole.garden_isMolecule S) σ Mk)
    have hU : Disjoint ((unitBlocks S σ Mk).get j).atoms ((unitBlocks S σ Mk).get j').atoms := by
      rcases lt_or_gt_of_ne hj with h | h
      · exact hpair j j' h
      · exact (hpair j' j h).symm
    exact Finset.disjoint_of_subset_left ((Finset.erase_subset _ _).trans (tau_specMk h1 ⟨j, k⟩).1)
      (Finset.disjoint_of_subset_right ((Finset.erase_subset _ _).trans (tau_specMk h1 ⟨j', k'⟩).1) hU)

include h1 in
theorem tau_nonemptyMk (i : TripIMk S σ Mk Tss) : ((tauMk Tss i).1.erase (tauMk Tss i).2.1).Nonempty := by
  obtain ⟨-, hx, hy, hxy, -⟩ := tau_specMk h1 i
  exact ⟨(tauMk Tss i).2.2, Finset.mem_erase.2 ⟨hxy.symm, hy⟩⟩

end tripfactsMk

/-- The index of the canonical ingredient triples of all units. -/
abbrev TripI (S : Garden w) (σ : Prescription S) (Tss : Fin (unitBlocks S σ).length → List (Trip S)) : Type :=
  Σ j : Fin (unitBlocks S σ).length, Fin (Tss j).length

/-- The ingredient triple of an index. -/
def tau {S : Garden w} {σ : Prescription S} (Tss : Fin (unitBlocks S σ).length → List (Trip S))
    (i : TripI S σ Tss) : Trip S := (Tss i.1).get i.2

section tripfacts
variable {S : Garden w} {σ : Prescription S} {Tss : Fin (unitBlocks S σ).length → List (Trip S)}
  (h1 : ∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredient S.molecule ((unitBlocks S σ).get j).atoms
          ((unitBlocks S σ).get j).upper ((unitBlocks S σ).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2)
  (h2 : ∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint)

include h1 in
theorem tau_spec (i : TripI S σ Tss) :
    (tau Tss i).1 ⊆ ((unitBlocks S σ).get i.1).atoms ∧ (tau Tss i).2.1 ∈ (tau Tss i).1 ∧
      (tau Tss i).2.2 ∈ (tau Tss i).1 ∧ (tau Tss i).2.1 ≠ (tau Tss i).2.2 ∧
      (tau Tss i).1 ∈ unitIngredients S σ :=
  tau_specMk (Mk := ∅) h1 i

include h1 h2 in
theorem tau_disjoint {i i' : TripI S σ Tss} (hne : i ≠ i') :
    Disjoint ((tau Tss i).1.erase (tau Tss i).2.1) ((tau Tss i').1.erase (tau Tss i').2.1) :=
  tau_disjointMk (Mk := ∅) h1 h2 hne

include h1 in
theorem tau_nonempty (i : TripI S σ Tss) : ((tau Tss i).1.erase (tau Tss i).2.1).Nonempty :=
  tau_nonemptyMk (Mk := ∅) h1 i

end tripfacts

open Classical in
/-- B2d: **the bad-ingredient exponent** at any marked set. -/
theorem E_leMk {S : Garden w} (hS : S.IsPlain) {σ : Prescription S} {Mk : Set (Stage1.CLVine S)} (D : ReconstructionData S) (p : ℕ)
    {Tss : Fin (unitBlocks S σ Mk).length → List (Trip S)}
    (h1 : ∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredient S.molecule ((unitBlocks S σ Mk).get j).atoms
          ((unitBlocks S σ Mk).get j).upper ((unitBlocks S σ Mk).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2)
    (h2 : ∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint)
    (A : Finset (LayeredGarden w)) (gs : ReplacementSlot S → ℕ)
    (hA : ∀ LG ∈ A, IsCanonGC (p + 1) LG ∧ ∃ hd : D.Decodes hS LG.garden, ∀ s, slotInc D hS LG s = gs s)
    (gfix : Finset (GBranch S.tree) → ℕ) :
    ∑ j, (((Tss j).filter (fun t => ¬ GoodIng S hS p (A.image (coreOf D hS)) gfix t)).map
        (fun t => gfix t.1 + 3)).sum ≤
      8 * ∑ T ∈ (Finset.univ : Finset (TripIMk S σ Mk Tss)).image (fun i => (tauMk Tss i).1), gfix T +
        6 * ∑ s, gs s := by
  set 𝓖 := A.image (coreOf D hS) with h𝓖
  -- convert to a sum over the index
  have hconv : ∑ j, (((Tss j).filter (fun t => ¬ GoodIng S hS p 𝓖 gfix t)).map (fun t => gfix t.1 + 3)).sum =
      ∑ i : TripIMk S σ Mk Tss, if ¬ GoodIng S hS p 𝓖 gfix (tauMk Tss i) then gfix (tauMk Tss i).1 + 3 else 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [listSum_filter_eq]
    rfl
  rw [hconv]
  set RB : TripIMk S σ Mk Tss → Prop := fun i => ∃ s, regionHas hS (tauMk Tss i).1 (tauMk Tss i).2.1 s ∧ 1 ≤ gs s with hRB
  have hpt : ∀ i : TripIMk S σ Mk Tss, (if ¬ GoodIng S hS p 𝓖 gfix (tauMk Tss i) then gfix (tauMk Tss i).1 + 3 else 0) ≤
      4 * gfix (tauMk Tss i).1 + (if RB i then 3 else 0) := by
    intro i
    by_cases hg : GoodIng S hS p 𝓖 gfix (tauMk Tss i)
    · rw [if_neg (not_not.2 hg)]; omega
    · rw [if_pos hg]
      by_cases hz : gfix (tauMk Tss i).1 = 0
      · have hRBi : RB i := by
          by_contra hno
          apply hg
          refine ⟨?_, hz, ?_⟩
          · obtain ⟨n, hn⟩ := h1 i.1
            exact (hn _ (List.get_mem (Tss i.1) i.2)).2
          · intro f hf
            obtain ⟨LG, hLG, rfl⟩ := Finset.mem_image.1 hf
            obtain ⟨hc, hd, hinc⟩ := hA LG hLG
            refine sourceRegion_of_zero hS p hc D hd _ _ (fun s hs => ?_)
            rw [hinc s]
            by_contra hne
            exact hno ⟨s, hs, by omega⟩
        rw [if_pos hRBi, hz]
      · have : 1 ≤ gfix (tauMk Tss i).1 := by omega
        split_ifs <;> omega
  have hsum1 : ∑ i : TripIMk S σ Mk Tss, (4 * gfix (tauMk Tss i).1 + (if RB i then 3 else 0)) =
      4 * ∑ i : TripIMk S σ Mk Tss, gfix (tauMk Tss i).1 + 3 * (Finset.univ.filter (fun i => RB i)).card := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    ring
  have hfib := sum_le_two_mul_of_fiber (fun i : TripIMk S σ Mk Tss => (tauMk Tss i).1) (fun i => (tauMk Tss i).2.1)
    (fun i => (tau_specMk h1 i).2.1) (fun i => tau_nonemptyMk h1 i) (fun i i' hne => tau_disjointMk h1 h2 hne)
    ((Finset.univ : Finset (TripIMk S σ Mk Tss)).image (fun i => (tauMk Tss i).1))
    (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)) gfix
  have hcard := card_bad_region_le hS (fun i : TripIMk S σ Mk Tss => (tauMk Tss i).1) (fun i => (tauMk Tss i).2.1)
    (fun i i' hne => tau_disjointMk h1 h2 hne) gs
  calc ∑ i : TripIMk S σ Mk Tss, (if ¬ GoodIng S hS p 𝓖 gfix (tauMk Tss i) then gfix (tauMk Tss i).1 + 3 else 0)
      ≤ ∑ i : TripIMk S σ Mk Tss, (4 * gfix (tauMk Tss i).1 + (if RB i then 3 else 0)) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ ≤ _ := by
        have hcard' : (Finset.univ.filter (fun i => RB i)).card ≤ 2 * ∑ s, gs s := hcard
        rw [hsum1]; omega

open Classical in
/-- **The bad-ingredient exponent.** -/
theorem E_le {S : Garden w} (hS : S.IsPlain) {σ : Prescription S} (D : ReconstructionData S) (p : ℕ)
    {Tss : Fin (unitBlocks S σ).length → List (Trip S)}
    (h1 : ∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredient S.molecule ((unitBlocks S σ).get j).atoms
          ((unitBlocks S σ).get j).upper ((unitBlocks S σ).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2)
    (h2 : ∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint)
    (A : Finset (LayeredGarden w)) (gs : ReplacementSlot S → ℕ)
    (hA : ∀ LG ∈ A, IsCanonGC (p + 1) LG ∧ ∃ hd : D.Decodes hS LG.garden, ∀ s, slotInc D hS LG s = gs s)
    (gfix : Finset (GBranch S.tree) → ℕ) :
    ∑ j, (((Tss j).filter (fun t => ¬ GoodIng S hS p (A.image (coreOf D hS)) gfix t)).map
        (fun t => gfix t.1 + 3)).sum ≤
      8 * ∑ T ∈ (Finset.univ : Finset (TripI S σ Tss)).image (fun i => (tau Tss i).1), gfix T +
        6 * ∑ s, gs s :=
  E_leMk (Mk := ∅) hS D p h1 h2 A gs hA gfix

theorem class_numerics {K0 : ℝ} (hK2 : 2 ≤ K0) {p G Γ ρq E V rt size n : ℕ} {cardA Sg : ℝ} (hSg0 : 0 ≤ Sg)
    (hb1 : cardA ≤ ((2 : ℝ) ^ (9 * p)) ^ G * 2 ^ size * 2 ^ (p * rt) * Sg)
    (hw : Sg ≤ K0 ^ (4 * n) * (K0 ^ (p + 1)) ^ (8 * ρq + Γ + E)) (hE : E ≤ 8 * V + 6 * G)
    (hrt : rt ≤ 16 * ρq) :
    cardA ≤ (2 : ℝ) ^ size * K0 ^ (4 * n) * (K0 ^ (p + 1)) ^ (24 * ρq + 15 * G + Γ + 8 * V) := by
  have hK1 : 1 ≤ K0 := by linarith
  have hK0 : 0 ≤ K0 := by linarith
  set X : ℝ := K0 ^ (p + 1) with hX
  have hX1 : 1 ≤ X := one_le_pow₀ hK1
  have h2p : (2 : ℝ) ^ p ≤ X := by
    calc (2 : ℝ) ^ p ≤ K0 ^ p := pow_le_pow_left₀ (by norm_num) hK2 p
      _ ≤ K0 ^ (p + 1) := pow_le_pow_right₀ hK1 (by omega)
  have hA1 : ((2 : ℝ) ^ (9 * p)) ^ G ≤ X ^ (9 * G) := by
    calc ((2 : ℝ) ^ (9 * p)) ^ G = ((2 : ℝ) ^ p) ^ (9 * G) := by
          rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ ≤ X ^ (9 * G) := pow_le_pow_left₀ (by positivity) h2p _
  have hA2 : (2 : ℝ) ^ (p * rt) ≤ X ^ (16 * ρq) := by
    rw [pow_mul]
    calc ((2 : ℝ) ^ p) ^ rt ≤ X ^ rt := pow_le_pow_left₀ (by positivity) h2p _
      _ ≤ X ^ (16 * ρq) := pow_le_pow_right₀ hX1 hrt
  calc cardA ≤ ((2 : ℝ) ^ (9 * p)) ^ G * 2 ^ size * 2 ^ (p * rt) * Sg := hb1
    _ ≤ X ^ (9 * G) * 2 ^ size * X ^ (16 * ρq) * (K0 ^ (4 * n) * X ^ (8 * ρq + Γ + E)) := by
        gcongr
    _ = 2 ^ size * K0 ^ (4 * n) * X ^ (9 * G + 16 * ρq + (8 * ρq + Γ + E)) := by
        rw [pow_add, pow_add]; ring
    _ ≤ 2 ^ size * K0 ^ (4 * n) * X ^ (24 * ρq + 15 * G + Γ + 8 * V) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (by omega)) (by positivity)

open Classical in
/-- B2d: **the class bound** at any marked set. -/
theorem class_boundMk : ∃ K0 : ℝ, 2 ≤ K0 ∧ ∀ {w : ℕ} (S : Garden w) (hS : S.IsPlain) (D : ReconstructionData S)
    (σ : Prescription S) (Mk : Set (Stage1.CLVine S)),
    ∃ Tss : Fin (unitBlocks S σ Mk).length → List (Trip S),
      (∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredient S.molecule ((unitBlocks S σ Mk).get j).atoms
          ((unitBlocks S σ Mk).get j).upper ((unitBlocks S σ Mk).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2) ∧
      (∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint) ∧
      ∀ (p : ℕ) (A : Finset (LayeredGarden w)) (gs : ReplacementSlot S → ℕ)
        (γ : {T // T ∈ (stSt S σ Mk).G.molecule.maximalLadders} → ℕ) (V : ℕ)
        (hA : ∀ LG ∈ A, IsCanonGC (p + 1) LG ∧ ∃ hd : D.Decodes hS LG.garden, (∀ s, slotInc D hS LG s = gs s) ∧
          ∀ i, incoherencyIndex (coreOf D hS LG ∘ (stSt S σ Mk).M.ob)
            (ladderGroups ((ladderDataOf (stSt S σ Mk).G).upper i) ((ladderDataOf (stSt S σ Mk).G).lower i)) = γ i)
        (hconst : ∀ LG ∈ A, ∀ LG' ∈ A, ∀ i : TripIMk S σ Mk Tss,
          vineIncoh S (coreOf D hS LG) (tauMk Tss i).1 = vineIncoh S (coreOf D hS LG') (tauMk Tss i).1)
        (hV : ∀ LG ∈ A, ∑ T ∈ (Set.toFinite (unitIngredients S σ Mk)).toFinset, vineIncoh S (coreOf D hS LG) T ≤ V),
      (A.card : ℝ) ≤ (2 : ℝ) ^ D.size * K0 ^ (4 * Fintype.card (GBranch S.tree)) *
        (K0 ^ (p + 1)) ^ (24 * ((stSt S σ Mk).G.molecule.rho + (unitBlocks S σ Mk).length) + 15 * ∑ s, gs s +
          ∑ i, γ i + 8 * V) := by
  obtain ⟨K0, hK0, hW⟩ := weight_sum_leMk
  refine ⟨K0, hK0, ?_⟩
  intro w S hS D σ Mk
  obtain ⟨Tss, h1, h2, hmain⟩ := hW S hS σ Mk
  refine ⟨Tss, h1, h2, ?_⟩
  intro p A gs γ V hA hconst hV
  have hK1 : 1 ≤ K0 := by linarith
  have hK0' : 0 ≤ K0 := by linarith
  by_cases hAe : A = ∅
  · subst hAe
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨LG0, hLG0⟩ := Finset.nonempty_iff_ne_empty.2 hAe
  set 𝓖 := A.image (coreOf D hS) with h𝓖def
  set gfix : Finset (GBranch S.tree) → ℕ := fun T => vineIncoh S (coreOf D hS LG0) T with hgfix_def
  have h𝓖 : ∀ f ∈ 𝓖, LFTwist.IsBranchPrelayering S f ∧ ∀ x, f x ≤ p := by
    intro f hf
    obtain ⟨LG, hLG, rfl⟩ := Finset.mem_image.1 hf
    obtain ⟨hc, hd, -⟩ := hA LG hLG
    refine ⟨?_, fun x => ?_⟩
    · rw [coreOf_eq D hS hd]
      exact LFTwist.inducedPrelayer_isBranchPrelayering LG D hS hd
    · rw [coreOf_eq D hS hd]; exact hc.2.2.1 _
  have hγ : ∀ f ∈ 𝓖, ∀ i, incoherencyIndex (f ∘ (stSt S σ Mk).M.ob)
      (ladderGroups ((ladderDataOf (stSt S σ Mk).G).upper i) ((ladderDataOf (stSt S σ Mk).G).lower i)) = γ i := by
    intro f hf i
    obtain ⟨LG, hLG, rfl⟩ := Finset.mem_image.1 hf
    exact (hA LG hLG).2.choose_spec.2 i
  have hgfix : ∀ f ∈ 𝓖, ∀ j, ∀ t ∈ Tss j, vineIncoh S f t.1 = gfix t.1 := by
    intro f hf j t ht
    obtain ⟨LG, hLG, rfl⟩ := Finset.mem_image.1 hf
    obtain ⟨k, rfl⟩ := List.mem_iff_get.1 ht
    exact hconst LG hLG LG0 hLG0 ⟨j, k⟩
  have hw := hmain p 𝓖 h𝓖 γ hγ gfix hgfix
  have hb1 := card_class_le_bond D hS p gs A (fun LG hLG => by
    obtain ⟨hc, hd, hinc, -⟩ := hA LG hLG
    exact ⟨hc.2.2, hc.1, hd, hinc⟩)
  have hE := E_leMk hS D p h1 h2 A gs (fun LG hLG => by
    obtain ⟨hc, hd, hinc, -⟩ := hA LG hLG
    exact ⟨hc, hd, hinc⟩) gfix
  have hYV : ∑ T ∈ (Finset.univ : Finset (TripIMk S σ Mk Tss)).image (fun i => (tauMk Tss i).1), gfix T ≤ V := by
    refine le_trans ?_ (hV LG0 hLG0)
    refine Finset.sum_le_sum_of_subset ?_
    intro T hT
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hT
    exact (Set.toFinite _).mem_toFinset.2 (tau_specMk h1 i).2.2.2.2
  have hrt := rootThings_leMk S hS σ Mk
  have hatoms : S.molecule.atoms = Finset.univ := rfl
  rw [hatoms] at hw
  have hEb := hE.trans (Nat.add_le_add (Nat.mul_le_mul_left 8 hYV) le_rfl)
  have hSg0 : 0 ≤ ∑ f ∈ 𝓖, (2 : ℝ) ^ (bondExp S.molecule Finset.univ f) :=
    Finset.sum_nonneg fun f _ => by positivity
  exact class_numerics hK0 hSg0 hb1 hw hEb hrt

open Classical in
/-- **The class bound.** -/
theorem class_bound : ∃ K0 : ℝ, 2 ≤ K0 ∧ ∀ {w : ℕ} (S : Garden w) (hS : S.IsPlain) (D : ReconstructionData S)
    (σ : Prescription S),
    ∃ Tss : Fin (unitBlocks S σ).length → List (Trip S),
      (∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredient S.molecule ((unitBlocks S σ).get j).atoms
          ((unitBlocks S σ).get j).upper ((unitBlocks S σ).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2) ∧
      (∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint) ∧
      ∀ (p : ℕ) (A : Finset (LayeredGarden w)) (gs : ReplacementSlot S → ℕ)
        (γ : {T // T ∈ (stSt S σ).G.molecule.maximalLadders} → ℕ) (V : ℕ)
        (hA : ∀ LG ∈ A, IsCanonGC (p + 1) LG ∧ ∃ hd : D.Decodes hS LG.garden, (∀ s, slotInc D hS LG s = gs s) ∧
          ∀ i, incoherencyIndex (coreOf D hS LG ∘ (stSt S σ).M.ob)
            (ladderGroups ((ladderDataOf (stSt S σ).G).upper i) ((ladderDataOf (stSt S σ).G).lower i)) = γ i)
        (hconst : ∀ LG ∈ A, ∀ LG' ∈ A, ∀ i : TripI S σ Tss,
          vineIncoh S (coreOf D hS LG) (tau Tss i).1 = vineIncoh S (coreOf D hS LG') (tau Tss i).1)
        (hV : ∀ LG ∈ A, ∑ T ∈ (Set.toFinite (unitIngredients S σ)).toFinset, vineIncoh S (coreOf D hS LG) T ≤ V),
      (A.card : ℝ) ≤ (2 : ℝ) ^ D.size * K0 ^ (4 * Fintype.card (GBranch S.tree)) *
        (K0 ^ (p + 1)) ^ (24 * ((stSt S σ).G.molecule.rho + (unitBlocks S σ).length) + 15 * ∑ s, gs s +
          ∑ i, γ i + 8 * V) :=
  let ⟨K0, hK0, h⟩ := class_boundMk
  ⟨K0, hK0, fun S hS D σ => h S hS D σ ∅⟩

end WaveTurbulence.ClassCount
