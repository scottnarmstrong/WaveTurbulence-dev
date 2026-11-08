/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.ClassBound
public import WaveTurbulence.Foundations.Stage1.ClassCount.KeyCount
import Mathlib.Tactic

/-!
# CLASSCOUNT: the classification data (σ-classes, keys) and their cardinalities

* the prescription `σ` enters the piece only through `unitBlocks S σ`, hence through the set of groups with `σ = SG`
  (at most `2^n` classes);
* the numbers of nonempty replacement slots, ingredient triples and ladders are bounded by `D.size`, `n`, `ρ`.
-/

@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.LayerCnt WaveTurbulence.Vine
  WaveTurbulence.Reg.Skeleton

theorem card_le_of_disjoint_nonempty {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (e : I → Finset V) (hne : ∀ i, (e i).Nonempty) (hd : ∀ i i', i ≠ i' → Disjoint (e i) (e i')) :
    Fintype.card I ≤ Fintype.card V := by
  refine Fintype.card_le_of_injective (fun i => (hne i).choose) ?_
  intro i i' h
  by_contra hne'
  have h' : (hne i).choose = (hne i').choose := h
  exact Finset.disjoint_left.1 (hd i i' hne') (hne i).choose_spec (by rw [h']; exact (hne i').choose_spec)

variable {w : ℕ}

theorem card_groupsFinset_le (S : Garden w) :
    (groupsFinset S).card ≤ Fintype.card (GBranch S.tree) := by
  classical
  have hM := Mole.garden_isMolecule S
  have hpart := partition_eq_maximalGroups (stage1Collection_isPartition hM)
  have hdisj : (maximalGroups S.molecule).Pairwise (fun T T' => Disjoint T T') := by
    have := (stage1Collection_isPartition hM).2.1
    rwa [hpart] at this
  have hne : ∀ T ∈ groupsFinset S, T.Nonempty := by
    intro T hT
    have hT' : T ∈ stage1Collection S.molecule := by
      rw [hpart]; exact mem_groupsFinset.1 hT
    exact Stage1.IsStage1Group.nonempty ((stage1Collection_isPartition hM).1 T hT')
  have := card_le_of_disjoint_nonempty (I := {T // T ∈ groupsFinset S}) (fun T => T.1)
    (fun T => hne T.1 T.2) (fun T T' h => hdisj (mem_groupsFinset.1 T.2) (mem_groupsFinset.1 T'.2)
      (fun h' => h (Subtype.ext h')))
  simpa using this

/-- B1b (Mk-general form of `unitBlocks_eq_of_filter_eq`). -/
theorem unitBlocks_eq_of_filter_eqMk (S : Garden w) (σ σ' : Prescription S)
    (h : (groupsFinset S).filter (fun T => σ T = Molecule.GapKind.SG) =
      (groupsFinset S).filter (fun T => σ' T = Molecule.GapKind.SG)) {Mk : Set (Stage1.CLVine _)} :
    unitBlocks (Mk := Mk) S σ = unitBlocks (Mk := Mk) S σ' := by
  classical
  have hsg : sgGroups S σ = sgGroups S σ' := by
    unfold sgGroups
    refine List.filter_congr fun T hT => ?_
    have hT' : T ∈ groupsFinset S := Finset.mem_toList.1 hT
    have : (T ∈ (groupsFinset S).filter (fun T => σ T = Molecule.GapKind.SG)) ↔
        (T ∈ (groupsFinset S).filter (fun T => σ' T = Molecule.GapKind.SG)) := by rw [h]
    simp only [Finset.mem_filter, hT', true_and] at this
    simpa using this
  unfold unitBlocks
  rw [hsg]

theorem unitBlocks_eq_of_filter_eq (S : Garden w) (σ σ' : Prescription S)
    (h : (groupsFinset S).filter (fun T => σ T = Molecule.GapKind.SG) =
      (groupsFinset S).filter (fun T => σ' T = Molecule.GapKind.SG)) :
    unitBlocks S σ = unitBlocks S σ' := unitBlocks_eq_of_filter_eqMk (Mk := ∅) S σ σ' h

theorem length_filter_eq_sum {ι : Type*} (L : List ι) (P : ι → Bool) :
    (L.filter P).length = (L.map (fun x => if P x then 1 else 0)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    cases h : P a <;> simp [h, ih] <;> omega

theorem incoherencyIndex_ladderGroups {α : Type*} (layer : α → ℕ) {m : ℕ} (u v : Fin (m + 1) → α) :
    incoherencyIndex layer (ladderGroups u v) = ∑ j : Fin (m + 1), if layer (u j) = layer (v j) then 0 else 1 := by
  classical
  unfold incoherencyIndex ladderGroups
  rw [length_filter_eq_sum, List.map_map, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp, GroupCoherent]
  by_cases h : layer (u j) = layer (v j)
  · simp [h]
  · simp only [h, if_false]
    have : ¬ (∀ x ∈ [u j, v j], ∀ y ∈ [u j, v j], layer x = layer y) := by
      intro hh; exact h (hh (u j) (by simp) (v j) (by simp))
    simp only [this, decide_false, if_false] ; simp

/-- B1b (Mk-general form of `gbar_decomp`). -/
theorem gbar_decompMk {R : ℕ} (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S} (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} :
    (stage1PieceOf (Mk := Mk) d hS LG hd σ).gbar = ∑ s, slotInc D hS LG s +
      ∑ T ∈ (Set.toFinite (unitIngredients (Mk := Mk) S σ)).toFinset, vineIncoh S (coreOf D hS LG) T +
      ∑ i : {T // T ∈ (stSt (Mk := Mk) S σ).G.molecule.maximalLadders},
        incoherencyIndex (coreOf D hS LG ∘ (stSt (Mk := Mk) S σ).M.ob)
          (ladderGroups ((ladderDataOf (stSt (Mk := Mk) S σ).G).upper i) ((ladderDataOf (stSt (Mk := Mk) S σ).G).lower i)) := by
  unfold LGSpine.Stage1PieceD.gbar LGSpine.Stage1PieceD.gsk LGSpine.Stage1PieceD.gsb
  simp only [stage1PieceOf, gskOf]
  rw [gregOf_eq_sum D hS hd, ← coreOf_eq D hS hd]
  unfold LGSpine.SourceMaximalLadderData.totalIncoherency
  have : ∀ i : {T // T ∈ (stSt (Mk := Mk) S σ).G.molecule.maximalLadders},
      LGSpine.sourceLadderIncoherency (stSt (Mk := Mk) S σ).G ((stSt (Mk := Mk) S σ).layer (coreOf D hS LG))
        ((ladderDataOf (stSt (Mk := Mk) S σ).G).upper i) ((ladderDataOf (stSt (Mk := Mk) S σ).G).lower i) =
      incoherencyIndex (coreOf D hS LG ∘ (stSt (Mk := Mk) S σ).M.ob)
          (ladderGroups ((ladderDataOf (stSt (Mk := Mk) S σ).G).upper i) ((ladderDataOf (stSt (Mk := Mk) S σ).G).lower i)) := by
    intro i
    rw [incoherencyIndex_ladderGroups]
    rfl
  rw [Finset.sum_congr rfl fun i _ => this i]

/-- **`ḡ` of a piece is `Σ gs + (vine incoherencies) + Σ γ`.** -/
theorem gbar_decomp {R : ℕ} (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S} (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) :
    (stage1PieceOf d hS LG hd σ).gbar = ∑ s, slotInc D hS LG s +
      ∑ T ∈ (Set.toFinite (unitIngredients S σ)).toFinset, vineIncoh S (coreOf D hS LG) T +
      ∑ i : {T // T ∈ (stSt S σ).G.molecule.maximalLadders},
        incoherencyIndex (coreOf D hS LG ∘ (stSt S σ).M.ob)
          (ladderGroups ((ladderDataOf (stSt S σ).G).upper i) ((ladderDataOf (stSt S σ).G).lower i)) := gbar_decompMk (Mk := ∅) d hS LG hd σ

/-- B1b (Mk-general form of `stSt_eq_of_unitBlocks_eq`). -/
theorem stSt_eq_of_unitBlocks_eqMk (S : Garden w) (σ σ' : Prescription S)
    {Mk : Set (Stage1.CLVine _)} (h : unitBlocks (Mk := Mk) S σ = unitBlocks (Mk := Mk) S σ') : stSt (Mk := Mk) S σ = stSt (Mk := Mk) S σ' := by
  unfold stSt; rw [h]

theorem stSt_eq_of_unitBlocks_eq (S : Garden w) (σ σ' : Prescription S)
    (h : unitBlocks S σ = unitBlocks S σ') : stSt S σ = stSt S σ' := stSt_eq_of_unitBlocks_eqMk (Mk := ∅) S σ σ' h

/-- B1b (Mk-general form of `unitIngredients_eq_of_unitBlocks_eq`). -/
theorem unitIngredients_eq_of_unitBlocks_eqMk (S : Garden w) (σ σ' : Prescription S)
    {Mk : Set (Stage1.CLVine _)} (h : unitBlocks (Mk := Mk) S σ = unitBlocks (Mk := Mk) S σ') : unitIngredients (Mk := Mk) S σ = unitIngredients (Mk := Mk) S σ' := by
  unfold unitIngredients; rw [h]

theorem unitIngredients_eq_of_unitBlocks_eq (S : Garden w) (σ σ' : Prescription S)
    (h : unitBlocks S σ = unitBlocks S σ') : unitIngredients S σ = unitIngredients S σ' := unitIngredients_eq_of_unitBlocks_eqMk (Mk := ∅) S σ σ' h

/-- The `ḡ`-decomposition as a function of the splice state and the ingredient set. -/
noncomputable def gbarRHS {R : ℕ} {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (st : SpState S) (ing : Finset (Finset (GBranch S.tree))) : ℕ :=
  ∑ s, slotInc D hS LG s + ∑ T ∈ ing, vineIncoh S (coreOf D hS LG) T +
    ∑ i : {T // T ∈ st.G.molecule.maximalLadders},
      incoherencyIndex (coreOf D hS LG ∘ st.M.ob)
        (ladderGroups ((ladderDataOf st.G).upper i) ((ladderDataOf st.G).lower i))

/-- B2d: `ḡ` of a piece at a marked set, as a function of the splice state and the ingredient set. -/
theorem gbar_eq_gbarRHSMk {R : ℕ} (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S} (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) (Mk : Set (Stage1.CLVine S)) :
    (stage1PieceOf d hS LG hd σ Mk).gbar =
      gbarRHS D hS LG (stSt S σ Mk) (Set.toFinite (unitIngredients S σ Mk)).toFinset :=
  gbar_decompMk (Mk := Mk) d hS LG hd σ

theorem gbar_eq_gbarRHS {R : ℕ} (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S} (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) :
    (stage1PieceOf d hS LG hd σ).gbar =
      gbarRHS D hS LG (stSt S σ) (Set.toFinite (unitIngredients S σ)).toFinset :=
  gbar_eq_gbarRHSMk d hS LG hd σ ∅

theorem rbarOf_eqMk (S : Garden (2 * w)) (σ : Prescription S) (Mk : Set (Stage1.CLVine S)) :
    rbarOfMk S σ Mk = (stSt S σ Mk).G.molecule.rho + (stSt S σ Mk).hinges.card := rfl

theorem rbarOf_eq (S : Garden (2 * w)) (σ : Prescription S) :
    rbarOf S σ = (stSt S σ).G.molecule.rho + (stSt S σ).hinges.card := rbarOf_eqMk S σ ∅

/-- B2d: the piece data `(ḡ, ρ̄)` depend on the prescription and the marked set only through the unit list. -/
theorem gbar_rbar_eq_of_unitBlocks_eqMk {R : ℕ} (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ σ' : Prescription S)
    (Mk Mk' : Set (Stage1.CLVine S)) (h : unitBlocks S σ Mk = unitBlocks S σ' Mk') :
    (stage1PieceOf d hS LG hd σ Mk).gbar = (stage1PieceOf d hS LG hd σ' Mk').gbar ∧
      rbarOfMk S σ Mk = rbarOfMk S σ' Mk' := by
  have hst : stSt S σ Mk = stSt S σ' Mk' := by unfold stSt; rw [h]
  have hing : unitIngredients S σ Mk = unitIngredients S σ' Mk' := by unfold unitIngredients; rw [h]
  have hfin : (Set.toFinite (unitIngredients S σ Mk)).toFinset =
      (Set.toFinite (unitIngredients S σ' Mk')).toFinset := by
    ext T; simp [hing]
  refine ⟨?_, ?_⟩
  · rw [gbar_eq_gbarRHSMk, gbar_eq_gbarRHSMk, hfin, hst]
  · rw [rbarOf_eqMk, rbarOf_eqMk, hst]

theorem gbar_rbar_eq_of_unitBlocks_eq {R : ℕ} (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ σ' : Prescription S)
    (h : unitBlocks S σ = unitBlocks S σ') :
    (stage1PieceOf d hS LG hd σ).gbar = (stage1PieceOf d hS LG hd σ').gbar ∧ rbarOf S σ = rbarOf S σ' := by
  have hst := stSt_eq_of_unitBlocks_eq S σ σ' h
  have hing := unitIngredients_eq_of_unitBlocks_eq S σ σ' h
  have hfin : (Set.toFinite (unitIngredients S σ)).toFinset = (Set.toFinite (unitIngredients S σ')).toFinset := by
    ext T; simp [hing]
  refine ⟨?_, ?_⟩
  · rw [gbar_eq_gbarRHS, gbar_eq_gbarRHS, hfin]
    rw [hst]
  · rw [rbarOf_eq, rbarOf_eq, hst]

/-- B1b (Mk-general form of `length_le_hinges`). -/
theorem length_le_hingesMk (S : Garden w) (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} :
    (unitBlocks (Mk := Mk) S σ).length ≤ (stSt (Mk := Mk) S σ).hinges.card := by
  classical
  have hM := Mole.garden_isMolecule S
  have hpair := List.pairwise_iff_get.mp (unitBlocks_pairwiseMk (Mk := Mk) hM σ)
  have hrange : ∀ j : Fin (unitBlocks (Mk := Mk) S σ).length, ∃ c, (stSt (Mk := Mk) S σ).M.ob c = ((unitBlocks (Mk := Mk) S σ).get j).upper := by
    intro j
    rw [(stSt (Mk := Mk) S σ).M.ob_range]
    right
    rw [stSt_cls_memMk (Mk := Mk) hM σ (List.get_mem _ _) ((unitBlocks (Mk := Mk) S σ).get j).isBlock.2.1]
  choose c hc using hrange
  have hmem : ∀ j, c j ∈ (stSt (Mk := Mk) S σ).hinges := by
    intro j
    rw [SpState.mem_hinges, hc j, stSt_cls_memMk (Mk := Mk) hM σ (List.get_mem _ _) ((unitBlocks (Mk := Mk) S σ).get j).isBlock.2.1]
    simp
  calc (unitBlocks (Mk := Mk) S σ).length = Fintype.card (Fin (unitBlocks (Mk := Mk) S σ).length) := (Fintype.card_fin _).symm
    _ ≤ (stSt (Mk := Mk) S σ).hinges.card := by
        refine Finset.card_le_card_of_injOn c (fun j _ => hmem j) ?_
        intro j _ j' _ h
        by_contra hne
        have hd : Disjoint ((unitBlocks (Mk := Mk) S σ).get j).atoms ((unitBlocks (Mk := Mk) S σ).get j').atoms := by
          rcases lt_or_gt_of_ne hne with h' | h'
          · exact hpair j j' h'
          · exact (hpair j' j h').symm
        have hu := congrArg (stSt (Mk := Mk) S σ).M.ob h
        rw [hc j, hc j'] at hu
        exact Finset.disjoint_left.1 hd ((unitBlocks (Mk := Mk) S σ).get j).isBlock.2.1 (hu ▸ ((unitBlocks (Mk := Mk) S σ).get j').isBlock.2.1)

theorem length_le_hinges (S : Garden w) (σ : Prescription S) :
    (unitBlocks S σ).length ≤ (stSt S σ).hinges.card := length_le_hingesMk (Mk := ∅) S σ

/-- B2d: `ρ_sb + #units ≤ ρ̄` at any marked set. -/
theorem rho_add_length_le_rbarOfMk (S : Garden (2 * w)) (σ : Prescription S) (Mk : Set (Stage1.CLVine S)) :
    (stSt S σ Mk).G.molecule.rho + (unitBlocks S σ Mk).length ≤ rbarOfMk S σ Mk := by
  rw [rbarOf_eqMk]
  have := length_le_hingesMk (Mk := Mk) S σ
  omega

theorem rho_add_length_le_rbarOf (S : Garden (2 * w)) (σ : Prescription S) :
    (stSt S σ).G.molecule.rho + (unitBlocks S σ).length ≤ rbarOf S σ :=
  rho_add_length_le_rbarOfMk S σ ∅

theorem card_ladders_le_rho (G : Garden w) :
    Fintype.card {T // T ∈ G.molecule.maximalLadders} ≤ G.molecule.rho := by
  classical
  rw [Fintype.card_coe]
  unfold Molecule.rho Molecule.numLadders
  omega

/-- The size of a replacement slot. -/
def slotSize {S : Garden w} (D : ReconstructionData S) : ReplacementSlot S → ℕ
  | .inl pr => (D.couple pr).size
  | .inr b => (D.tree b).size

theorem sum_slotSize {S : Garden w} (D : ReconstructionData S) : ∑ s, slotSize D s = D.size := by
  rw [Fintype.sum_sum_type, ReconstructionData.size]
  simp only [slotSize, add_comm]

theorem card_slots_nonempty_le {S : Garden w} (D : ReconstructionData S) :
    ((Finset.univ : Finset (ReplacementSlot S)).filter (fun s => slotSize D s ≠ 0)).card ≤ D.size := by
  classical
  calc _ = ∑ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => slotSize D s ≠ 0), 1 := by simp
    _ ≤ ∑ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => slotSize D s ≠ 0), slotSize D s :=
        Finset.sum_le_sum fun s hs => Nat.one_le_iff_ne_zero.2 (Finset.mem_filter.1 hs).2
    _ ≤ ∑ s, slotSize D s := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = D.size := sum_slotSize D

theorem slotInc_eq_zero_of_size {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (LG : LayeredGarden w)
    (s : ReplacementSlot S) (h : slotSize D s = 0) : slotInc D hS LG s = 0 := by
  cases s with
  | inl pr =>
    have := Links.couple_linksAt_length (D.couple pr) (cplA D hS pr) (cplB D hS pr)
    have h0 : ((D.couple pr).linksAt (cplA D hS pr) (cplB D hS pr)).length = 0 := by
      have : (D.couple pr).size = 0 := h
      omega
    show Links.incohCount LG ((D.couple pr).linksAt (cplA D hS pr) (cplB D hS pr)) = 0
    rw [List.length_eq_zero_iff.1 h0]
    rfl
  | inr b =>
    have := Links.chain_linksAt_length (D.tree b) (nodeSign S.sig b.1) (treeA D b)
    have h0 : ((D.tree b).linksAt (nodeSign S.sig b.1) (treeA D b)).length = 0 := by
      have : (D.tree b).size = 0 := h
      omega
    show Links.incohCount LG ((D.tree b).linksAt (nodeSign S.sig b.1) (treeA D b)) = 0
    rw [List.length_eq_zero_iff.1 h0]
    rfl

/-- B2d: the number of ingredient triples is at most the number of atoms (any marked set). -/
theorem card_tripI_leMk {S : Garden w} {σ : Prescription S} {Mk : Set (Stage1.CLVine S)} {Tss : Fin (unitBlocks S σ Mk).length → List (Trip S)}
    (h1 : ∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredient S.molecule ((unitBlocks S σ Mk).get j).atoms
          ((unitBlocks S σ Mk).get j).upper ((unitBlocks S σ Mk).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2)
    (h2 : ∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint) :
    Fintype.card (TripIMk S σ Mk Tss) ≤ Fintype.card (GBranch S.tree) :=
  card_le_of_disjoint_nonempty (fun i : TripIMk S σ Mk Tss => (tauMk Tss i).1.erase (tauMk Tss i).2.1)
    (fun i => tau_nonemptyMk h1 i) (fun i i' hne => tau_disjointMk h1 h2 hne)

theorem card_tripI_le {S : Garden w} {σ : Prescription S} {Tss : Fin (unitBlocks S σ).length → List (Trip S)}
    (h1 : ∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredient S.molecule ((unitBlocks S σ).get j).atoms
          ((unitBlocks S σ).get j).upper ((unitBlocks S σ).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2)
    (h2 : ∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint) :
    Fintype.card (TripI S σ Tss) ≤ Fintype.card (GBranch S.tree) :=
  card_tripI_leMk (Mk := ∅) h1 h2

end WaveTurbulence.ClassCount
