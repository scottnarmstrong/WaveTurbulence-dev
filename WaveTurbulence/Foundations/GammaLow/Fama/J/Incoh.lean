/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Code.Pieces
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.Discharge
public import WaveTurbulence.Foundations.Vine.A.VineIngredientCarrier
public import WaveTurbulence.Foundations.Stage1.Represents.RepCnt1
import Mathlib.Tactic
/-! # The vine incoherency of the spliced units is at most `Σ (|u| − 1)` (packet L5a, item J)

Main's `Represents.sum_vineIncoh_le_units(Mk)` (`Stage1/Represents/RepCnt1.lean`) bounds the total incoherency index
of the ingredients of the spliced units by `Σ_u (|u| − 1)`, through main's chain assemblies and drawn realizations
(`RepVE1`, `RepVE2`, `RepUG15`). Over `𝒱_γ` the same bound is proved directly:
* every member `T` of `𝒱_γ` has `vineIncoh T + 1 ≤ |T|` (bad vines: main's `realized_two_mul_add_two_le`; T-vines: the
  D11 pieces are disjoint nonempty subsets of the interior, so at most `|T| − 2` of them are incoherent);
* the ingredients of a unit `u` all lie on one spine of `u` (`isIngredient_vc`, uniqueness of spines), and along a
  spine `Σ (|T| − 1) + 1 = |u|`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Fama
open Finset WaveTurbulence.GammaLow.FinalCount WaveTurbulence.RedSplice

section Spine
variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {γ : ℝ}

/-- Along a spine, the atom counts of the ingredients telescope: `Σ (|T| − 1) + 1 = |U|`. -/
theorem Spine.sum_card {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (h : Spine γ M L U a b) :
    (L.map fun t => t.1.card - 1).sum + 1 = U.card := by
  induction h with
  | @one T a b hv =>
    have h1 : 1 ≤ T.card := card_pos.mpr ⟨a, (Src.isBlock_of_isSomeVine hv).2.1⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    omega
  | @snoc L U T a b c _ hv hi _ ih =>
    have hbT : b ∈ T := (Src.isBlock_of_isSomeVine hv).2.1
    have h1 : 1 ≤ T.card := card_pos.mpr ⟨b, hbT⟩
    have h2 := card_union_add_card_inter U T
    rw [hi, card_singleton] at h2
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    omega

/-- The pieces of an atom set with two distinct joints in it number at most `|S| − 2`. -/
theorem card_pieces_le (S : Finset V) (j₁ j₂ : V) :
    (M.pieces S j₁ j₂).card ≤ ((S.erase j₁).erase j₂).card := by
  classical
  have hne : ∀ P ∈ M.pieces S j₁ j₂, P.Nonempty := fun P hP => by
    obtain ⟨u, hu, h⟩ := (ClassCount.mem_pieces_iff M).mp hP
    exact ⟨u, (h u).mpr ⟨hu, ClassCount.samePiece_refl M S u⟩⟩
  refine card_le_card_of_injOn (fun P => if h : P.Nonempty then h.choose else j₁) ?_ ?_
  · intro P hP
    have hP' : P ∈ M.pieces S j₁ j₂ := hP
    simp only [dif_pos (hne P hP')]
    exact ClassCount.pieces_subset M hP' (hne P hP').choose_spec
  · intro P hP Q hQ h
    have hP' : P ∈ M.pieces S j₁ j₂ := hP
    have hQ' : Q ∈ M.pieces S j₁ j₂ := hQ
    simp only [dif_pos (hne P hP'), dif_pos (hne Q hQ')] at h
    exact ClassCount.piece_eq_of_mem M hP' hQ' (hne P hP').choose_spec (h ▸ (hne Q hQ').choose_spec)

/-- A sum over the distinct entries of a list is at most the sum over the list. -/
theorem sum_toFinset_le_list_sum {α : Type} [DecidableEq α] (l : List α) (f : α → ℕ) :
    ∑ x ∈ l.toFinset, f x ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.toFinset_cons, List.map_cons, List.sum_cons]
    by_cases ha : a ∈ l.toFinset
    · rw [insert_eq_of_mem ha]; omega
    · rw [sum_insert ha]; omega

/-- A sum over a union is at most the sum of the sums (natural-number values). -/
theorem sum_biUnion_le_nat {ι α : Type} [DecidableEq ι] [DecidableEq α] (s : Finset ι) (t : ι → Finset α)
    (f : α → ℕ) : ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [biUnion_insert, sum_insert has]
    calc ∑ x ∈ t a ∪ s.biUnion t, f x ≤ ∑ x ∈ t a, f x + ∑ x ∈ s.biUnion t, f x := by
          rw [← sum_union_inter]; omega
      _ ≤ _ := by omega

end Spine

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)]

/-- **The incoherency index of a member of `𝒱_γ` is at most `|T| − 1`.** -/
theorem vineIncoh_add_one_le (G : Garden w) (layer0 : GBranch G.tree → ℕ) {T : Finset (GBranch G.tree)}
    {p q : GBranch G.tree} (hT : Src.IsSomeVine γ G.molecule T p q) : vineIncoh γ G layer0 T + 1 ≤ T.card := by
  classical
  have hB := Src.isBlock_of_isSomeVine hT
  have h2 : 2 ≤ T.card := by
    have := card_le_card (show ({p, q} : Finset (GBranch G.tree)) ⊆ T by
      intro v hv; rcases mem_insert.mp hv with rfl | hv
      · exact hB.2.1
      · rw [mem_singleton.mp hv]; exact hB.2.2.1)
    rwa [card_pair hB.2.2.2.1] at this
  unfold vineIncoh
  split_ifs with h h'
  · have := Represents.realized_two_mul_add_two_le
      (Classical.choice (Vine.isVine_iff_realization.mp h.choose_spec.choose_spec.choose_spec.2).2) layer0
    omega
  · have hTB := h'.choose_spec.choose_spec.1
    have hl : Vine.incoherencyIndex layer0
        ((G.molecule.tvineGroups T h'.choose h'.choose_spec.choose).toList.map Finset.toList) ≤
        (G.molecule.tvineGroups T h'.choose h'.choose_spec.choose).card := by
      unfold Vine.incoherencyIndex
      refine (List.length_filter_le _ _).trans ?_
      simp
    have hc : (G.molecule.tvineGroups T h'.choose h'.choose_spec.choose).card ≤
        ((T.erase h'.choose).erase h'.choose_spec.choose).card :=
      card_pieces_le (M := G.molecule) T h'.choose h'.choose_spec.choose
    have he : ((T.erase h'.choose).erase h'.choose_spec.choose).card + 2 = T.card := by
      have h1 : h'.choose ∈ T := hTB.2.1
      have h2' : h'.choose_spec.choose ∈ T.erase h'.choose := mem_erase.mpr ⟨hTB.2.2.2.1.symm, hTB.2.2.1⟩
      rw [card_erase_of_mem h2', card_erase_of_mem h1]
      have : 2 ≤ T.card := h2
      omega
    omega
  · omega

variable [Fact TVineIsoInvariant] [Fact Famc.ClassCount.TVineStructInputs]

/-- **Main's `sum_vineIncoh_le_unitsMk` over `𝒱_γ`:** the total incoherency index of the ingredients of the spliced
units is at most `Σ_u (|u| − 1)`. -/
theorem sum_vineIncoh_le_unitsMk {S : Garden w} (hM : S.molecule.IsMolecule) (σ : Prescription S)
    (layer0 : GBranch S.tree → ℕ) {Mk : Set (CLVineG γ S)} :
    ∑ T ∈ (Set.toFinite (unitIngredients γ S σ Mk)).toFinset, vineIncoh γ S layer0 T ≤
      ((unitBlocks γ S σ Mk).map fun u => u.atoms.card - 1).sum := by
  classical
  -- a spine for every unit
  have hsp : ∀ u ∈ unitBlocks γ S σ Mk, ∃ L, Spine γ S.molecule L u.atoms u.upper u.lower := by
    intro u hu
    obtain ⟨n, hc⟩ := Famc.VineA.unitBlocks_chainMk hu
    exact Spine.of_chain hc
  choose! Lof hLof using hsp
  let ing : CLBlock S → Finset (Finset (GBranch S.tree)) := fun u => ((Lof u).map fun t => t.1).toFinset
  -- every unit ingredient is on the spine of its unit
  have hcov : (Set.toFinite (unitIngredients γ S σ Mk)).toFinset ⊆
      ((unitBlocks γ S σ Mk).toFinset).biUnion ing := by
    intro T hT
    obtain ⟨u, hu, x, y, n, p, q, hi⟩ := (Set.Finite.mem_toFinset _).mp hT
    have hc := (chainIngredientG_spec hi).1
    have hj : ({x, y} : Finset (GBranch S.tree)) = {u.upper, u.lower} := by
      have hd := Mole.block_joint_degrees S.molecule u.isBlock
      exact Vine.joints_eq_of_two_low_degrees S.molecule (subset_refl _) u.isBlock.2.1 u.isBlock.2.2.1
        u.isBlock.2.2.2.1 (chain_joints_ne hc) (by omega) (by omega) (chain_interior_degree S.molecule hM hc)
    have hBxy := Mole.block_transport_joints S.molecule hj u.isBlock
    obtain ⟨p', q', hm | hm⟩ := isIngredient_vc hM u.isBlock (hLof u hu) (Or.inl ⟨x, y, n, p, q, hBxy, hi⟩)
    · exact mem_biUnion.mpr ⟨u, List.mem_toFinset.mpr hu, List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, hm, rfl⟩)⟩
    · exact mem_biUnion.mpr ⟨u, List.mem_toFinset.mpr hu, List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, hm, rfl⟩)⟩
  -- the per-vine bound on each spine
  have hper : ∀ u ∈ unitBlocks γ S σ Mk, ∑ T ∈ ing u, vineIncoh γ S layer0 T ≤ u.atoms.card - 1 := by
    intro u hu
    have hs := hLof u hu
    have hsum := Spine.sum_card hs
    calc ∑ T ∈ ing u, vineIncoh γ S layer0 T ≤ ∑ T ∈ ing u, (T.card - 1) := by
          refine sum_le_sum fun T hT => ?_
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hT)
          have hv := (hs.mem_vine ht).1
          have := vineIncoh_add_one_le S layer0 hv
          omega
      _ ≤ ((Lof u).map fun t => t.1.card - 1).sum := by
          have e : ((Lof u).map fun t => t.1.card - 1) = (((Lof u).map fun t => t.1).map fun T => T.card - 1) := by
            rw [List.map_map]; rfl
          rw [e]
          exact sum_toFinset_le_list_sum _ _
      _ = u.atoms.card - 1 := by omega
  calc _ ≤ ∑ T ∈ ((unitBlocks γ S σ Mk).toFinset).biUnion ing, vineIncoh γ S layer0 T :=
        sum_le_sum_of_subset hcov
    _ ≤ ∑ u ∈ (unitBlocks γ S σ Mk).toFinset, ∑ T ∈ ing u, vineIncoh γ S layer0 T := sum_biUnion_le_nat _ _ _
    _ ≤ ∑ u ∈ (unitBlocks γ S σ Mk).toFinset, (u.atoms.card - 1) :=
        sum_le_sum fun u hu => hper u (List.mem_toFinset.mp hu)
    _ ≤ ((unitBlocks γ S σ Mk).map fun u => u.atoms.card - 1).sum := sum_toFinset_le_list_sum _ _

/-- The unmarked form (main's `sum_vineIncoh_le_units`). -/
theorem sum_vineIncoh_le_units {S : Garden w} (hM : S.molecule.IsMolecule) (σ : Prescription S)
    (layer0 : GBranch S.tree → ℕ) :
    ∑ T ∈ (Set.toFinite (unitIngredients γ S σ)).toFinset, vineIncoh γ S layer0 T ≤
      ((unitBlocks γ S σ).map fun u => u.atoms.card - 1).sum :=
  sum_vineIncoh_le_unitsMk (Mk := ∅) hM σ layer0

end WaveTurbulence.GammaLow.Fama
