/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepCnt1
import Mathlib.Tactic

/-!
# S2 REPRESENTS, `Stage1Counts` item 3, part 2: the order of `G_sb` and the number of hinges

For the splice `stSt S σ` of the (pairwise disjoint) units `unitBlocks S σ` of a molecule garden:
`n_sb + |A| = n_sk + #hinges` where `A` is the set of merged atoms (`|A| = Σ_u |u.atoms|`), and `#hinges ≤ #units`.
Consequently `n_sb + #hinges ≤ n_sk` and `n_sb + Σ_u (|u.atoms| - 1) ≤ n_sk`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset TTree WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole

variable {w : ℕ} {S : Garden w}

theorem card_union_blocks (l : List (CLBlock S)) (hd : l.Pairwise fun u u' => Disjoint u.atoms u'.atoms) :
    ((Finset.univ : Finset (GBranch S.tree)).filter fun v => ∃ u ∈ l, v ∈ u.atoms).card =
      (l.map fun u => u.atoms.card).sum := by
  classical
  induction l with
  | nil => simp
  | cons u l ih =>
    have hd' := List.pairwise_cons.mp hd
    have e : ((Finset.univ : Finset (GBranch S.tree)).filter fun v => ∃ u' ∈ u :: l, v ∈ u'.atoms) =
        u.atoms ∪ ((Finset.univ : Finset (GBranch S.tree)).filter fun v => ∃ u' ∈ l, v ∈ u'.atoms) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons, Finset.mem_union]
      constructor
      · rintro ⟨u', rfl | h, hv⟩
        · exact Or.inl hv
        · exact Or.inr ⟨u', h, hv⟩
      · rintro (h | ⟨u', h, hv⟩)
        · exact ⟨u, Or.inl rfl, h⟩
        · exact ⟨u', Or.inr h, hv⟩
    rw [e, Finset.card_union_of_disjoint, ih hd'.2, List.map_cons, List.sum_cons]
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv'
    obtain ⟨u', hu', hv2⟩ := hv'
    exact Finset.disjoint_left.mp (hd'.1 u' hu') hv hv2

theorem two_le_card_atoms (hM : S.molecule.IsMolecule) (u : CLBlock S) : 2 ≤ u.atoms.card := by
  obtain ⟨-, h1, h2, h3, -⟩ := u.isBlock
  have : ({u.upper, u.lower} : Finset (GBranch S.tree)) ⊆ u.atoms := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have h4 := Finset.card_le_card this
  rwa [Finset.card_pair h3] at h4

section Counts
variable (hM : S.molecule.IsMolecule) (σ : Prescription S)
include hM

/-- The merged atoms of the splice. -/
noncomputable def mergedAtoms (Mk : Set (Stage1.CLVine S) := ∅) : Finset (GBranch S.tree) :=
  by classical exact Finset.univ.filter fun v => (stSt S σ Mk).cls v ≠ none

/-- The crown atoms of the splice. -/
noncomputable def crownAtoms (Mk : Set (Stage1.CLVine S) := ∅) : Finset (GBranch S.tree) :=
  by classical exact Finset.univ.filter fun v => (stSt S σ Mk).cls v = some v

/-- B1b (Mk-general form of `card_mergedAtoms`). -/
theorem card_mergedAtomsMk {Mk : Set (Stage1.CLVine _)} : (mergedAtoms (Mk := Mk) σ).card = ((unitBlocks (Mk := Mk) S σ).map fun u => u.atoms.card).sum := by
  classical
  rw [← card_union_blocks _ (unitBlocks_pairwiseMk (Mk := Mk) hM σ)]
  congr 1
  ext v
  simp only [mergedAtoms, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    exact h (stSt_cls_noneMk (Mk := Mk) hM σ hn)
  · rintro ⟨u, hu, hv⟩
    rw [stSt_cls_memMk (Mk := Mk) hM σ hu hv]; simp

theorem card_mergedAtoms : (mergedAtoms σ).card = ((unitBlocks S σ).map fun u => u.atoms.card).sum := card_mergedAtomsMk (Mk := ∅) hM σ

theorem crownAtoms_subset : crownAtoms σ ⊆ mergedAtoms σ := by
  classical
  intro v hv
  simp only [crownAtoms, mergedAtoms, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  rw [hv]; simp

/-- B1b (Mk-general form of `card_crownAtoms_le`). -/
theorem card_crownAtoms_leMk {Mk : Set (Stage1.CLVine _)} : (crownAtoms (Mk := Mk) σ).card ≤ (unitBlocks (Mk := Mk) S σ).length := by
  classical
  have : crownAtoms (Mk := Mk) σ ⊆ ((unitBlocks (Mk := Mk) S σ).map fun u => u.upper).toFinset := by
    intro v hv
    simp only [crownAtoms, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have hn : (stSt (Mk := Mk) S σ).cls v ≠ none := by rw [hv]; simp
    have : ∃ u ∈ unitBlocks (Mk := Mk) S σ, v ∈ u.atoms := by
      by_contra h
      push Not at h
      exact hn (stSt_cls_noneMk (Mk := Mk) hM σ h)
    obtain ⟨u, hu, hvu⟩ := this
    rw [stSt_cls_memMk (Mk := Mk) hM σ hu hvu] at hv
    have : u.upper = v := Option.some.inj hv
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨u, hu, this⟩)
  refine (Finset.card_le_card this).trans ?_
  exact (List.toFinset_card_le _).trans (by simp)

theorem card_crownAtoms_le : (crownAtoms σ).card ≤ (unitBlocks S σ).length := card_crownAtoms_leMk (Mk := ∅) hM σ

/-- B1b (Mk-general form of `two_mul_units_le`). -/
theorem two_mul_units_leMk {Mk : Set (Stage1.CLVine _)} : 2 * (unitBlocks (Mk := Mk) S σ).length ≤ (mergedAtoms (Mk := Mk) σ).card := by
  rw [card_mergedAtomsMk (Mk := Mk) hM σ]
  have : ∀ l : List (CLBlock S), (∀ u ∈ l, 2 ≤ u.atoms.card) → 2 * l.length ≤ (l.map fun u => u.atoms.card).sum := by
    intro l
    induction l with
    | nil => simp
    | cons u l ih =>
      intro h
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have := ih fun v hv => h v (List.mem_cons_of_mem _ hv)
      have := h u (List.mem_cons_self ..)
      omega
  exact this _ fun u _ => two_le_card_atoms hM u

theorem two_mul_units_le : 2 * (unitBlocks S σ).length ≤ (mergedAtoms σ).card := two_mul_units_leMk (Mk := ∅) hM σ

/-- B1b (Mk-general form of `order_add_merged`). -/
theorem order_add_mergedMk {Mk : Set (Stage1.CLVine _)} :
    (stSt (Mk := Mk) S σ).G.order + (mergedAtoms (Mk := Mk) σ).card = S.order + (crownAtoms (Mk := Mk) σ).card := by
  classical
  set st := stSt (Mk := Mk) S σ
  have hord : st.G.order = (Finset.univ.filter fun v : GBranch S.tree => st.cls v = none ∨ st.cls v = some v).card := by
    rw [Garden_order_eq_card]
    rw [← Finset.card_univ, ← Finset.card_image_of_injective _ st.M.ob_inj]
    congr 1
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    exact st.M.ob_range v
  have hS : S.order = (Finset.univ.filter fun v : GBranch S.tree => st.cls v = none).card + (mergedAtoms (Mk := Mk) σ).card := by
    rw [Garden_order_eq_card, ← Finset.card_univ]
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (GBranch S.tree))) (fun v => st.cls v = none)
    rw [← this]
    congr 2
  have hsplit : (Finset.univ.filter fun v : GBranch S.tree => st.cls v = none ∨ st.cls v = some v) =
      (Finset.univ.filter fun v : GBranch S.tree => st.cls v = none) ∪ crownAtoms (Mk := Mk) σ := by
    ext v
    simp [crownAtoms, st]
  have hdisj : Disjoint (Finset.univ.filter fun v : GBranch S.tree => st.cls v = none) (crownAtoms (Mk := Mk) σ) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [crownAtoms, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1] at h2; simp at h2
  rw [hord, hsplit, Finset.card_union_of_disjoint hdisj]
  omega

theorem order_add_merged :
    (stSt S σ).G.order + (mergedAtoms σ).card = S.order + (crownAtoms σ).card := order_add_mergedMk (Mk := ∅) hM σ

/-- B1b (Mk-general form of `card_hinges_eq`). -/
theorem card_hinges_eqMk {Mk : Set (Stage1.CLVine _)} : (stSt (Mk := Mk) S σ).hinges.card = (crownAtoms (Mk := Mk) σ).card := by
  classical
  set st := stSt (Mk := Mk) S σ
  unfold SpState.hinges
  rw [← Finset.card_image_of_injective _ st.M.ob_inj]
  congr 1
  ext v
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, crownAtoms]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rcases (st.M.ob_range (st.M.ob c)).mp ⟨c, rfl⟩ with h | h
    · exact absurd h hc
    · exact h
  · intro h
    have hr : ∃ c, st.M.ob c = v := (st.M.ob_range v).mpr (Or.inr h)
    obtain ⟨c, hc⟩ := hr
    exact ⟨c, by rw [hc, h]; simp, hc⟩

theorem card_hinges_eq : (stSt S σ).hinges.card = (crownAtoms σ).card := card_hinges_eqMk (Mk := ∅) hM σ

/-- B1b (Mk-general form of `order_add_hinges_le`). -/
theorem order_add_hinges_leMk {Mk : Set (Stage1.CLVine _)} : (stSt (Mk := Mk) S σ).G.order + (stSt (Mk := Mk) S σ).hinges.card ≤ S.order := by
  have h1 := order_add_mergedMk (Mk := Mk) hM σ
  have h2 := card_hinges_eqMk (Mk := Mk) hM σ
  have h3 := card_crownAtoms_leMk (Mk := Mk) hM σ
  have h4 := two_mul_units_leMk (Mk := Mk) hM σ
  omega

/-- `n_sb + #hinges ≤ n_sk`. -/
theorem order_add_hinges_le : (stSt S σ).G.order + (stSt S σ).hinges.card ≤ S.order := order_add_hinges_leMk (Mk := ∅) hM σ

/-- B1b (Mk-general form of `order_add_units_le`). -/
theorem order_add_units_leMk {Mk : Set (Stage1.CLVine _)} :
    (stSt (Mk := Mk) S σ).G.order + ((unitBlocks (Mk := Mk) S σ).map fun u => u.atoms.card - 1).sum ≤ S.order := by
  have h1 := order_add_mergedMk (Mk := Mk) hM σ
  have h3 := card_crownAtoms_leMk (Mk := Mk) hM σ
  have h5 := card_mergedAtomsMk (Mk := Mk) hM σ
  have h6 : ((unitBlocks (Mk := Mk) S σ).map fun u => u.atoms.card - 1).sum + (unitBlocks (Mk := Mk) S σ).length =
      ((unitBlocks (Mk := Mk) S σ).map fun u => u.atoms.card).sum := by
    have : ∀ l : List (CLBlock S), (∀ u ∈ l, 2 ≤ u.atoms.card) →
        (l.map fun u => u.atoms.card - 1).sum + l.length = (l.map fun u => u.atoms.card).sum := by
      intro l
      induction l with
      | nil => simp
      | cons u l ih =>
        intro h
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        have := ih fun v hv => h v (List.mem_cons_of_mem _ hv)
        have := h u (List.mem_cons_self ..)
        omega
    exact this _ fun u _ => two_le_card_atoms hM u
  omega

/-- `n_sb + Σ_u (|u.atoms| - 1) ≤ n_sk`. -/
theorem order_add_units_le :
    (stSt S σ).G.order + ((unitBlocks S σ).map fun u => u.atoms.card - 1).sum ≤ S.order := order_add_units_leMk (Mk := ∅) hM σ

end Counts
end WaveTurbulence.Represents
