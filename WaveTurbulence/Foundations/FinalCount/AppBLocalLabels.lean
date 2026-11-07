/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBRealizations
import Mathlib.Tactic

/-! # Exact local label encoding for Appendix B deletion counts -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D K : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

def localLabels (κ : D → K) : Fin P.edges.length → K := fun i => κ (r.edge i).val

def retainedLabels (κ : D → K) : Degen.RetainedDart M r.removedAtoms → K := fun x => κ x.val

/-- Local labels determine every removed outgoing label, including
parallel bonds individually. -/
theorem removed_label_eq {κ κ' : D → K} (hq : r.localLabels κ = r.localLabels κ')
    {x : D} (hx : x ∈ appbRemovedBonds M r.removedAtoms) : κ x = κ' x := by
  have he := congrFun hq (r.edge.symm ⟨x,hx⟩)
  change κ (r.edge (r.edge.symm ⟨x,hx⟩)).val = κ' (r.edge (r.edge.symm ⟨x,hx⟩)).val at he
  simpa only [r.edge.apply_symm_apply] using he

/-- The actual split into removed outgoing labels and retained labels is
injective on bond-constant decorations. This supplies the fiber encoding
for basiccount, rather than assuming a count comparison. -/
theorem labels_injective {κ κ' : D → K}
    (hκ : ∀ x, κ (M.mate x) = κ x) (hκ' : ∀ x, κ' (M.mate x) = κ' x)
    (hq : r.localLabels κ = r.localLabels κ') (hret : r.retainedLabels κ = r.retainedLabels κ') : κ = κ' := by
  funext x
  by_cases hkeep : M.atom x ∉ r.removedAtoms ∧ M.atom (M.mate x) ∉ r.removedAtoms
  · exact congrFun hret ⟨x,hkeep⟩
  · have hdel : M.atom x ∈ r.removedAtoms ∨ M.atom (M.mate x) ∈ r.removedAtoms := by tauto
    cases hout : M.out x
    · have hmate : M.mate x ∈ appbRemovedBonds M r.removedAtoms := by
        apply mem_filter.mpr
        constructor
        · apply mem_filter.mpr
          exact ⟨mem_univ _,by rw [M.out_mate,hout]; rfl⟩
        · simpa only [M.mate_mate,or_comm] using hdel
      have he := r.removed_label_eq hq hmate
      simpa only [hκ,hκ'] using he
    · exact r.removed_label_eq hq (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hout⟩,hdel⟩)

/-- Exact finite counting consequence of the source label decomposition. -/
theorem card_le_local_mul_retained [DecidableEq K] (S : Finset (D → K))
    (hb : ∀ κ ∈ S, ∀ x, κ (M.mate x) = κ x) :
    S.card ≤ (S.image r.localLabels).card * (S.image r.retainedLabels).card := by
  let f : (D → K) → (Fin P.edges.length → K) × (Degen.RetainedDart M r.removedAtoms → K) :=
    fun κ => (r.localLabels κ,r.retainedLabels κ)
  have hi : Set.InjOn f S := by
    intro κ hκ κ' hκ' he
    exact r.labels_injective (hb κ hκ) (hb κ' hκ') (congrArg Prod.fst he) (congrArg Prod.snd he)
  calc
    S.card = (S.image f).card := (card_image_of_injOn hi).symm
    _ ≤ ((S.image r.localLabels) ×ˢ (S.image r.retainedLabels)).card := by
      apply card_le_card
      intro q hq
      obtain ⟨κ,hκ,rfl⟩ := mem_image.mp hq
      exact mem_product.mpr ⟨mem_image_of_mem _ hκ,mem_image_of_mem _ hκ⟩
    _ = _ := card_product _ _

end AppbRealization
end WaveTurbulence.Mole
