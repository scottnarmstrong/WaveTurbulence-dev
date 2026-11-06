/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentTopLayer
/-! TARGET L2233–2235: keep the coherent top-tree truncation explicit. -/
public section
namespace WaveTurbulence.LGSpine
open Finset

theorem sum_topOrder_eq_order_of_uniform {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hlayer : ∀ a, LG.layer a = p) :
    ∑ j, LG.topOrder p j = LG.garden.order := by
  classical
  simp only [LayeredGarden.topOrder, hlayer, and_true]
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset (GBranch LG.garden.tree))) (t := (univ : Finset (Fin w)))
    (f := fun b : GBranch LG.garden.tree => b.1.1) (by simp)
  rw [card_univ, card_gbranch] at h
  exact h.symm

/-- A coherent canonical couple surviving the actual top-tree cutoff has total order at most
 twice that cutoff. Thus the high-order comparison with the full Taylor sum needs a tail bound. -/
theorem coherent_truncated_order_le {LG : LayeredGarden 2} {p Ntop Natt : ℕ}
    (hcan : IsCanonC (p + 1) LG) (hcoh : IsCoherentCouple LG)
    (htr : LG.IsTrunc p Ntop Natt) : LG.garden.order ≤ 2 * Ntop := by
  have hsum := sum_topOrder_eq_order_of_uniform LG p (coherent_canonical_layer_eq hcan hcoh)
  rw [Fin.sum_univ_two] at hsum
  have h0 := htr.1 0
  have h1 := htr.1 1
  omega

/-- Above twice the cutoff the coherent truncated sum vanishes; the Taylor term does not disappear. -/
theorem coherentCoupleSum_eq_zero_of_large_order (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (p N : ℕ) (hN : 2 * P.N (p + 1) < N) (t : ℝ) (k : Mom P.d) :
    coherentCoupleSum P F (p + 1) N t k = 0 := by
  classical
  unfold coherentCoupleSum
  apply sum_eq_zero
  intro LG hLG
  rcases mem_filter.mp hLG with ⟨hm, hc⟩
  have hm' : IsCanonC (p + 1) LG ∧
      LG.IsTrunc p (P.N (p + 1)) (P.N p) ∧ LG.garden.order = N := by
    simpa only [coupleCarrier, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Nat.add_sub_cancel] using hm
  have h := coherent_truncated_order_le hm'.1 hc hm'.2.1
  omega

end WaveTurbulence.LGSpine
