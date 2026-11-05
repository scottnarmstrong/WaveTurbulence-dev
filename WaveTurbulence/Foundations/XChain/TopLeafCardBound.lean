/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeLeafCard
/-! Explicit leaf and block size bounds for bounded top forests. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem forest_card_leaves_le {w N : ℕ} (top : Fin w → TTree)
    (h : ∀ j, (top j).order ≤ N) : Fintype.card (GLeaf top) ≤ w * (2 * N + 1) := by
  have hs : (∑ j, (top j).order) ≤ w * N := by
    simpa only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] using
      sum_le_sum (s := (univ : Finset (Fin w))) (fun j _ => h j)
  rw [forest_card_leaves_eq]
  calc
    2 * (∑ j, (top j).order) + w ≤ 2 * (w * N) + w := by omega
    _ = w * (2 * N + 1) := by ring

theorem topBlock_card_le {w N : ℕ} (top : Fin w → TTree)
    (h : ∀ j, (top j).order ≤ N)
    (P : Finpartition (univ : Finset (GLeaf top))) (B : P.parts) :
    B.1.card ≤ w * (2 * N + 1) :=
  (card_le_univ B.1).trans (forest_card_leaves_le top h)

end WaveTurbulence.Induct
