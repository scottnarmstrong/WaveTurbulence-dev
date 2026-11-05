/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentTruncation
public import WaveTurbulence.Foundations.RegStruct.SourceRegularDecoding
/-! The full coherent canonical carrier equals the source's top-layer regular carrier.
The truncation predicate is retained separately and removed only in the proved low-order range. -/
public section
namespace WaveTurbulence.LGSpine
open Finset Set WaveTurbulence.Reg

theorem canonCriterion_of_uniform_layer {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hlayer : ∀ a, LG.layer a = p) : LG.CanonCriterion p := by
  have hpar : ∀ a, LG.parentLayer p a = p := by
    intro a
    unfold LayeredGarden.parentLayer
    split_ifs
    · rfl
    · exact hlayer _
  refine ⟨fun a => (hlayer a).le, ?_⟩
  intro a a' _ _
  simp only [hpar, hlayer, min_self, max_self, le_refl]

theorem coherent_canonical_iff_regular_uniform (LG : LayeredGarden 2) (p : ℕ) :
    (IsCanonC (p + 1) LG ∧ IsCoherentCouple LG) ↔
      (IsRegularCouple LG.garden ∧ ∀ a, LG.layer a = p) := by
  constructor
  · rintro ⟨hcan, hcoh⟩
    exact ⟨hcoh.1, coherent_canonical_layer_eq hcan hcoh⟩
  · rintro ⟨hreg, hlayer⟩
    obtain ⟨Q, hwf, hQ⟩ := isRegularCouple_exists_wf_decodes LG.garden hreg
    refine ⟨⟨hQ.1, canonCriterion_of_uniform_layer LG p hlayer⟩, hreg, Q, hwf, hQ, ?_⟩
    simp only [LayeredGarden.incoherency, hlayer, ne_self_iff_false, and_false, filter_false,
      Finset.card_empty]

theorem coherent_truncated_carrier_iff_of_small_order (P : WTParams) (p N : ℕ)
    (hN : N ≤ P.N (p + 1)) (LG : LayeredGarden 2) :
    (LG ∈ coupleCarrier P (p + 1) N ∧ IsCoherentCouple LG) ↔
      (IsRegularCouple LG.garden ∧ LG.garden.order = N ∧ ∀ a, LG.layer a = p) := by
  classical
  simp only [coupleCarrier, Set.Finite.mem_toFinset, mem_ofPred_eq, Nat.add_sub_cancel]
  constructor
  · rintro ⟨⟨hcan, _, horder⟩, hcoh⟩
    exact ⟨hcoh.1, horder, coherent_canonical_layer_eq hcan hcoh⟩
  · rintro ⟨hreg, horder, hlayer⟩
    have hc := (coherent_canonical_iff_regular_uniform LG p).mpr ⟨hreg, hlayer⟩
    refine ⟨⟨hc.1, ⟨fun j => ?_, fun u _ => ?_⟩, horder⟩, hc.2⟩
    · exact (LG.topOrder_le_order p j).trans (horder ▸ hN)
    · have hnext : P.N (p + 1) ≤ P.N p := by
        simpa only [Nat.add_sub_cancel] using P.N_le_N_pred (q := p + 1) (by omega)
      exact (LG.attachedOrder_le_order p u).trans ((horder ▸ hN).trans hnext)

end WaveTurbulence.LGSpine
