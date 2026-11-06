/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentCarrier
public import WaveTurbulence.Foundations.Spine.CoherentSourceTypes
/-! Finite top-layer carriers and the exact low-order split used to consume Prop 6.2. -/
@[expose] public section
namespace WaveTurbulence.LGSpine
open Finset Set

def topRegularCarrier (p N : ℕ) : Set (LayeredGarden 2) :=
  {LG | IsRegularCouple LG.garden ∧ LG.garden.order = N ∧ ∀ a, LG.layer a = p}

theorem finite_topRegularCarrier (p N : ℕ) : (topRegularCarrier p N).Finite :=
  (Canon.finite_canonC (p + 1) N).subset fun LG h =>
    ⟨((coherent_canonical_iff_regular_uniform LG p).mpr ⟨h.1, h.2.2⟩).1, h.2.1.le⟩

theorem finsum_topRegular_eq_sum {d : ℕ} (p N : ℕ) (f : LayeredGarden 2 → Mom d → ℂ) (k : Mom d) :
    (∑ᶠ (LG : LayeredGarden 2) (_ : IsRegularCouple LG.garden ∧ LG.garden.order = N ∧
      ∀ a, LG.layer a = p), f LG k) =
      ∑ LG ∈ (finite_topRegularCarrier p N).toFinset, f LG k := by
  rw [← finsum_mem_eq_finite_toFinset_sum]
  rfl

theorem coherentCoupleSum_eq_full_of_small_order (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (p N : ℕ) (hN : N ≤ P.N (p + 1)) (t : ℝ) (k : Mom P.d) :
    coherentCoupleSum P F (p + 1) N t k =
      ∑ LG ∈ (finite_topRegularCarrier p N).toFinset, KQ P.L P.γ P.δ F LG t k := by
  classical
  have he : (coupleCarrier P (p + 1) N).filter IsCoherentCouple =
      (finite_topRegularCarrier p N).toFinset := by
    ext LG
    rw [mem_filter, Set.Finite.mem_toFinset]
    exact coherent_truncated_carrier_iff_of_small_order P p N hN LG
  unfold coherentCoupleSum
  rw [he]


end WaveTurbulence.LGSpine
