/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoupleZeroClassification
public import WaveTurbulence.Foundations.Spine.CoherentZeroNorm
/-! Full order-zero couple remainder, including the classification of every carrier term. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset WaveTurbulence.Reg
open scoped ENNReal

theorem coherent_of_couple_order_zero (LG : LayeredGarden 2) (hc : IsCouple LG.garden)
    (ho : LG.garden.order = 0) : IsCoherentCouple LG := by
  have hQ := trivial_decodes_of_couple_zero LG.garden hc ho
  have hg := carrier_unique (uniformDecodedCouple_decodes 0 .triv) hQ
  have hreg := uniformDecodedCouple_regular 0 .triv rfl
  refine ⟨hg ▸ hreg, .triv, rfl, hQ, ?_⟩
  simp only [LayeredGarden.incoherency, RegCpl.links, RegCpl.linksAt,
    List.not_mem_nil, false_and, filter_false, card_empty]

end WaveTurbulence.LGSpine
