/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGroupCatalogue
public import WaveTurbulenceVineParam.VineParamNormalizedBaseSource
public import WaveTurbulenceVineParam.VineParamBaseOutgoing
import Mathlib.Tactic

/-! # Complete physical parametrization of every actual directed base vine

Directions are recovered from the source shape and degree equations.
All physical origins and cap supports are produced, not assumed.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- Complete source producer for an arbitrary directed base template.
The root labels specify which of the two actual joints is included. -/
theorem exists_physical_base_chart (X : VineType) {m : ℕ}
    (A : Fin m → Fin X.template.n × Fin X.template.n)
    (hU : ((List.ofFn (fun e => ((A e).1.1,(A e).2.1)) : List (ℕ×ℕ)) : Multiset (ℕ×ℕ)).map
      (fun e => s(e.1,e.2))=(X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)))
    (hdeg : ∀ v : Fin X.template.n,
      outgoingCount (List.ofFn (fun e => ((A e).1.1,(A e).2.1))) v.1=if v.1<2 then 1 else 2)
    (joint : Fin 2) (a b : Fin X.template.n) (ha : a.1=1-joint.1) (hb : b.1=joint.1) :
    ∃ P : PhysicalGraphChart A X a b,
      (∀ s : Fin X.template.slots.length,P.CapSupported (baseSourceCap X s)) ∧
      (∀ s : Fin X.template.slots.length,∀ j : Fin P.full.indexing.shape.m,
        (P.full.indexing.atom (P.full.indexing.shape.xSlot j)).1 ∈ baseSourceCap X s ↔
          (P.full.indexing.atom (P.full.indexing.shape.ySlot j)).1 ∈ baseSourceCap X s) ∧
      indexingGroupSet P.full.indexing (fun v => v.1) = listGroupSet X.template.groups := by
  obtain ⟨p,hp⟩ := exists_actual_base_profile X
    (List.ofFn (fun e => ((A e).1.1,(A e).2.1))) hU hdeg
  obtain ⟨C,H,haC,hbC,hG⟩ := exists_normalized_base_certificate_groups X joint p
  apply exists_physical_base_of_certificate C H hG A hU
    (by simpa only [Multiset.coe_count] using hp) a b
    (haC.trans ha.symm) (hbC.trans hb.symm)

end WaveTurbulence.Vine.Param
