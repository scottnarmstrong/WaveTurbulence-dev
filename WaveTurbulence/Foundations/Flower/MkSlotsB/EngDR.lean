/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.EngDRep
public import WaveTurbulence.Foundations.Flower.MkSlotsB.EngDShift
public import WaveTurbulence.Foundations.Flower.FinalMKFine.LBPin

/-! # B3s-HELPER3 B3 (5): the domain-generic engine on the relaxed pinned domain

* `hHkPropD_of_hHkProp`: main's unpinned hinge hypothesis `HHkProp` gives `HHkPropD` on the relaxed pinned domain
  `splicedTimeDomainFix π.Gsb π.layer tt π.fix`, when the pins lie in their windows and below the root times (`hpv`),
  are monotone along pinned parent–child pairs (`hpm`), and the hinge clocks at branches are free (`hclk0`): a pinned
  point `τ` of the relaxed domain is shifted into the unpinned domain without moving the free coordinates
  (`exists_shift_mem_splicedTimeDomain`), and the hinge HasSum reads `τ` only through the hinge clocks.
* `representsIntMK_of_vineModesFixR`: `representsIntMK_of_vineModesFixD` at `Dom := splicedTimeDomainFix …`, with
  EngVN's hinge hypothesis. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsB

/-- **`HHkPropD` on the relaxed pinned domain from main's `HHkProp`** (the shift method). -/
theorem hHkPropD_of_hHkProp {P : WTParams} {R : ℕ} {J : Type} (π : Stage1PieceMK P.d R) (tt : Fin (2 * R) → ℝ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (Hk : J → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) (H : HingeFam J P.d)
    (hpv : ∀ b v, π.fix b = some v → (π.layer b : ℝ) < v ∧ v ≤ π.layer b + 1 ∧ v ≤ tt b.1.1)
    (hpm : ∀ b b' v v', π.fix b = some v → π.fix b' = some v' → b'.IsChildOf b → v' ≤ v)
    (hclk0 : ∀ j i c, hclk j i = Sum.inr c → π.fix c = none)
    (hHk : HHkProp π.toStage1PieceD tt base roots selSk hclk hmom Hk H) :
    HHkPropD π tt base roots selSk (splicedTimeDomainFix π.Gsb π.layer tt π.fix) hclk hmom Hk H := by
  intro κ hsel τ hτ hpin j c hc
  obtain ⟨ε, -, hmem⟩ := exists_shift_mem_splicedTimeDomain π.Gsb π.layer tt π.fix hpv hpm τ hτ hpin
  have hclkeq : (fun i => clockOf π.Gsb tt (fun b => τ b - ε * shiftW π.fix b) (hclk j i)) =
      fun i => clockOf π.Gsb tt τ (hclk j i) := by
    funext i
    rcases h : hclk j i with y | b
    · rfl
    · show τ b - ε * shiftW π.fix b = τ b
      rw [shiftW_of_none π.fix (hclk0 j i b h), mul_zero, sub_zero]
  have key := hHk κ hsel _ hmem j c hc
  rw [hclkeq] at key
  exact key

end WaveTurbulence.Flower.MkSlotsB
