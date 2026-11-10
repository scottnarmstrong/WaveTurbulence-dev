/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.EngDInt
public import WaveTurbulence.Foundations.Flower.MkSlots.OuterFixD

/-! # B3s-HELPER3 B3 (2): pinned representations of the per-mode outer forms on a general domain

Domain-generic twin of `MkSlots/EngRep.lean`. The per-mode outer form is `outerValMμD … Dom …` against
`fixMeasure π.fix`; `Dom` enters through `MeasurableSet Dom`, `fixMeasure π.fix Dom ≤ 1`, the slice hypothesis `hsliceD`
(on the pinned slice `Dom` is the relaxed `splicedTimeDomainFix`) and the hinge hypothesis `HHkPropD` on the points of
`Dom` whose pinned coordinates are the pins. Main's `AsmCtxH` is still built from the unpinned `HHkProp`.

* `HHkPropD`: the hinge HasSum on `Dom ∩ pinSet π.fix`;
* `repIntCMK_of_asmHD` (`EngRep.repIntCMK_of_asmH` on `Dom`), `repIntCMK_modeD` (`repIntCMK_mode`),
  `repIntCMK_vine_modesD` (`repIntCMK_vine_modes`; the countable mode sums `MkSlots.repIntCMK_modes` are
  domain-free). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg.Skeleton
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsB

/-- **The hinge superposition property on a time domain `Dom`, at the pinned points** (main's `HHkProp`, RepVN2, with
`τ ∈ Dom` whose pinned coordinates are the pins in place of `τ ∈ splicedTimeDomain π.Gsb π.layer tt`). -/
abbrev HHkPropD {P : WTParams} {R : ℕ} {J : Type} (π : Stage1PieceMK P.d R) (tt : Fin (2 * R) → ℝ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (Dom : Set (GBranch π.Gsb.tree → ℝ)) (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (Hk : J → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) (H : HingeFam J P.d) : Prop :=
  ∀ κ : GenDecoration π.Gsb P.d roots 0, selSk κ → ∀ τ ∈ Dom, (∀ b v, π.fix b = some v → τ b = v) → ∀ j c,
    (∀ i, ‖(base + latticePoint P.L (κ.1 (hmom j i))) - latPt P.d (c i)‖ ≤ 1) →
    HasSum (fun l => (H.w j c l : ℂ) * H.a j c l (fun i => base + latticePoint P.L (κ.1 (hmom j i))) *
      fsPhase (H.m j c l) (fun i => clockOf π.Gsb tt τ (hclk j i)))
      (Hk j (fun i => clockOf π.Gsb tt τ (hclk j i)) (fun i => base + latticePoint P.L (κ.1 (hmom j i))))

end WaveTurbulence.Flower.MkSlotsB
