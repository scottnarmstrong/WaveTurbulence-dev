/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsS.EngMom

/-! # B3s-HELPER4 (δ) S1 (4): pinned representations on a domain, with selection moments

Copies of B3s's `MkSlots/EngRep.lean` with (i) the time domain an arbitrary `Dom` agreeing with the kernel domain
`fixLB = splicedTimeDomainFix ∩ splicedLBDomain π.lb` (ruling R187) on the pinned slice (`hsliceD`), the hinge
expansions on `Dom` (`HHkPropD`), and (ii) the
selection moments of the kernel frequencies carried in the mass (`RepIntCMKS`, `RepIntCMKF`):

* `repIntCMKF_of_asmHD` (B3s `repIntCMK_of_asmH`): the assembled expansion of an outer form over `domFix` is a
  `RepIntCMKF` whose frequencies are the assembled frequencies `A.freqH`;
* `repIntCMKS_mode` (B3s `repIntCMK_mode`): one outer slot mode on `Dom`; its moment is that of the routed
  frequencies (`routedFreq`), provided no unit clock is a selected branch (`hselclk`);
* `repIntCMKS_vine_modes` (B3s `repIntCMK_vine_modes`): the INTERFACE v2 mode form with per-slot time weights
  `θs`, the moments paid by the slots adjacent to the selected branches (`modes_mass_sel_le`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg.Skeleton
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsS

/-- **The hinge superposition property on a time domain `Dom`** (main's `HHkProp`, RepVN2, with `Dom` in place of the
unpinned spliced domain). -/
abbrev HHkPropD {P : WTParams} {R : ℕ} {J : Type} (π : Stage1Piece P R) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (Dom : Set (GBranch π.Gsb.tree → ℝ))
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (Hk : J → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) (H : HingeFam J P.d) : Prop :=
  ∀ κ : GenDecoration π.Gsb P.d roots 0, selSk κ → ∀ τ ∈ Dom, ∀ j c,
    (∀ i, ‖(base + latticePoint P.L (κ.1 (hmom j i))) - latPt P.d (c i)‖ ≤ 1) →
    HasSum (fun l => (H.w j c l : ℂ) * H.a j c l (fun i => base + latticePoint P.L (κ.1 (hmom j i))) *
      fsPhase (H.m j c l) (fun i => clockOf π.Gsb tt τ (hclk j i)))
      (Hk j (fun i => clockOf π.Gsb tt τ (hclk j i)) (fun i => base + latticePoint P.L (κ.1 (hmom j i))))

end WaveTurbulence.Flower.MkSlotsS
