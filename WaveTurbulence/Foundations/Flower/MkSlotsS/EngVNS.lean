/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsS.EngRepS

/-! # B3s-HELPER4 (δ) S1: the selected engine (domain-generic)

**`representsIntMKSel_of_vineModesFixD`**: the twin of B3s's `MkSlots.representsIntMK_of_vineModesFix`
(`MkSlots/EngVN.lean`) with
* (i) the per-mode outer forms `outerValMμD … Dom …` on an arbitrary time domain `Dom` that agrees with the pinned
  kernel domain `fixLB π.Gsb π.layer tt π.fix π.lb = splicedTimeDomainFix … ∩ splicedLBDomain π.lb` (the pinned domain
  with the lower bounds of ruling R187) on time vectors extending the free times by the pins (`hsliceD`; with
  `Dom = splicedTimeDomain` and `π.lb = none` it is B3s's `hslice`), the hinge expansions on `Dom` (`HHkPropD`);
* (ii) the conclusion D7's `RepresentsIntMKSel π sel n cP tt base roots s val` for a finset `sel` of atoms of
  `G_sb` that are not unit clocks (`hselclk`): the moments `∏_{v∈sel}(1+|ξ_v|)^{1/18}` of the kernel frequencies are
  paid by the slots adjacent to `v` (per-slot time weights `θs s ≥ 2c + Σ_i selE s i`, as U1's `ModesMomentSel`),
  at the extra per-slot constant `selF s ∈ {1, 3}` carried by the slot losses in `hs`, and the loss
  `L^{7(47d+2)·#sel}` of `RepresentsIntMKSel` is the room for the stronger slot weights (`hs`).
  (Pinning or filters of the atoms of `sel` are not needed by the engine.)

* `representsIntMK_of_vineModesFix'`: at `sel = ∅`, `Dom = splicedTimeDomain`, `θs ≡ θ`, `π.lb = none` the hypotheses
  are B3s's (pre-R187 form) and the conclusion is B3s's (`representsIntMKSel_empty`): the α engine is recovered;
* `repMK_of_rep`: from the same data, plain `π.RepresentsIntMK n (cP + 343) tt base roots (b ^ N) val` when
  `s ≤ b^N` and `L^{7(47d+2)·#sel} ≤ L^{343·d·nProt}` (`Stage1MKGate.ClassPieceOK.repMK`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.MkSlots
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsS

/-- The order/gain part of the `RepresentsIntMK` bound. -/
def repCoreMK (P : WTParams) {R : ℕ} (π : Stage1PieceMK P.d R) (n : ℕ) : ℝ :=
  (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
    P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ))

/-- The selected bound in the form of `RepresentsIntMKSel`. -/
theorem repCoreMK_le_repBoundSel (P : WTParams) {R : ℕ} (π : Stage1PieceMK P.d R) (a n : ℕ) (cP s : ℝ)
    (hL1 : 1 ≤ P.L) (hcP : 0 ≤ cP) (hT0 : 0 ≤ repCoreMK P π n)
    (hs0 : 0 ≤ P.L ^ (7 * (47 * P.d + 2) * (a : ℝ)) * s) :
    repCoreMK P π n * (P.L ^ (7 * (47 * P.d + 2) * (a : ℝ)) * s) ≤ repBoundSel P π a n cP s := by
  have hLc : 1 ≤ P.L ^ (cP * P.d * (π.nProt : ℝ)) := Real.one_le_rpow hL1 (by positivity)
  calc repCoreMK P π n * (P.L ^ (7 * (47 * P.d + 2) * (a : ℝ)) * s)
      ≤ repCoreMK P π n * P.L ^ (cP * P.d * (π.nProt : ℝ)) * (P.L ^ (7 * (47 * P.d + 2) * (a : ℝ)) * s) :=
        mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hT0 hLc) hs0
    _ = repBoundSel P π a n cP s := by simp only [repCoreMK, repBoundSel]; ring

theorem repCoreMK_nonneg {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (n : ℕ) (hL1 : 1 ≤ P.L)
    (hC1 : 0 ≤ P.C₁) : 0 ≤ repCoreMK P π n := by
  have := Real.rpow_nonneg (zero_le_one.trans hL1) (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
      P.η ^ 7 * (π.Cs.hinges.card : ℝ))
  unfold repCoreMK
  positivity

/-- The numeric hypothesis forces `C₁ ≥ 0`. -/
theorem C₁_nonneg_of_hC {P : WTParams} (hd1 : 1 ≤ P.d) {K Ch : ℝ} (hK : 1 ≤ K) (hCh : 1 ≤ Ch)
    (hC : Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch ≤ P.C₁) : 0 ≤ P.C₁ := by
  obtain ⟨hCge, -⟩ := Cchi_spec hd1
  have hb1 : (1 : ℝ) ≤ nodeBallCard P.d := by exact_mod_cast nodeBallCard_pos P.d
  have : 1 ≤ Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch := by
    have h1 := one_le_mul_of_one_le_of_one_le hCge hb1
    have h2 : 1 ≤ (9 * K) ^ 2 := by nlinarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) hCh
  linarith

end WaveTurbulence.Flower.MkSlotsS
