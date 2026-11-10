/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntMember1
public import WaveTurbulence.Foundations.Flower.MkUnits.WMember

/-! # B3s MK-SLOTS (integration, member identity 2): a member's class summand is a pinned skeleton value

For a member `y` of the run class of the representative `a` (at the marking `mk`, classes at `mkF`):
the frozen class summand of `y.1.layered` (`kernelKgenSel` with the plain intrinsic pins, the removed phases and the
marked weight, at the selection `selPMk` of the fine′ class) is the `G_sb` dagger constant `capConstO` times the
pinned skeleton value `skelValF` of `y` (pinned slot kernels with the chain node weight `chainW`, pins
`fixCore … fixCap`), at a skeleton selection `selSk` whose indicator is the `G_sb` weight `ZwG` (the piece's
dagger sibling indicator times the common gap selection `selSkCMk`) at the restricted decoration
(`member_skelVal`).

Route: `classSummand_eq_capKernel` (frozen summand = pinned weighted cap kernel) → `selPMk_iff_related` (the selection
of the fine′ class is the member's own `selAt`) → `capKernel_reconstruction` → `prod_capNodeW_split` +
`restW_cosetDecoration` + `kernelLeavesSelNWF_mul_ind` (the remaining dagger weight is a constant on the support of
`RestInd`) → `kernelLeaves_skeleton_reduction_selNWF`; `member_restConst`, `member_sibInd` (R-core) and B3's
`hZ_commonMk` for the selection. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence.Flower.Stage1MKGate

namespace WaveTurbulence.Flower.MkSlots.IntMember

open WaveTurbulence.Flower.MkSlots.IntRest WaveTurbulence.Flower.MkSlots.IntCore

section Defs
variable {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))

/-- The skeleton dagger support of a dagger datum (`True` without dagger). -/
def restIndO {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (L : ℝ) (J : Finset (Fin w))
    (dag : Option (Fin w → Fin 3 → Mom d)) {roots : Fin w → (Fin d → ℤ)} (κS : GenDecoration S d roots 0) : Prop :=
  dag.elim True fun cc => RestInd D hS layer hLayer L J cc κS

/-- The skeleton dagger constant of a dagger datum (`1` without dagger). -/
def restConstO {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (L γ δ s : ℝ) (J : Finset (Fin w))
    (roots : Fin w → (Fin d → ℤ)) (dag : Option (Fin w → Fin 3 → Mom d)) : ℂ :=
  dag.elim 1 fun cc => restConst D hS layer hLayer L γ δ s J roots cc

/-- **The `G_sb` dagger constant** of a dagger datum (`1` without dagger). -/
def capConstO {d : ℕ} (J : Finset (Fin (2 * R))) (L γ δ s : ℝ) (roots : Fin (2 * R) → (Fin d → ℤ))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom d)) : ℂ :=
  dag.elim 1 fun cc => capConstG a mk J L γ δ s roots cc

theorem norm_capConstO {d : ℕ} (J : Finset (Fin (2 * R))) (L γ δ s : ℝ) (roots : Fin (2 * R) → (Fin d → ℤ))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom d)) : ‖capConstO a mk J L γ δ s roots dag‖ = 1 := by
  cases dag with
  | none => simp [capConstO]
  | some cc => exact norm_capConstG a mk J L γ δ s roots cc

/-- **The decoration weight of `G_sb`**: the piece's dagger sibling indicator times the common gap selection. -/
def ZwG {d : ℕ} (J : Finset (Fin (2 * R))) (L γ η : ℝ) (hL : L ≠ 0) (roots : Fin (2 * R) → (Fin d → ℤ))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom d))
    (z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G d roots 0) : ℝ :=
  sibIndAt J a (mk a.prime) dag (flwAt J a (mk a.prime))
      (cosetDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G L 0 z.1) *
    (if selSkCMk a mk L γ η hL 0 roots z then 1 else 0)

end Defs

end WaveTurbulence.Flower.MkSlots.IntMember
