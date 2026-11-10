/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WCount
public import WaveTurbulence.Foundations.Flower.Stage1W.Bridge

/-! # STAGE1W-VINE (T6, part 5): the weighted vine case at one parameter record

`vineCaseRepresentsFW_of_gate` (main's `vineCaseRepresents_of_gate`, RepVD15, with the frontier weight):
`VineCaseRepresentsFW {Pg with C₁ := C}` from the two leafwise gates (through `GateEnv Pg`), INC-TOP's
`TopIncoherentDecayAtR` (at `Pg` for the outer slots, at `{Pg with C₁ := C}` for T5), and the staged
**`V5FrontierClassBoundAt {Pg with C₁ := C}`**.

Weight bookkeeping: the outer slot `s'` carries `cψ ^ slotNr`, unit `j` carries `cψ ^ (9 |U_j| + 4 n₂(j))` and the
fixed constant `topFilterMass` (absorbed into the hinge constant `ChFW d η`); both `cψ`-powers are folded into the leaf
factors `lf`, `lfj` of main's `representsIntA_of_vineModes`, and their total exponent is `≤ 16 N` (`weight_exponent_le`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.PL2330
  WaveTurbulence.VineEstS5C VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W
open scoped ENNReal Classical

/-- The VINEEST mass of a unit with its weight power (without the top filter mass). -/
def unitMassC (P : WTParams) {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (cψ B₀ : ℝ) : ℝ :=
  cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) * unitMass P hM9 B RD hG layer hLayer B₀

theorem prod_pow_mul_prod {ι : Type*} [Fintype ι] (c : ℝ) (e : ι → ℕ) (f : ι → ℝ) :
    ∏ i, (c ^ e i * f i) = c ^ (∑ i, e i) * ∏ i, f i := by
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

section VineCase
variable (Pg : WTParams) (C : ℝ)

end VineCase

end WaveTurbulence.Flower.Stage1WVine
