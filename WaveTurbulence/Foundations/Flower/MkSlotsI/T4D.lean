/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PVBRInteg
public import WaveTurbulence.Foundations.Flower.MkUnitsL.ClassL

/-! # B3s MK-SLOTS (final assembly): the pinned list-T4 on a general time domain

The τ-class sum of the members' per-mode outer values is the outer value with the class kernels. α's
`MkSlots/IntT4.lean` states this (T4) for `outerValMμ` (fixed layered domain, any time measure, complex decoration
weight) with the `Option ℝ` top filters of V5W; B3-2's `MkUnitsL/ClassL.lean` states it for main's `outerValM`
(Lebesgue, real decoration weight) with the LIST top filters `SU : J₀ → List ℝ`. Both proofs only use main's generic
`VineC.sum_outer_core`, which holds for every measure and every time domain. Here they are combined for the
domain-generic pinned outer form `outerValMμD … Dom …` (arbitrary time domain `Dom`, time measure `μ`, complex
decoration weight `Zw`), whose integrand is β's `outerIntegrandMD`.

* `sum_classU_outerValMμD` (α's `sum_classU_outerValMμ` on the domain `Dom`);
* **`weightedClassFactorizationμDL`** (B3-2's `WeightedClassFactorizationL` for `outerValMμD`, unit kernels
  `unitRecenteredFWL`, class kernels `twistedRecenteredFWL`).

Copied by source (see `COPIED-SHA256SUMS`). -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkSlotsI
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Represents WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 TTree MeasureTheory
open WaveTurbulence.VineC WaveTurbulence.Flower.V5W
open WaveTurbulence.Flower.V5W2L (twistedLocalKernelFWL twistedRecenteredFWL unitRecenteredFWL)
open WaveTurbulence.Flower.MkSlots (outerValMμD)
open WaveTurbulence.Flower.MkSlotsB (outerIntegrandMD)
open WaveTurbulence.Flower.MkUnitsL (unitKernelFWL_classProd)

variable {w : ℕ}

section Outer
variable {ι : Type*} {J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J] {κ : J → Type*}
  [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] {Us : UnitSplit ι J κ} {p : ℕ} {kind : Bool}

-- [copied] world `Flower/MkSlots/IntT4.lean` lines 41–70 (`sum_classU_outerValMμ`), with `outerValMμ` →
-- `outerValMμD` (time domain `Dom`) and `outerIntegrandM` → `outerIntegrandMD`, see COPIED-SHA256SUMS.
/-- **The class sum of the per-mode outer form on a time domain `Dom`, against a time measure `μ`.** For unit factors
of the class members that are functions of the unit coordinates, `Σ_{y ∈ τ} outerValMμD(HkM_y) = outerValMμD(Σ-class
factors)`, given the `μ`-integrability of each member's integrand and the summability of its decoration sum. -/
theorem sum_classU_outerValMμD {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)) {d : ℕ} (G : Garden w) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (Dom : Set (GBranch G.tree → ℝ))
    (hinges : Finset (GBranch G.tree)) (Zw : GenDecoration G d roots 0 → ℂ) (hS : G.IsPlain)
    (μ : Measure (GBranch G.tree → ℝ)) (amp : ReplacementSlot G → Mom d → ℂ)
    (frq : ReplacementSlot G → Fin 2 → ℤ) (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J)
    (hclk : J → Fin 3 → ClkSrc G) (hmom : J → Fin 4 → GNode G.tree)
    (HkMy : UState w Us → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ)
    (gk : ∀ j, ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) →
      (Σ X : FamilyReconstruction w (κ j), ChainAt X.skeleton X.family) → ℂ)
    (hfg : ∀ y ∈ classU Us p kind A us, ∀ j lam t k, HkMy y j lam t k = gk j lam t k (classProd Us p kind A us y j))
    (hint : ∀ y ∈ classU Us p kind A us, ∀ z,
      Integrable (outerIntegrandMD G L γ δ base roots tt Dom hS amp frq route hclk hmom (HkMy y) z) μ)
    (hsm : ∀ y ∈ classU Us p kind A us, Summable (fun z : GenDecoration G d roots 0 =>
      (splicedEpsilon G hinges z.1 : ℂ) * Zw z *
        ∫ τ, outerIntegrandMD G L γ δ base roots tt Dom hS amp frq route hclk hmom (HkMy y) z τ ∂μ)) :
    ∑ y ∈ classU Us p kind A us,
        outerValMμD G L γ δ base roots tt Dom hinges Zw hS μ amp frq route hclk hmom (HkMy y) =
      outerValMμD G L γ δ base roots tt Dom hinges Zw hS μ amp frq route hclk hmom
        (fun j lam t k => ∑ x ∈ canonFinsetK p kind (Us.st A j) (Us.reg us j), gk j lam t k x) := by
  unfold outerValMμD
  refine sum_outer_core _ μ _ (fun z => (splicedEpsilon G hinges z.1 : ℂ) * Zw z) Dom
    (fun z τ => phaseProd L γ δ G (cosetDecoration G L base z.1) τ *
      (∏ s, amp s (base + latticePoint L (z.1 (slotNode hS s)))) * routedPhase frq route tt τ)
    (fun y z τ => ∏ j, HkMy y j (modLam frq route j) (fun c => clockOf G tt τ (hclk j c))
        (fun c => base + latticePoint L (z.1 (hmom j c))))
    (fun z τ => ∏ j, ∑ x ∈ canonFinsetK p kind (Us.st A j) (Us.reg us j), gk j (modLam frq route j)
        (fun c => clockOf G tt τ (hclk j c)) (fun c => base + latticePoint L (z.1 (hmom j c))) x)
    (fun z τ => sum_classU_prod hA us _ _ fun y hy j => hfg y hy j _ _ _) hint hsm
-- [end copied]

end Outer

-- [copied] world `Flower/MkUnitsL/ClassL.lean` lines 95–136 (`WeightedClassFactorizationL`, statement) and
-- lines 254–291 (`weightedClassFactorizationL`, proof), with `outerValM … lay … (Zw : → ℝ) …` →
-- `outerValMμD … Dom … (Zw : → ℂ) … μ …`, `outerIntegrandM … lay …` → `outerIntegrandMD … Dom …` (integrals against
-- `μ`), `sum_classU_outerValM` → `sum_classU_outerValMμD`; stated as a theorem (not through a `Prop`), see
-- COPIED-SHA256SUMS.
-- [end copied]

end WaveTurbulence.Flower.MkSlotsI
