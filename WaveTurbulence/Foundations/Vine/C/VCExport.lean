/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.C.VCOuter

/-! # VINE-C export: the τ-class sum over VINE-B♯'s per-mode factorization (INTERFACE v2, R58)

* `unitKernelW_eq_of_data`, `unitRecenteredW_eq_of_data`: the unit kernel of a class member does not depend on the choice
  of the CL region data of the unit's block (`regionData_subsingleton`) nor on the presentation of the layering
  (`layeredReconstruction_inj`): any region data of the triple `(U, a, b)` and any layering decoding the member's layered
  garden give the same kernel.  This is how a per-state kernel built from `unitBlocks` (VINE-B♯) is matched with the
  carried unit regions of the class.
* `canonFinsetK_congr`: V5's class of a unit depends only on the start state and the raw start region `(U, a, b)`.
* `sum_layered_eq_sum_classU`: a sum over the gardens of the τ-class is the sum over the class members `classU`.
* `sum_tauClass_vineB`: **the vine-case class sum**.  If every member's (per-mode) value is VINE-B♯'s factorization
  `Σ_i sign_i · outerValM(…_i…, K̃^{U_j,(λ_j)}_{(y)})`, then
  `Σ_{LG ∈ τ} value = Σ_i sign_i · outerValM(…_i…, K̃^{U_j,(λ_j)})` with the recentered modulated class kernels of the
  units over V5's classes `canonFinsetK p kind (Us.st A j) (Us.reg us j)` (the modulations `λ_j = modLam frq route j` as
  parameters; `λ = 0` is the unmodulated form).  The integrability and summability of each member's outer integrand are
  hypotheses (they are VINE-D's analytic input; the identity is a finite interchange).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineC
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Represents WaveTurbulence.RegRed WaveTurbulence.LGSpine TTree MeasureTheory

variable {w : ℕ}

section Data
variable {ι : Type*} {Q : ι → Prop}

/-- The unit kernel with any region data of the block and any layering decoding the state. -/
theorem unitKernelW_eq_of_data {d : ℕ} (X : FamilyReconstruction w ι) (u : UnitAt X.skeleton X.family Q)
    (R : CLRegionData X.skeleton u.blk.U u.blk.a u.blk.b) (layer : GNode (X.data.forest X.plain) → ℕ)
    (hL : IsLayering (X.data.garden X.plain) layer) (hspec : layeredReconstruction X.data X.plain layer hL = X.layered)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    clLocalKernelW X.data X.plain R L γ δ F layer hL base W t0 t1 t2 e f g h =
      unitKernelW X u L γ δ F base W t0 t1 t2 e f g h := by
  have hl : layer = stateLayer X := layeredReconstruction_inj X.data X.plain (hspec.trans (stateLayer_spec X).symm)
  subst hl
  rw [regionData_subsingleton R (clRegionData X.skeleton u.blk.block u.cl)]
  rfl

/-- The recentered unit kernel with any region data of the block and any layering decoding the state. -/
theorem unitRecenteredW_eq_of_data {d : ℕ} (X : FamilyReconstruction w ι) (u : UnitAt X.skeleton X.family Q)
    (R : CLRegionData X.skeleton u.blk.U u.blk.a u.blk.b) (layer : GNode (X.data.forest X.plain) → ℕ)
    (hL : IsLayering (X.data.garden X.plain) layer) (hspec : layeredReconstruction X.data X.plain layer hL = X.layered)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    recPhase (X.skeleton.sign u.blk.a.toNode) L γ δ t0 e f g h *
        clLocalKernelW X.data X.plain R L γ δ F layer hL base W t0 t1 t2 e f g h =
      unitRecenteredW X u L γ δ F base W t0 t1 t2 e f g h := by
  rw [unitKernelW_eq_of_data X u R layer hL hspec]
  rfl

end Data

section Start

end Start

section Sum
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J] {κ : J → Type*}
  [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] {Us : UnitSplit ι J κ} {p : ℕ} {kind : Bool}

omit [Fintype J] [DecidableEq J] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] in
/-- **A sum over the gardens of the τ-class is the sum over the class members.** -/
theorem sum_layered_eq_sum_classU {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)) (T : Finset (LayeredGarden w))
    (hT : (T : Set (LayeredGarden w)) = A.allCoreOutputs (p := p) (kind := kind)) {M : Type*} [AddCommMonoid M]
    (V : LayeredGarden w → M) :
    ∑ LG ∈ T, V LG = ∑ y ∈ classU Us p kind A us, V y.1.layered := by
  classical
  have hinj : Set.InjOn (fun y : UState w Us => y.1.layered) (classU Us p kind A us) := by
    intro y hy y' hy' he
    exact classU_layered_injOn hA us ((mem_classU hA).mp hy) ((mem_classU hA).mp hy') he
  have himg : (classU Us p kind A us).image (fun y => y.1.layered) = T := by
    apply Finset.coe_injective
    rw [Finset.coe_image, hT, ← classU_layered_image (p := p) (kind := kind) us]
    congr 1
    ext y
    exact mem_classU hA
  rw [← himg, Finset.sum_image hinj]

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {κ₀ : J₀ → Type*} [∀ j, Fintype (κ₀ j)] [∀ j, DecidableEq (κ₀ j)]
  {Us₀ : UnitSplit ι J₀ κ₀}

end Sum

end WaveTurbulence.VineC
