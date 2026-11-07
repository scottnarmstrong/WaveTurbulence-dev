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

/-- V5's class of a unit only depends on the start state and the raw start region: this identifies
`canonFinsetK p kind (Us.st A j) (Us.reg us j)` with `canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B)`
once the restricted state is the start state of the unit's chain assembly and the regions have the same `(U, a, b)`. -/
theorem canonFinsetK_congr {κ : Type*} [Fintype κ] {p : ℕ} {kind : Bool} {X X' : FamilyReconstruction w κ} (hX : X = X')
    {c : ChainAt X.skeleton X.family} {c' : ChainAt X'.skeleton X'.family} (hU : HEq c.U c'.U) (ha : HEq c.a c'.a)
    (hb : HEq c.b c'.b) : canonFinsetK p kind X c = canonFinsetK p kind X' c' := by
  have e : (⟨X, c⟩ : Σ Bs : FamilyReconstruction w κ, ChainAt Bs.skeleton Bs.family) = ⟨X', c'⟩ :=
    sigma_chainAt_ext hX hU ha hb
  exact congrArg (fun x : Σ Bs : FamilyReconstruction w κ, ChainAt Bs.skeleton Bs.family => canonFinsetK p kind x.1 x.2) e

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

/-- **The vine-case τ-class sum (VINE-C over VINE-B♯, INTERFACE v2).**  `V LG` is the (per-mode) value of a garden of the
class; `hV` is VINE-B♯'s per-state factorization at every class member, with the unit factors the member's recentered
modulated unit kernels `K̃^{U_j,(λ)}_{(y)}`.  Then the class sum is the factorization with the class kernels of the units
`K̃^{U_j,(λ)}` over V5's classes of the units. -/
theorem sum_tauClass_vineB {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    (us : ∀ j, UnitAt A.skeleton A.family (Us₀.Q j)) (T : Finset (LayeredGarden w))
    (hT : (T : Set (LayeredGarden w)) = A.allCoreOutputs (p := p) (kind := kind)) (V : LayeredGarden w → ℂ)
    {I : Type*} [Fintype I] (sgn : I → ℂ) {d : ℕ} (G : Garden w) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GBranch G.tree → ℕ) (hinges : Finset (GBranch G.tree))
    (Zw : GenDecoration G d roots 0 → ℝ) (hS : G.IsPlain) (amp : I → ReplacementSlot G → Mom d → ℂ)
    (frq : I → ReplacementSlot G → Fin 2 → ℤ) (route : I → ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J₀)
    (hclk : J₀ → Fin 3 → ClkSrc G) (hmom : J₀ → Fin 4 → GNode G.tree) (F : I → J₀ → ℕ → Mom d → ℝ)
    (hV : ∀ y ∈ classU Us₀ p kind A us, V y.1.layered = ∑ i, sgn i *
      outerValM G L γ δ base roots tt layer hinges Zw hS (amp i) (frq i) (route i) hclk hmom
        (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
          (k 0) (k 1) (k 2) (k 3)))
    (hint : ∀ i, ∀ y ∈ classU Us₀ p kind A us, ∀ z,
      Integrable (outerIntegrandM G L γ δ base roots tt layer hS (amp i) (frq i) (route i) hclk hmom
        (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
          (k 0) (k 1) (k 2) (k 3)) z))
    (hsm : ∀ i, ∀ y ∈ classU Us₀ p kind A us, Summable (fun z : GenDecoration G d roots 0 =>
      (splicedEpsilon G hinges z.1 : ℂ) * (Zw z : ℂ) *
        ∫ τ, outerIntegrandM G L γ δ base roots tt layer hS (amp i) (frq i) (route i) hclk hmom
          (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
            (k 0) (k 1) (k 2) (k 3)) z τ)) :
    ∑ LG ∈ T, V LG = ∑ i, sgn i *
      outerValM G L γ δ base roots tt layer hinges Zw hS (amp i) (frq i) (route i) hclk hmom
        (fun j lam t k => twistedRecenteredW A.skeleton (us j).blk.a
          (canonFinsetK p kind (Us₀.st A j) (Us₀.reg us j)) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
          (k 0) (k 1) (k 2) (k 3)) := by
  rw [sum_layered_eq_sum_classU hA us T hT V, Finset.sum_congr rfl hV, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact sum_classU_outerValM_kernel hA us G L γ δ base roots tt layer hinges Zw hS (amp i) (frq i) (route i) hclk hmom
    (F i) (hint i) (hsm i)

end Sum

end WaveTurbulence.VineC
