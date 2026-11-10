/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.C.VCClass2
public import WaveTurbulence.Foundations.Stage1.Represents.RepOuterM

/-! # VINE-C: the recentered unit kernels and the class sum of the per-mode outer form (INTERFACE v2, R58)

* `unitRecenteredW X u … W …`: the recentered weighted unit kernel of a class member (the member term of TARGET (vineest1),
  `e^{-πiδL^{2γ}t_{u1}Γ} K^{U,(W)}_{(G)}`); `twistedRecenteredW G a Z … W …`: the recentered class kernel (V5's
  `twistedRecentered` for `W = 1`, V5-CONT's `twistedRecenteredModC … λ` for `W = modW λ`, up to the order of the factors in
  the integrand, see the HANDOFF bridge).
* `ReachU.sign_upper`: the sign of the upper joint of a unit is invariant along the class (only lower joints flip).
* `sum_classU_prod_recenteredW`: `Σ_{y ∈ τ} Π_j K̃^{U_j,(W_j)}_{(y)} = Π_j K̃^{U_j,(W_j)}` (class kernels of the units).
* `sum_classU_outerValM`: the class sum of S2's per-mode outer form `outerValM` (INTERFACE v2, step 3) with the per-member
  unit kernels is `outerValM` with the class kernels, given the integrability of each member's integrand and the
  summability of each member's decoration sum (`sum_classU_outerValM_kernel`: the kernel instance with `W_j = modW λ_j`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineC
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Represents WaveTurbulence.RegRed WaveTurbulence.LGSpine TTree MeasureTheory

variable {w : ℕ}

/-- The recentering phase `e^{-πiδL^{2γ} t_{u1} Γ}` of a unit with upper-joint sign `s`. -/
@[expose] noncomputable def recPhase {d : ℕ} (s : ℤˣ) (L γ δ : ℝ) (t0 : ℝ) (e f g h : Mom d) : ℂ :=
  Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * t0 * boundaryEnergyFromMomenta s e f g h : ℝ) : ℂ) * Complex.I)

/-- The recentered weighted kernel of the unit region `u` of the state `X`. -/
@[expose] noncomputable def unitRecenteredW {ι : Type*} {Q : ι → Prop} {d : ℕ} (X : FamilyReconstruction w ι)
    (u : UnitAt X.skeleton X.family Q) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ)
    (e f g h : Mom d) : ℂ :=
  recPhase (X.skeleton.sign u.blk.a.toNode) L γ δ t0 e f g h * unitKernelW X u L γ δ F base W t0 t1 t2 e f g h

/-- The recentered weighted class kernel `e^{-πiδL^{2γ}t_{u1}Γ} Σ_{x ∈ Z} K^{U,(W)}_{(x)}` (TARGET (vineest1)). -/
@[expose] noncomputable def twistedRecenteredW {κ : Type*} {d : ℕ} (G : Garden w) (a : GBranch G.tree)
    (Z : Finset (Σ Bs : FamilyReconstruction w κ, ChainAt Bs.skeleton Bs.family)) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g h : Mom d) : ℂ :=
  recPhase (G.sign a.toNode) L γ δ t0 e f g h * ∑ x ∈ Z, twistedLocalKernelW x.1 x.2 L γ δ F base W t0 t1 t2 e f g h

section Sign
variable {ι J : Type*} {Qm : J → ι → Prop} {p : ℕ} {kind : Bool}

/-- **The sign of the upper joint of a unit is invariant along a batch** (unit twists flip only the lower joints of
members, which are never the upper joint of a unit). -/
theorem ReachU.sign_upper {L : List ι} {A B : FamilyReconstruction w ι} {us : ∀ j, UnitAt A.skeleton A.family (Qm j)}
    {us' : ∀ j, UnitAt B.skeleton B.family (Qm j)} (h : ReachU p kind Qm L A us B us') (j : J) :
    B.skeleton.sign (us' j).blk.a.toNode = A.skeleton.sign (us j).blk.a.toNode := by
  induction h with
  | nil A us => rfl
  | skip i h ih => exact ih
  | @apply L A us B us' i op h ih =>
    refine ih.trans ?_
    obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    cases ε
    · rfl
    · have hne : (us j).blk.a ≠ (A.family.placement i).lower := by
        by_cases hi : Qm j i
        · exact ((us j).lower_ne i hi).symm
        · intro he
          exact Finset.disjoint_left.mp ((us j).disj i hi) (lower_mem_atoms A.family i) (he ▸ (us j).blk.block.2.1)
      show (unitTwistGarden A.skeleton (A.family.placement i)).sign
          (coreBranchEquiv A.skeleton (A.family.placement i) (us j).blk.a).toNode = _
      rw [coreBranchEquiv_sign, ite_eq_right hne]

end Sign

section Class
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J] {κ : J → Type*}
  [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] {Us : UnitSplit ι J κ} {p : ℕ} {kind : Bool}

end Class

/-! ## The class sum of the per-mode outer form -/

/-- A finite sum of outer expressions `C · Σ'_z a_z ∫ 1_S · P · H_y` with integrable and summable members is the outer
expression of the summed factor. -/
theorem sum_outer_core {Y : Type*} (s : Finset Y) {Z : Type*} {T : Type*} [MeasurableSpace T] (μ : Measure T) (C : ℂ)
    (a : Z → ℂ) (S : Set T) (P : Z → T → ℂ) (Hy : Y → Z → T → ℂ) (Hc : Z → T → ℂ)
    (hsum : ∀ z τ, ∑ y ∈ s, Hy y z τ = Hc z τ)
    (hint : ∀ y ∈ s, ∀ z, Integrable (fun τ => S.indicator (fun τ => P z τ * Hy y z τ) τ) μ)
    (hsm : ∀ y ∈ s, Summable (fun z => a z * ∫ τ, S.indicator (fun τ => P z τ * Hy y z τ) τ ∂μ)) :
    ∑ y ∈ s, C * ∑' z, a z * ∫ τ, S.indicator (fun τ => P z τ * Hy y z τ) τ ∂μ =
      C * ∑' z, a z * ∫ τ, S.indicator (fun τ => P z τ * Hc z τ) τ ∂μ := by
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum hsm]
  congr 1
  refine tsum_congr fun z => ?_
  rw [← Finset.mul_sum, ← integral_finsetSum s (fun y hy => hint y hy z)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  by_cases hτ : τ ∈ S
  · simp only [Set.indicator_of_mem hτ]
    rw [← Finset.mul_sum, hsum z τ]
  · simp only [Set.indicator_of_notMem hτ, Finset.sum_const_zero]

section Outer
variable {ι : Type*} {J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J] {κ : J → Type*}
  [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] {Us : UnitSplit ι J κ} {p : ℕ} {kind : Bool}

/-- The integrand of S2's per-mode outer form `outerValM` (RepOuterM), at the decoration `z` and the times `τ`. -/
@[expose] noncomputable def outerIntegrandM {d : ℕ} (G : Garden w) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GBranch G.tree → ℕ) (hS : G.IsPlain)
    (amp : ReplacementSlot G → Mom d → ℂ) (frq : ReplacementSlot G → Fin 2 → ℤ)
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J) (hclk : J → Fin 3 → ClkSrc G) (hmom : J → Fin 4 → GNode G.tree)
    (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) (z : GenDecoration G d roots 0) (τ : GBranch G.tree → ℝ) : ℂ :=
  (splicedTimeDomain G layer tt).indicator (fun τ =>
    phaseProd L γ δ G (cosetDecoration G L base z.1) τ *
      (∏ s, amp s (base + latticePoint L (z.1 (slotNode hS s)))) * routedPhase frq route tt τ *
      ∏ j, HkM j (modLam frq route j) (fun c => clockOf G tt τ (hclk j c))
        (fun c => base + latticePoint L (z.1 (hmom j c)))) τ

/-- **The class sum of the per-mode outer form** (INTERFACE v2, step 3, right-hand side): for unit factors of the class
members that are functions of the unit coordinates, `Σ_{y ∈ τ} outerValM(HkM_y) = outerValM(Σ-class factors)`, given the
integrability of each member's integrand and the summability of each member's decoration sum. -/
theorem sum_classU_outerValM {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)) {d : ℕ} (G : Garden w) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GBranch G.tree → ℕ) (hinges : Finset (GBranch G.tree))
    (Zw : GenDecoration G d roots 0 → ℝ) (hS : G.IsPlain) (amp : ReplacementSlot G → Mom d → ℂ)
    (frq : ReplacementSlot G → Fin 2 → ℤ) (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J)
    (hclk : J → Fin 3 → ClkSrc G) (hmom : J → Fin 4 → GNode G.tree)
    (HkMy : UState w Us → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ)
    (gk : ∀ j, ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → (Σ X : FamilyReconstruction w (κ j), ChainAt X.skeleton X.family) → ℂ)
    (hfg : ∀ y ∈ classU Us p kind A us, ∀ j lam t k, HkMy y j lam t k = gk j lam t k (classProd Us p kind A us y j))
    (hint : ∀ y ∈ classU Us p kind A us, ∀ z,
      Integrable (outerIntegrandM G L γ δ base roots tt layer hS amp frq route hclk hmom (HkMy y) z))
    (hsm : ∀ y ∈ classU Us p kind A us, Summable (fun z : GenDecoration G d roots 0 =>
      (splicedEpsilon G hinges z.1 : ℂ) * (Zw z : ℂ) *
        ∫ τ, outerIntegrandM G L γ δ base roots tt layer hS amp frq route hclk hmom (HkMy y) z τ)) :
    ∑ y ∈ classU Us p kind A us,
        outerValM G L γ δ base roots tt layer hinges Zw hS amp frq route hclk hmom (HkMy y) =
      outerValM G L γ δ base roots tt layer hinges Zw hS amp frq route hclk hmom
        (fun j lam t k => ∑ x ∈ canonFinsetK p kind (Us.st A j) (Us.reg us j), gk j lam t k x) := by
  unfold outerValM
  refine sum_outer_core _ volume _ (fun z => (splicedEpsilon G hinges z.1 : ℂ) * (Zw z : ℂ))
    (splicedTimeDomain G layer tt)
    (fun z τ => phaseProd L γ δ G (cosetDecoration G L base z.1) τ *
      (∏ s, amp s (base + latticePoint L (z.1 (slotNode hS s)))) * routedPhase frq route tt τ)
    (fun y z τ => ∏ j, HkMy y j (modLam frq route j) (fun c => clockOf G tt τ (hclk j c))
        (fun c => base + latticePoint L (z.1 (hmom j c))))
    (fun z τ => ∏ j, ∑ x ∈ canonFinsetK p kind (Us.st A j) (Us.reg us j), gk j (modLam frq route j)
        (fun c => clockOf G tt τ (hclk j c)) (fun c => base + latticePoint L (z.1 (hmom j c))) x)
    (fun z τ => sum_classU_prod hA us _ _ fun y hy j => hfg y hy j _ _ _) hint hsm

/-- **The kernel instance** (INTERFACE v2): the unit factor of a class member is its recentered modulated unit kernel
`K̃^{U_j,(λ)}_{(y)}` (`W = modW λ`, the modulation `e^{πiλτ_{b_j}}`, R58); the class factor is the recentered modulated
class kernel over V5's class of the unit. -/
theorem sum_classU_outerValM_kernel {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)) {d : ℕ} (G : Garden w) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GBranch G.tree → ℕ) (hinges : Finset (GBranch G.tree))
    (Zw : GenDecoration G d roots 0 → ℝ) (hS : G.IsPlain) (amp : ReplacementSlot G → Mom d → ℂ)
    (frq : ReplacementSlot G → Fin 2 → ℤ) (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J)
    (hclk : J → Fin 3 → ClkSrc G) (hmom : J → Fin 4 → GNode G.tree) (F : J → ℕ → Mom d → ℝ)
    (hint : ∀ y ∈ classU Us p kind A us, ∀ z,
      Integrable (outerIntegrandM G L γ δ base roots tt layer hS amp frq route hclk hmom
        (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F j) base (modW lam) (t 0) (t 1) (t 2)
          (k 0) (k 1) (k 2) (k 3)) z))
    (hsm : ∀ y ∈ classU Us p kind A us, Summable (fun z : GenDecoration G d roots 0 =>
      (splicedEpsilon G hinges z.1 : ℂ) * (Zw z : ℂ) *
        ∫ τ, outerIntegrandM G L γ δ base roots tt layer hS amp frq route hclk hmom
          (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F j) base (modW lam) (t 0) (t 1) (t 2)
            (k 0) (k 1) (k 2) (k 3)) z τ)) :
    ∑ y ∈ classU Us p kind A us,
        outerValM G L γ δ base roots tt layer hinges Zw hS amp frq route hclk hmom
          (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F j) base (modW lam) (t 0) (t 1) (t 2)
            (k 0) (k 1) (k 2) (k 3)) =
      outerValM G L γ δ base roots tt layer hinges Zw hS amp frq route hclk hmom
        (fun j lam t k => twistedRecenteredW A.skeleton (us j).blk.a (canonFinsetK p kind (Us.st A j) (Us.reg us j))
          L γ δ (F j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) := by
  rw [sum_classU_outerValM hA us G L γ δ base roots tt layer hinges Zw hS amp frq route hclk hmom _
    (fun j lam t k x => recPhase (A.skeleton.sign (us j).blk.a.toNode) L γ δ (t 0) (k 0) (k 1) (k 2) (k 3) *
      twistedLocalKernelW x.1 x.2 L γ δ (F j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))
    (fun y hy j lam t k => by
      obtain ⟨M, _, hR⟩ := (mem_classU hA).mp hy
      unfold unitRecenteredW
      rw [hR.sign_upper j, unitKernelW_classProd hA ((mem_classU hA).mp hy) j])
    hint hsm]
  congr 1
  funext j lam t k
  unfold twistedRecenteredW
  rw [Finset.mul_sum]

end Outer

end WaveTurbulence.VineC
