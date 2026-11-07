/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.GenMerge
public import WaveTurbulence.Foundations.VineEst.VineEstS4.BaseCase
public import WaveTurbulence.Foundations.VineEst.VineEstS4.CanonStatement

/-! # The base case of the induction over the core vines, and the native summand as an abstract summand (WP-I)

`psiNat`: the native local summand of a CL region as a function of the decoration, the exterior clocks and the clock
(`clLocalKernel_eq_lkRaw`: `K^R = c ζ lkRaw R psiNat`).  `lkRaw_idx`: region index congruence.  `canonFinset_of_noop`: with no LF
operation at `A`, the class is `{(A, c)}` (any state, any chain region).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- The time-domain condition of a CL region as a predicate on the clock. -/
def ClDom (R : CLRegionData G U a b) (layer0 : GBranch G.tree → ℕ) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) : Prop :=
  (∀ v ∈ clInteriorBranches R, (layer0 v : ℝ) < u v ∧ u v < layer0 v + 1 ∧ 0 < u v ∧ u v < parentClock (t 0) u v.toNode) ∧
    ((b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching → t 1 < u b) ∧
    ((b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching → t 2 < u b)

theorem mem_clLocalTimeDomain_iff (R : CLRegionData G U a b) (layer0 : GBranch G.tree → ℕ) (t : Fin 3 → ℝ)
    (τ : CLInternalTime R) : τ ∈ clLocalTimeDomain R layer0 t ↔ ClDom R layer0 t (clLocalClock R t τ) := by
  unfold clLocalTimeDomain ClDom
  simp only [Set.mem_setOf_eq]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro h v hv
    have := h ⟨v, hv⟩
    rwa [clLocalClock_internal R t τ ⟨v, hv⟩]
  · intro h v
    have := h v.1 v.2
    rwa [clLocalClock_internal R t τ v] at this


open Classical in
/-- The native summand of a CL region as a function of the decoration, the exterior clocks and the clock. -/
noncomputable def psiNat (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b) (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) : ℂ :=
  (clRegionalEpsilon G U x : ℂ) *
    (if ClDom R (fun v => layer (D.coreBranch hG v).toNode) t u then
      clRegionalPhase G U L γ δ (cosetDecoration G L base x) u *
        starProd D hG L γ δ F layer hLayer base U a (t 0) x u else 0)

open Classical in
theorem clLocalSummand_eq_psiNat (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b) (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (β : Fin 4 → Mom d) (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base β) (τ : CLInternalTime R) :
    clLocalSummand D hG R L γ δ F layer hLayer base β t κ τ =
      psiNat D hG R L γ δ F layer hLayer base (clExtendIndices R κ.1) t (clLocalClock R t τ) := by
  unfold clLocalSummand psiNat
  by_cases hτ : τ ∈ clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t
  · rw [Set.indicator_of_mem hτ, if_pos ((mem_clLocalTimeDomain_iff R _ t τ).mp hτ)]
    rw [clLocalStarProduct_eq]
  · rw [Set.indicator_of_notMem hτ, if_neg (fun h => hτ ((mem_clLocalTimeDomain_iff R _ t τ).mpr h))]

theorem clLocalKernel_eq_lkRaw (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b) (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    clLocalKernel D hG R L γ δ F layer hLayer base t0 t1 t2 e f g h =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        lkRaw R L base (psiNat D hG R L γ δ F layer hLayer base) ![t0, t1, t2] ![e, f, g, h] := by
  unfold clLocalKernel lkRaw
  congr 1
  refine tsum_congr fun κ => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  exact clLocalSummand_eq_psiNat D hG R L γ δ F layer hLayer base _ _ κ τ

/-- Region index congruence for `lkRaw`. -/
theorem lkRaw_idx {U U' : Finset (GBranch G.tree)} {a a' b b' : GBranch G.tree} (hU : U = U') (ha : a = a') (hb : b = b')
    (R : CLRegionData G U a b) (R' : CLRegionData G U' a' b') (L : ℝ) (base : Mom d)
    (Ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ) (t : Fin 3 → ℝ) (β : Fin 4 → Mom d) :
    lkRaw R L base Ψ t β = lkRaw R' L base Ψ t β := by
  subst hU ha hb
  rw [regionData_subsingleton R R']


section NoOp
variable {ι : Type*} [Fintype ι] {p : ℕ}

/-- With no LF operation available at `A`, the start is the only section. -/
theorem classSection_of_noop (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family)
    (hno : ∀ i, IsEmpty (FamilyOperation (p := p) (kind := kind) A i)) :
    ClassSectionK p kind A c {⟨A, c⟩} := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact ⟨_, List.Perm.refl _, reach_skips _ _⟩
  · intro x hx y hy _
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
    rw [hx, hy]
  · ext LH
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx
      subst hx
      exact FamilyReconstruction.mem_outputs _ _
    · rintro ⟨M, B', _, hB, rfl⟩
      refine ⟨⟨A, c⟩, by simp, ?_⟩
      rw [batch_eq_of_noOperation hB hno]

theorem canonFinset_of_noop [DecidableEq ι] (A : FamilyReconstruction w ι) (hA : IsPrimeGarden A.skeleton)
    (c : ChainAt A.skeleton A.family) (hno : ∀ i, IsEmpty (FamilyOperation (p := p) (kind := kind) A i)) :
    canonFinsetK p kind A c = {⟨A, c⟩} :=
  (classSection_eq hA (classSection_of_noop A c hno)).symm

end NoOp

end WaveTurbulence.VineEstS5C
