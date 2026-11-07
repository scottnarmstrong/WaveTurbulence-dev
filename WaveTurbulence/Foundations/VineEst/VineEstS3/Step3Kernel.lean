/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.EpsLabels
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Engine
public import WaveTurbulence.Foundations.VineEst.VineEstS2.VineChainSumintForm

/-! # Step 3: V4's recentered kernel is `(δ/2L^{d-γ})^{n₁} ζ · clockedExprEps`

On the `sumint` output set the boundary vector is `sumintBoundary ζ (w̲ + β)` for an integer `β` with the gap relation
(`outSet_exists_beta`), and V4's endpoint `vineChain_eq_sumintForm` together with `clRegionalEpsilon_eq_epsOf` and
`clockedIntegrand_assembly` identifies the kernel with `coupling^{n₁} ζ · clockedExprEps` (`kernel_eq_clockedExprEps`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine VineParamContract
  TTree Reg Reg.Skeleton RegRed MeasureTheory
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem sumintBoundary_invol {E : Type*} (ζ : ℤˣ) (β : Fin 4 → E) :
    sumintBoundary ζ (sumintBoundary ζ β) = β := by
  funext c
  simp only [sumintBoundary, boundaryPerm_involutive]

/-- A point of the `sumint` output set is `sumintBoundary ζ (w̲ + β)` for an integer `β` with the gap relation. -/
theorem outSet_exists_beta {L : ℝ} (hL : L ≠ 0) (ζ : ℤˣ) (wBar : Mom d) (E : Fin 4 → Mom d)
    (hE : ∀ c, ∃ nv : Fin d → ℤ, E c = wBar + latticePoint L nv) (hgap : E 0 - E 1 = E 3 - E 2) :
    ∃ β : Fin 4 → (Fin d → ℤ), ((ζ : ℤ) • (β 0 - β 1) = β 2 - β 3) ∧
      E = sumintBoundary ζ (fun j => wBar + latticePoint L (β j)) := by
  choose nv hnv using hE
  refine ⟨fun j => nv (sumintBoundaryPermutation ζ j), ?_, ?_⟩
  · have hinj := latticePoint_injective_of_ne_zero (d := d) hL
    apply hinj
    have h : latticePoint L (nv 0) - latticePoint L (nv 1) = latticePoint L (nv 3) - latticePoint L (nv 2) := by
      have := hgap
      rw [hnv 0, hnv 1, hnv 2, hnv 3] at this
      simpa using this
    rcases Int.units_eq_one_or ζ with rfl | rfl
    · simp only [sumintBoundaryPermutation, ite_true, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 4) ≠ 0) (by decide : (2 : Fin 4) ≠ 1),
        Equiv.swap_apply_of_ne_of_ne (by decide : (3 : Fin 4) ≠ 0) (by decide : (3 : Fin 4) ≠ 1),
        Units.val_one, one_smul]
      rw [latticePoint_sub, latticePoint_sub, ← neg_sub, h]; abel
    · have hn : (-1 : ℤˣ) ≠ 1 := by decide
      simp only [sumintBoundaryPermutation, hn, ite_false, Equiv.refl_apply, Units.val_neg, Units.val_one,
        neg_one_smul]
      rw [show -(nv 0 - nv 1) = nv 1 - nv 0 by abel, latticePoint_sub, latticePoint_sub, ← neg_sub, h]; abel
  · funext c
    simp only [sumintBoundary, boundaryPerm_involutive]
    exact hnv c

/-- **The kernel as `coupling^{n₁} ζ · clockedExprEps`** at points of the `sumint` output set. -/
theorem kernel_eq_clockedExprEps (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer)
    (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hc : W.constraints = assemblyTimeConstraints hM9 B)
    (hb1 : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching)
    (hb2 : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching)
    (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d)
    (hE : ∀ c, ∃ nv : Fin d → ℤ, E c = W.wBar + latticePoint L nv) (hgap : E 0 - E 1 = E 3 - E 2) :
    clRecenteredLocalKernel RD hG R L γ δ F layer hLayer W.wBar (tt 0) (tt 1) (tt 2)
        (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3) =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        clockedExprEps (fun v : ↥U => childLabel hM9 B hG v.1 0) (fun v : ↥U => childLabel hM9 B hG v.1 1)
          (fun v : ↥U => childLabel hM9 B hG v.1 2) (assemblyClockedS hM9 B RD hG W L γ δ F layer hLayer)
          (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) (assemblyShape_I_pos hM9 B) L γ (2 * δ) η tt E := by
  obtain ⟨β, hβ, rfl⟩ := outSet_exists_beta hL (G.sign a.toNode) W.wBar E hE hgap
  have hfun : (fun c => sumintBoundary (G.sign a.toNode)
      (sumintBoundary (G.sign a.toNode) (fun j => W.wBar + latticePoint L (β j))) c) =
      fun j => W.wBar + latticePoint L (β j) := by
    rw [sumintBoundary_invol]
  have h0 := vineChain_eq_sumintForm hM9 B RD hG W hpar hbad hL γ δ η F layer hLayer hq hc hb1 hb2 W.wBar β hβ tt
  have e0 : sumintBoundary (G.sign a.toNode)
      (sumintBoundary (G.sign a.toNode) (fun j => W.wBar + latticePoint L (β j))) 0 =
      W.wBar + latticePoint L (β 0) := by rw [sumintBoundary_invol]
  have e1 : sumintBoundary (G.sign a.toNode)
      (sumintBoundary (G.sign a.toNode) (fun j => W.wBar + latticePoint L (β j))) 1 =
      W.wBar + latticePoint L (β 1) := by rw [sumintBoundary_invol]
  have e2 : sumintBoundary (G.sign a.toNode)
      (sumintBoundary (G.sign a.toNode) (fun j => W.wBar + latticePoint L (β j))) 2 =
      W.wBar + latticePoint L (β 2) := by rw [sumintBoundary_invol]
  have e3 : sumintBoundary (G.sign a.toNode)
      (sumintBoundary (G.sign a.toNode) (fun j => W.wBar + latticePoint L (β j))) 3 =
      W.wBar + latticePoint L (β 3) := by rw [sumintBoundary_invol]
  rw [e0, e1, e2, e3, h0]
  unfold clockedExprEps
  congr 1
  refine tsum_congr fun x => ?_
  rw [clRegionalEpsilon_eq_epsOf hM9 B hG W hL W.wBar β hβ x]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  exact (clockedIntegrand_assembly hM9 B RD hG W L γ δ F layer hLayer _ _ γ (2 * δ) η x _ tt τ).symm

end WaveTurbulence.VineEstS3
