/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P3.Bound

/-! # P2: the recentered form of `unrolled_bound` (finding F-RECENTER)

P3's `termFn`/`clsFn` are the NON-recentered kernels (`twistedLocalKernel`), whereas the engine (`clockedExprMul3`, the `sumint` form of V4)
and `VineEstCanonLayer` (`twistedRecentered`) carry the unimodular factor `recFac = exp(-πiδL^{2γ} t₀ Γ(E))`, which depends on the exterior
clock `t₀` and on the boundary momenta, so `XNorm00Restr` is NOT invariant under it.  Here: `termFnR = recFac · termFn`, and
`unrolled_bound_recentered`: the recentered class sum is the sum of the recentered terms, so the abstract per-term bound `TermBoundR` (of
`termFnR`) gives the same finite-Minkowski bound as `P3.unrolled_bound`. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P2
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2
  WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton
  WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3
open scoped ENNReal

/-- The recentering phase `exp(-πiδL^{2γ} t₀ Γ)` (`Γ` the boundary energy of the boundary `sumintBoundary s E`, with the sign `σ` of the
top joint), as in `twistedRecentered`. -/
noncomputable def recFac {d : ℕ} (σ : ℤˣ) (s : ℤˣ) (L γ δ : ℝ) (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d) : ℂ :=
  Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * tt 0 * boundaryEnergyFromMomenta σ (sumintBoundary s E 0) (sumintBoundary s E 1)
    (sumintBoundary s E 2) (sumintBoundary s E 3) : ℝ) : ℂ) * Complex.I)

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}

/-- The recentered observable of a summand. -/
noncomputable def termFnR (σ : ℤˣ) (κ0 : KPar d) (lv : Lvl B) (ψ : PsiT G d) (s : ℤˣ) : (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ :=
  fun tt E => recFac σ s κ0.L κ0.γ κ0.δ tt E * termFn B κ0 lv ψ s tt E

/-- The recentered class sum of a level. -/
noncomputable def clsFnR (σ : ℤˣ) (κ0 : KPar d) (lv : Lvl B) (s : ℤˣ) : (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ :=
  fun tt E => recFac σ s κ0.L κ0.γ κ0.δ tt E * clsFn (p := p) (kind := kind) B RD hG layer hLayer κ0 lv s tt E

variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

/-- **The recentered unrolled bound.**  As `P3.unrolled_bound`, with `termFnR`/`clsFnR` (the recentering factor is a common factor of all
terms). -/
theorem unrolled_bound_recentered (σ : ℤˣ) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (lv : Lvl B) (s : ℤˣ)
    {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q) {K : Set (Fin 4 → Mom d)} (hK : K.Countable)
    (hWin : ∀ tt ∈ Bx, ∀ E ∈ K, ∀ κ : CLLocalDecoration lv.region κ0.L κ0.base (sumintBoundary s E), ∀ᵐ τ : CLInternalTime lv.region,
      Lvl.winOf (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv (clExtendIndices lv.region κ.1) tt
        (clLocalClock lv.region tt τ))
    (habs : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv, ∀ tt ∈ Bx, ∀ E ∈ K,
      LkAbs lv.region κ0.L κ0.base ψ tt (sumintBoundary s E))
    (β : ℝ≥0∞)
    (TermBoundR : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv,
      XNorm00Restr θ Bx K (termFnR B σ κ0 lv ψ s) ≤ β) :
    XNorm00Restr θ Bx K (clsFnR (p := p) (kind := kind) B RD hG layer hLayer σ κ0 lv s) ≤
      (cutoffMultiplierConstant θ (cutQ q) + 1) *
        ((Multiset.card (Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv) : ℝ≥0∞) * β) := by
  classical
  set T := Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv with hT
  have hmem : ∀ j : Fin T.toList.length, T.toList[j] ∈ T := fun j => Multiset.mem_toList.mp (List.getElem_mem j.2)
  have h1 := XNorm00Restr_finsum_le hθ q hBx hK (fun j : Fin T.toList.length => termFnR B σ κ0 lv T.toList[j] s)
    (clsFnR (p := p) (kind := kind) B RD hG layer hLayer σ κ0 lv s) (fun tt htt E hE => by
      unfold clsFnR termFnR
      rw [clsFn_eq_sum_terms (p := p) (kind := kind) B RD hG layer hLayer BE hL hF lv s tt E (hWin tt htt E hE) (fun ψ hψ => habs ψ hψ tt htt E hE),
        multiset_sum_eq_fin, Finset.mul_sum])
  refine h1.trans (mul_le_mul' le_rfl ?_)
  calc ∑ j : Fin T.toList.length, XNorm00Restr θ Bx K (termFnR B σ κ0 lv T.toList[j] s)
      ≤ ∑ _j : Fin T.toList.length, β := Finset.sum_le_sum fun j _ => TermBoundR _ (hmem j)
    _ = (Multiset.card T : ℝ≥0∞) * β := by
        simp [Finset.sum_const, nsmul_eq_mul, Multiset.length_toList]

end WaveTurbulence.VineEstS5C.P2
