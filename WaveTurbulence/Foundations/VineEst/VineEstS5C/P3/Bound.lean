/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P3.Unroll

/-! # P3 EXPORT: `unrolled_bound` (V5 Step 4d part C)

The observable `termFn lv ψ s tt E = c ζ lkRaw ψ tt (sumintBoundary s E)` of a summand `ψ`; `clsFn lv s` the class sum with the boundary
parameters `sumintBoundary s E`.  `clsFn_eq_sum_terms`: on the window, `clsFn` is the sum of `termFn ψ` over the unrolled terms.
**`unrolled_bound`**: the abstract per-term bound `TermBound` (to be delivered by the engine, one clocked expression per term) gives
`XNorm00Restr θ B K (clsFn) ≤ (cc θ q + 1) * (#terms * β)`; `unrolled_bound_pow`: `#terms ≤ N ^ #members`; `unrolled_bound_gain`: the
gain `L^{-η² b}` of a term bound `C L^{-η² b}` combines with `N ^ #members`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P3
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C
open scoped ENNReal

theorem list_sum_eq_fin {α : Type*} (l : List α) (g : α → ℂ) : (l.map g).sum = ∑ j : Fin l.length, g l[j] := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    exact (Fin.sum_univ_succ (fun j : Fin (l.length + 1) => g (a :: l)[j])).symm

theorem multiset_sum_eq_fin {α : Type*} (m : Multiset α) (g : α → ℂ) :
    (m.map g).sum = ∑ j : Fin m.toList.length, g m.toList[j] := by
  conv_lhs => rw [← Multiset.coe_toList m]
  rw [Multiset.map_coe, Multiset.sum_coe]
  exact list_sum_eq_fin _ _

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}

/-- The constant `c ζ` of a level. -/
noncomputable def Lvl.cst (κ0 : KPar d) (lv : Lvl B) : ℂ :=
  (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region

/-- The observable of a summand: `c ζ lkRaw ψ` at the exterior clocks `tt` and the boundary `sumintBoundary s E`. -/
noncomputable def termFn (κ0 : KPar d) (lv : Lvl B) (ψ : PsiT G d) (s : ℤˣ) : (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ :=
  fun tt E => Lvl.cst B κ0 lv * lkRaw lv.region κ0.L κ0.base ψ tt (sumintBoundary s E)

theorem vec3_eta (tt : Fin 3 → ℝ) : ![tt 0, tt 1, tt 2] = tt := by
  ext i; fin_cases i <;> rfl

theorem vec4_eta' {E : Type*} (v : Fin 4 → E) : ![v 0, v 1, v 2, v 3] = v := by
  ext i; fin_cases i <;> rfl

variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

end WaveTurbulence.VineEstS5C.P3
