/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P3.Count

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

/-- The class sum of a level as a function of the exterior clocks `tt` and the boundary `E`. -/
noncomputable def clsFn (κ0 : KPar d) (lv : Lvl B) (s : ℤˣ) : (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ :=
  fun tt E => lv.classSum (p := p) (kind := kind) B RD hG layer hLayer κ0 (tt 0) (tt 1) (tt 2)
    (sumintBoundary s E 0) (sumintBoundary s E 1) (sumintBoundary s E 2) (sumintBoundary s E 3)

theorem vec3_eta (tt : Fin 3 → ℝ) : ![tt 0, tt 1, tt 2] = tt := by
  ext i; fin_cases i <;> rfl

theorem vec4_eta' {E : Type*} (v : Fin 4 → E) : ![v 0, v 1, v 2, v 3] = v := by
  ext i; fin_cases i <;> rfl

variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

/-- The class sum is the sum of the term observables, for exterior data whose clock domains lie in the window. -/
theorem clsFn_eq_sum_terms (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (lv : Lvl B) (s : ℤˣ)
    (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d)
    (hWin : ∀ κ : CLLocalDecoration lv.region κ0.L κ0.base (sumintBoundary s E), ∀ᵐ τ : CLInternalTime lv.region,
      Lvl.winOf (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv (clExtendIndices lv.region κ.1) tt
        (clLocalClock lv.region tt τ))
    (habs : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv,
      LkAbs lv.region κ0.L κ0.base ψ tt (sumintBoundary s E)) :
    clsFn (p := p) (kind := kind) B RD hG layer hLayer κ0 lv s tt E =
      ((Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv).map fun ψ => termFn B κ0 lv ψ s tt E).sum := by
  classical
  have hflat := Lvl.classSum_eq_flat (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hF hprime lv (tt 0) (tt 1) (tt 2)
    (sumintBoundary s E 0) (sumintBoundary s E 1) (sumintBoundary s E 2) (sumintBoundary s E 3)
  rw [vec3_eta, vec4_eta'] at hflat
  set T := Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv with hT
  have hmem : ∀ j : Fin T.toList.length, T.toList[j] ∈ T := fun j => Multiset.mem_toList.mp (List.getElem_mem j.2)
  have hlk := lkRaw_finsum lv.region κ0.L κ0.base
    (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (Fintype.card lv.ι + 1) lv) (fun j : Fin T.toList.length => T.toList[j])
    tt (sumintBoundary s E)
    (fun κ => (hWin κ).mono fun τ hτ => by
      rw [Lvl.psiFuel_eq_terms (p := p) (kind := kind) B RD hG layer hLayer BE _ _ _ _ _ hτ, multiset_sum_eq_fin])
    (fun j => habs _ (hmem j))
  show lv.classSum (p := p) (kind := kind) B RD hG layer hLayer κ0 (tt 0) (tt 1) (tt 2) (sumintBoundary s E 0) (sumintBoundary s E 1)
      (sumintBoundary s E 2) (sumintBoundary s E 3) = _
  rw [hflat, hlk, multiset_sum_eq_fin, Finset.mul_sum]
  rfl

/-- **P3 EXPORT.**  The class sum of a level `lv` satisfies the order-zero restriction bound `(cc + 1) * (#terms * β)`, where `β` bounds the
observable of every unrolled term (`TermBound`, the engine bound of one clocked expression per term, supplied by P2/P4). -/
theorem unrolled_bound (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (lv : Lvl B) (s : ℤˣ)
    {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q) {K : Set (Fin 4 → Mom d)} (hK : K.Countable)
    (hWin : ∀ tt ∈ Bx, ∀ E ∈ K, ∀ κ : CLLocalDecoration lv.region κ0.L κ0.base (sumintBoundary s E), ∀ᵐ τ : CLInternalTime lv.region,
      Lvl.winOf (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv (clExtendIndices lv.region κ.1) tt
        (clLocalClock lv.region tt τ))
    (habs : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv, ∀ tt ∈ Bx, ∀ E ∈ K,
      LkAbs lv.region κ0.L κ0.base ψ tt (sumintBoundary s E))
    (β : ℝ≥0∞)
    (TermBound : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv,
      XNorm00Restr θ Bx K (termFn B κ0 lv ψ s) ≤ β) :
    XNorm00Restr θ Bx K (clsFn (p := p) (kind := kind) B RD hG layer hLayer κ0 lv s) ≤
      (cutoffMultiplierConstant θ (cutQ q) + 1) *
        ((Multiset.card (Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv) : ℝ≥0∞) * β) := by
  classical
  set T := Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv with hT
  have hmem : ∀ j : Fin T.toList.length, T.toList[j] ∈ T := fun j => Multiset.mem_toList.mp (List.getElem_mem j.2)
  have h1 := XNorm00Restr_finsum_le hθ q hBx hK (fun j : Fin T.toList.length => termFn B κ0 lv T.toList[j] s)
    (clsFn (p := p) (kind := kind) B RD hG layer hLayer κ0 lv s) (fun tt htt E hE => by
      rw [clsFn_eq_sum_terms (p := p) (kind := kind) B RD hG layer hLayer BE hL hF lv s tt E (hWin tt htt E hE) (fun ψ hψ => habs ψ hψ tt htt E hE),
        multiset_sum_eq_fin])
  refine h1.trans (mul_le_mul' le_rfl ?_)
  calc ∑ j : Fin T.toList.length, XNorm00Restr θ Bx K (termFn B κ0 lv T.toList[j] s)
      ≤ ∑ _j : Fin T.toList.length, β := Finset.sum_le_sum fun j _ => TermBound _ (hmem j)
    _ = (Multiset.card T : ℝ≥0∞) * β := by
        simp [Finset.sum_const, nsmul_eq_mul, Multiset.length_toList]

/-- `unrolled_bound` with the count `#terms ≤ N ^ #members` of `Lvl.card_terms_le`. -/
theorem unrolled_bound_pow (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (lv : Lvl B) (s : ℤˣ)
    {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q) {K : Set (Fin 4 → Mom d)} (hK : K.Countable)
    (hWin : ∀ tt ∈ Bx, ∀ E ∈ K, ∀ κ : CLLocalDecoration lv.region κ0.L κ0.base (sumintBoundary s E), ∀ᵐ τ : CLInternalTime lv.region,
      Lvl.winOf (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv (clExtendIndices lv.region κ.1) tt
        (clLocalClock lv.region tt τ))
    (habs : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv, ∀ tt ∈ Bx, ∀ E ∈ K,
      LkAbs lv.region κ0.L κ0.base ψ tt (sumintBoundary s E))
    (N : ℕ) (hN : 1 ≤ N)
    (hCh : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), Fintype.card (BE lv pstar hk).Ch ≤ N)
    (β : ℝ≥0∞)
    (TermBound : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv,
      XNorm00Restr θ Bx K (termFn B κ0 lv ψ s) ≤ β) :
    XNorm00Restr θ Bx K (clsFn (p := p) (kind := kind) B RD hG layer hLayer κ0 lv s) ≤
      (cutoffMultiplierConstant θ (cutQ q) + 1) * (((N ^ Fintype.card lv.ι : ℕ) : ℝ≥0∞) * β) := by
  refine (unrolled_bound (p := p) (kind := kind) B RD hG layer hLayer BE hL hF lv s hθ q hBx hK hWin habs β TermBound).trans ?_
  refine mul_le_mul' le_rfl (mul_le_mul' ?_ le_rfl)
  exact_mod_cast Lvl.card_terms_le (p := p) (kind := kind) B RD hG layer hLayer BE N hN hCh _ lv (Nat.le_succ _ |>.trans' le_rfl |>.trans' le_rfl)

/-- The gain form: a term bound `C * L^{-(η² b)}` (the engine's bad-vine gain, `b` the number of bad vines, the same for every term by
invariance of the shape data) and `#terms ≤ N ^ #members` give `(cc+1) * C * (N^{#members} * L^{-η² b})`, with the `L^{-η²}` per bad
vine kept as a separate real factor. -/
theorem unrolled_bound_gain (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (lv : Lvl B) (s : ℤˣ)
    {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q) {K : Set (Fin 4 → Mom d)} (hK : K.Countable)
    (hWin : ∀ tt ∈ Bx, ∀ E ∈ K, ∀ κ : CLLocalDecoration lv.region κ0.L κ0.base (sumintBoundary s E), ∀ᵐ τ : CLInternalTime lv.region,
      Lvl.winOf (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv (clExtendIndices lv.region κ.1) tt
        (clLocalClock lv.region tt τ))
    (habs : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv, ∀ tt ∈ Bx, ∀ E ∈ K,
      LkAbs lv.region κ0.L κ0.base ψ tt (sumintBoundary s E))
    (N : ℕ) (hN : 1 ≤ N)
    (hCh : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), Fintype.card (BE lv pstar hk).Ch ≤ N)
    (Cterm Lg : ℝ) (hC : 0 ≤ Cterm) (nbad : ℕ)
    (TermBound : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv,
      XNorm00Restr θ Bx K (termFn B κ0 lv ψ s) ≤ ENNReal.ofReal (Cterm * Lg ^ nbad)) :
    XNorm00Restr θ Bx K (clsFn (p := p) (kind := kind) B RD hG layer hLayer κ0 lv s) ≤
      (cutoffMultiplierConstant θ (cutQ q) + 1) *
        ENNReal.ofReal ((N : ℝ) ^ Fintype.card lv.ι * (Cterm * Lg ^ nbad)) := by
  refine (unrolled_bound_pow (p := p) (kind := kind) B RD hG layer hLayer BE hL hF lv s hθ q hBx hK hWin habs N hN hCh _ TermBound).trans ?_
  refine mul_le_mul' le_rfl (le_of_eq ?_)
  have hNe : (((N ^ Fintype.card lv.ι : ℕ) : ℝ≥0∞)) = ENNReal.ofReal ((N : ℝ) ^ Fintype.card lv.ι) := by
    rw [ENNReal.ofReal_pow (by positivity)]; simp
  rw [hNe, ← ENNReal.ofReal_mul (by positivity)]

end WaveTurbulence.VineEstS5C.P3
