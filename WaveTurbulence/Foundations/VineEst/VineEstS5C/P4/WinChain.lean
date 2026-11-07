/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.UnrollR
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.NullSet
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelTop

/-! # P4: the exterior window at the top level, and the boundary of the clock box (V5 Step 4d part C)

The top level `Lvl.top` has the region of `U`, whose top joint is `a`; its layer is `layer (core a) = qOut 0`.  On the closed box of the
exterior clocks, `tt 0 ∈ [qOut 0, qOut 0 + 1]`; the strict window `ExtOf` of design R holds off the two hyperplanes `tt 0 = qOut 0`,
`tt 0 = qOut 0 + 1`, which are null, and `XNorm00Restr` does not see null sets of times (`XNorm00Restr_le_of_null`).

* `XNorm00Restr_mono_set`: monotonicity in the time set.
* `layOf_top`: the layer of the top joint at the top level is `layer (core a)`.
* **`top_boundR`**, **`top_boundR_prod`**: the recentered class sum of the top level on any box `Bx` whose exterior clock lies in the
  closed window `[layer (core a), layer (core a) + 1]` obeys the finite-Minkowski bound `(cc + 1) (#terms β)` (resp. with the per-vine
  count `∏ wt`), from term bounds `TermBoundR` on `Bx`.
* `kparOf`, `twistedRecentered_eq_clsFnR`: the integrand of `VineEstCanonLayer` is `clsFnR` of the top level.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P4
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal

set_option linter.unusedSectionVars false

/-- Monotonicity of the restriction norm in the time set. -/
theorem XNorm00Restr_mono_set {r : ℕ} {V : Type*} (θ : ℝ) {B B' : Set (Fin r → ℝ)} (h : B' ⊆ B) (K : Set V)
    (F : (Fin r → ℝ) → V → ℂ) : XNorm00Restr θ B' K F ≤ XNorm00Restr θ B K F := by
  unfold XNorm00Restr
  exact le_iInf₂ fun G hG => iInf₂_le G fun t ht v hv => hG t (h ht) v hv

/-- The box without the two hyperplanes `tt 0 = q₀`, `tt 0 = q₀ + 1`. -/
def openTop (Bx : Set (Fin 3 → ℝ)) (q₀ : ℝ) : Set (Fin 3 → ℝ) :=
  Bx \ ({tt | tt 0 = q₀} ∪ {tt | tt 0 = q₀ + 1})

theorem openTop_subset (Bx : Set (Fin 3 → ℝ)) (q₀ : ℝ) : openTop Bx q₀ ⊆ Bx := Set.sdiff_subset

theorem volume_diff_openTop (Bx : Set (Fin 3 → ℝ)) (q₀ : ℝ) : volume (Bx \ openTop Bx q₀) = 0 := by
  refine measure_mono_null (t := {tt : Fin 3 → ℝ | tt 0 = q₀} ∪ {tt | tt 0 = q₀ + 1}) ?_ ?_
  · intro tt ht
    by_contra hn
    exact ht.2 ⟨ht.1, hn⟩
  · exact measure_union_null (null_clock_hyperplane 0 q₀) (null_clock_hyperplane 0 (q₀ + 1))

/-- The restriction norm on `Bx` equals (is bounded by) the one on `openTop Bx q₀`. -/
theorem XNorm00Restr_le_openTop {V : Type*} (θ : ℝ) (Bx : Set (Fin 3 → ℝ)) (q₀ : ℝ) (K : Set V)
    (F : (Fin 3 → ℝ) → V → ℂ) : XNorm00Restr θ Bx K F ≤ XNorm00Restr θ (openTop Bx q₀) K F :=
  XNorm00Restr_le_of_null θ K F (volume_diff_openTop Bx q₀)

/-- Strict window off the two hyperplanes. -/
theorem strict_of_openTop {Bx : Set (Fin 3 → ℝ)} {q₀ : ℝ} (hq : ∀ tt ∈ Bx, q₀ ≤ tt 0 ∧ tt 0 ≤ q₀ + 1) :
    ∀ tt ∈ openTop Bx q₀, q₀ < tt 0 ∧ tt 0 < q₀ + 1 := by
  intro tt ht
  obtain ⟨h1, h2⟩ := hq tt ht.1
  have hn1 : tt 0 ≠ q₀ := fun h => ht.2 (Or.inl h)
  have hn2 : tt 0 ≠ q₀ + 1 := fun h => ht.2 (Or.inr h)
  exact ⟨lt_of_le_of_ne h1 (Ne.symm hn1), lt_of_le_of_ne h2 hn2⟩

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem stateLayer_startState : stateLayer (startState B RD hG layer hLayer) = layer :=
  layeredReconstruction_inj RD hG (l₁ := stateLayer (startState B RD hG layer hLayer)) (l₂ := layer)
    (h₁ := stateLayer_isLayering (startState B RD hG layer hLayer)) (h₂ := hLayer) (stateLayer_spec (startState B RD hG layer hLayer))

/-- The layer of the top joint of the top level is the layer of the core of `a` (`= qOut 0`). -/
theorem layOf_top : layOf ((Lvl.top B).state B RD hG layer hLayer) (Lvl.top B).c.a = layer (RD.coreBranch hG a).toNode := by
  show stateLayer (startState B RD hG layer hLayer) (RD.coreBranch hG a).toNode = _
  rw [stateLayer_startState]

variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

/-- **The top-level bound on a closed box** (design R plus the null boundary). -/
theorem top_boundR (hW : WinOfExt B RD hG layer hLayer BE) (σ : ℤˣ) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (s : ℤˣ)
    {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q) {K : Set (Fin 4 → Mom d)} (hK : K.Countable)
    (hq : ∀ tt ∈ Bx, (layer (RD.coreBranch hG a).toNode : ℝ) ≤ tt 0 ∧ tt 0 ≤ layer (RD.coreBranch hG a).toNode + 1)
    (habs : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B), ∀ tt ∈ Bx, ∀ E ∈ K,
      LkAbs (Lvl.top B).region κ0.L κ0.base ψ tt (sumintBoundary s E))
    (β : ℝ≥0∞)
    (TermBoundR : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B),
      XNorm00Restr θ Bx K (termFnR B σ κ0 (Lvl.top B) ψ s) ≤ β) :
    XNorm00Restr θ Bx K (clsFnR (p := p) (kind := kind) B RD hG layer hLayer σ κ0 (Lvl.top B) s) ≤
      (cutoffMultiplierConstant θ (cutQ q) + 1) *
        ((Multiset.card (Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B)) : ℝ≥0∞) * β) := by
  set q₀ : ℝ := (layer (RD.coreBranch hG a).toNode : ℝ) with hq₀
  refine (XNorm00Restr_le_openTop θ Bx q₀ K _).trans ?_
  have hsub := openTop_subset Bx q₀
  refine unrolled_boundR_ext (p := p) (kind := kind) B RD hG layer hLayer BE hW σ hL hF (Lvl.top B) s hθ q (hsub.trans hBx) hK ?_
    (fun ψ hψ tt htt E hE => habs ψ hψ tt (hsub htt) E hE) β
    (fun ψ hψ => (XNorm00Restr_mono_set θ hsub K _).trans (TermBoundR ψ hψ))
  intro tt htt
  rw [layOf_top]
  exact strict_of_openTop hq tt htt

/-- `top_boundR` with the per-vine count `#terms ≤ ∏_{members} wt`. -/
theorem top_boundR_prod (hW : WinOfExt B RD hG layer hLayer BE) (σ : ℤˣ) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (s : ℤˣ)
    {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q) {K : Set (Fin 4 → Mom d)} (hK : K.Countable)
    (hq : ∀ tt ∈ Bx, (layer (RD.coreBranch hG a).toNode : ℝ) ≤ tt 0 ∧ tt 0 ≤ layer (RD.coreBranch hG a).toNode + 1)
    (habs : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B), ∀ tt ∈ Bx, ∀ E ∈ K,
      LkAbs (Lvl.top B).region κ0.L κ0.base ψ tt (sumintBoundary s E))
    (wt : (assemblySourceFamily B).CoreIndex → ℕ) (hwt : ∀ i, 1 ≤ wt i)
    (hCh : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), Fintype.card (BE lv pstar hk).Ch ≤ wt (lv.e pstar))
    (β : ℝ≥0∞)
    (TermBoundR : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B),
      XNorm00Restr θ Bx K (termFnR B σ κ0 (Lvl.top B) ψ s) ≤ β) :
    XNorm00Restr θ Bx K (clsFnR (p := p) (kind := kind) B RD hG layer hLayer σ κ0 (Lvl.top B) s) ≤
      (cutoffMultiplierConstant θ (cutQ q) + 1) * (((∏ j, wt j : ℕ) : ℝ≥0∞) * β) := by
  refine (top_boundR (p := p) (kind := kind) B RD hG layer hLayer BE hW σ hL hF s hθ q hBx hK hq habs β TermBoundR).trans ?_
  refine mul_le_mul' le_rfl (mul_le_mul' ?_ le_rfl)
  exact_mod_cast Lvl.card_terms_le_prod (p := p) (kind := kind) B RD hG layer hLayer BE wt hwt hCh _ (Lvl.top B) (Nat.le_succ _)

/-- The kernel parameters of `VineEstCanonLayer` (the exterior times and boundary momenta of `KPar` are not read by `Lvl.classSum`). -/
def kparOf (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) : KPar d :=
  ⟨L, γ, δ, F, base, 0, 0, 0, 0, 0, 0, 0⟩

/-- **The integrand of `VineEstCanonLayer` is the recentered class sum of the top level.** -/
theorem twistedRecentered_eq_clsFnR (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (wBar : Mom d) :
    (fun (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d) => twistedRecentered G a
        (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B)) L γ δ F wBar
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) =
      clsFnR (p := p) (kind := kind) B RD hG layer hLayer (G.sign a.toNode) (kparOf L γ δ F wBar) (Lvl.top B) (G.sign a.toNode) := rfl

end WaveTurbulence.VineEstS5C.P4
