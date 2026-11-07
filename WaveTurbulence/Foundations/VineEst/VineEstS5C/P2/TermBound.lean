/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Final

/-! # P2 EXPORT: `termBound_of_pieces` and `habs_of_pieces` in the form of P3

For every unrolled term `ψ ∈ Lvl.terms BE (card ι + 1) lv` a certificate (`TermCert`): the dictionary data `T` of `ψ` over an assembly `B'` of the region of `lv`,
the engine data `Z`, a `PieceBound` and the identification `DictAll`.  Then `TermBoundR` of `P2.unrolled_bound_recentered` holds with
`β = ‖c ζ‖ · β'` and `LkAbs` (`habs` of P3) holds for every term at every point of the output set. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
variable {kind : Bool}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.VineEstS5C.P3
open scoped ENNReal

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The certificate of one unrolled term of a level `lv`: an assembly `B'` of the region of `lv` with the dictionary data `T` of `ψ`, the engine data `Z`,
a `PieceBound` with total size `β'`, and the identification `DictAll`; `Bx`, `K` are the output box and set of the engine datum. -/
def TermCert {A : ℝ} {P : WTParams} (κ0 : KPar P.d) (lv : Lvl B) (ψ : PsiT G P.d) (Bx : Set (Fin 3 → ℝ))
    (K : Set (Fin 4 → Mom P.d)) (β' : ℝ≥0∞) : Prop :=
  ∃ (n' : ℕ) (hM9 : VINEPARAM) (B' : CLChainAssembly G lv.region n') (T : TermData P hM9 B' hG) (Z : Amb A P T.D)
    (Kw Lw : (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ) (Ks Ls : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot T.D) (bK bL : ℝ≥0∞),
    T.ψ = ψ ∧ T.W.wBar = κ0.base ∧ Bx = outBox T.D ∧ K = outSet T.D P.L P.γ P.η ∧
    PieceBound Z Kw Ks Lw Ls bK bL ∧ DictAll T Z Kw Lw Ks Ls ∧ Z.pre * (bK * bL * Z.others) ≤ β'

variable {A : ℝ} {P : WTParams}

/-- **`termBound_of_pieces`**: the `TermBoundR` hypothesis of `unrolled_bound_recentered` (and of P3's `unrolled_bound`, in its recentered form), from the certificates of
all unrolled terms. -/
theorem termBound_of_pieces (κ0 : KPar P.d) (hκL : κ0.L = P.L) (hκγ : κ0.γ = P.γ) (hκδ : κ0.δ = P.δ) (lv : Lvl B)
    (σ s : ℤˣ) (hσ : σ = G.sign lv.c.a.toNode) (hs : s = σ) {Bx : Set (Fin 3 → ℝ)} {K : Set (Fin 4 → Mom P.d)} {β' : ℝ≥0∞}
    (S : Multiset (PsiT G P.d)) (hS : ∀ ψ ∈ S, TermCert (hG := hG) (A := A) B κ0 lv ψ Bx K β') :
    ∀ ψ ∈ S, XNorm00Restr (2 * P.η ^ 8) Bx K (termFnR B σ κ0 lv ψ s) ≤
      ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region‖ₑ * β' := by
  intro ψ hψ
  obtain ⟨n', hM9, B', T, Z, Kw, Lw, Ks, Ls, bK, bL, rfl, hbase, rfl, rfl, hP, hD, hβ⟩ := hS ψ hψ
  subst hs hσ
  have := termBoundR_of_piece T Z hP hD
  unfold termFnR termFn Lvl.cst
  rw [hκL, hκγ, hκδ, ← hbase]
  exact this.trans (mul_le_mul' le_rfl hβ)

/-- **`habs_of_pieces`**: `P3.LkAbs` of every certified term at every point of the output set. -/
theorem habs_of_pieces (κ0 : KPar P.d) (lv : Lvl B) (s : ℤˣ) (hs : s = G.sign lv.c.a.toNode)
    {Bx : Set (Fin 3 → ℝ)} {K : Set (Fin 4 → Mom P.d)} {β' : ℝ≥0∞} (hκL : κ0.L = P.L)
    (S : Multiset (PsiT G P.d)) (hS : ∀ ψ ∈ S, TermCert (hG := hG) (A := A) B κ0 lv ψ Bx K β') :
    ∀ ψ ∈ S, ∀ tt ∈ Bx, ∀ E ∈ K, LkAbs lv.region κ0.L κ0.base ψ tt (sumintBoundary s E) := by
  intro ψ hψ tt htt E hE
  obtain ⟨n', hM9, B', T, Z, Kw, Lw, Ks, Ls, bK, bL, rfl, hbase, rfl, rfl, hP, hD, hβ⟩ := hS ψ hψ
  subst hs
  rw [hκL, ← hbase]
  exact lkAbs_of_piece T Z hP hD tt htt E hE

variable {κ0 : KPar P.d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

/-- **The class-sum bound from the certificates of the unrolled terms** (`unrolled_bound_recentered` with `termBound_of_pieces` and `habs_of_pieces`). -/
theorem classSum_bound_of_pieces (hκL : κ0.L = P.L) (hκγ : κ0.γ = P.γ) (hκδ : κ0.δ = P.δ)
    (hF : ∀ k : ℕ, Summable fun n : Fin P.d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (lv : Lvl B) (s : ℤˣ)
    (hs : s = G.sign lv.c.a.toNode) {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)}
    (hBx : Bx ⊆ WaveTurbulence.VineEstS3.FS.cell q) {K : Set (Fin 4 → Mom P.d)} (hK : K.Countable)
    (hWin : ∀ tt ∈ Bx, ∀ E ∈ K, ∀ κ : CLLocalDecoration lv.region κ0.L κ0.base (sumintBoundary s E), ∀ᵐ τ : CLInternalTime lv.region,
      Lvl.winOf (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv (clExtendIndices lv.region κ.1) tt
        (clLocalClock lv.region tt τ))
    {β' : ℝ≥0∞}
    (hS : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv,
      TermCert (hG := hG) (A := A) B κ0 lv ψ Bx K β')
    (hθ2 : θ = 2 * P.η ^ 8) (hL0 : κ0.L ≠ 0) :
    XNorm00Restr θ Bx K (clsFnR (p := p) (kind := kind) B RD hG layer hLayer s κ0 lv s) ≤
      (WaveTurbulence.Fourier.cutoffMultiplierConstant θ (WaveTurbulence.VineEstS3.FS.cutQ q) + 1) *
        ((Multiset.card (Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv) : ℝ≥0∞) *
          (‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region‖ₑ * β')) := by
  subst hθ2
  refine unrolled_bound_recentered (p := p) (kind := kind) B RD hG layer hLayer BE s hL0 hF lv s hθ q hBx hK hWin
    (habs_of_pieces B hG κ0 lv s hs hκL _ hS) _ ?_
  exact termBound_of_pieces B hG κ0 hκL hκγ hκδ lv s s hs rfl _ hS

end WaveTurbulence.VineEstS5C.P2
