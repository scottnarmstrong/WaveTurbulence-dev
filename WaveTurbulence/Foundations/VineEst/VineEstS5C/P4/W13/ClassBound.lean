/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.EngineRHS
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.WinChain

/-! # P4-W1W3: the class sum of the top level in the literal form (W1 + W3 assembled with P4's unrolled bound)

`wpF_class`: with the bundle family `bundleFamOf hR (sffOf E hord)` (W1: separated expansions from the gates; `winOfExt_bundleFamOf`
for design R), the unrolled class sum of the top level on a closed box of the output clocks obeys

  `‖clsFnR (Lvl.top B)‖_{𝔛^{2η⁸,0,0}(Bx × K)} ≤ Λ (C₁√δ)^{n₍₂₎} Lp lf C₂^b`

from a uniform term bound `β ≤ Λ (Nₛ√δ)^{n₍₂₎} Lp lf` of the unrolled terms (W2, e.g. through `engine_rhs`), the count
(`card_terms_le_wt` with `sffOf_bounded`, then `card_le_count`), and `C₁ ≥ (ccη+1)·32·12⁹·Nₛ`, `C₂ ≥ 192·4^𝔇` (`wpF_top`).  It is the
twisted case of the prefix theorem (W4) up to the identification of the integrand (`twistedRecentered_eq_clsFnR`; for `λ ≠ 0`,
FLAT-MOD) and the psiBot terms (BOT-DECOMP, R60: the count hypothesis of `wpF_top` is the only place where the term multiset enters).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W13
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4
open scoped ENNReal

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {P : WTParams} {κ0 : KPar P.d} {Bh : ℕ → ℝ} {hprime : IsPrimeGarden G}

/-- **The top-level class sum in the literal form** (W1 + W3 with P4's `top_boundR`). -/
theorem wpF_class (hM9 : VINEPARAM) (hR : RealityAll) (E : GateEnv P κ0 p Bh) (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4)
    (σ : ℤˣ) (hL : κ0.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin P.d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (s : ℤˣ) {η : ℝ} (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q) {K : Set (Fin 4 → Mom P.d)}
    (hK : K.Countable)
    (hq : ∀ tt ∈ Bx, (layer (RD.coreBranch hG a).toNode : ℝ) ≤ tt 0 ∧ tt 0 ≤ layer (RD.coreBranch hG a).toNode + 1)
    (habs : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer
        (bundleFamOf B RD hG layer hLayer hR (sffOf (hprime := hprime) B RD hG layer hLayer E hord))
        (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B), ∀ tt ∈ Bx, ∀ E' ∈ K,
      LkAbs (Lvl.top B).region κ0.L κ0.base ψ tt (sumintBoundary s E'))
    {Λ Ns δ Lp lf C₁ C₂ : ℝ} {D : ℕ} (hpD : p ≤ D)
    (hTB : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer
        (bundleFamOf B RD hG layer hLayer hR (sffOf (hprime := hprime) B RD hG layer hLayer E hord))
        (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B),
      XNorm00Restr (2 * η ^ 8) Bx K (termFnR B σ κ0 (Lvl.top B) ψ s) ≤
        ENNReal.ofReal (Λ * ((Ns * Real.sqrt δ) ^ clLocalOrder2 RD hG R * Lp * lf)))
    (hΛ : 0 ≤ Λ) (hNs : 0 ≤ Ns) (hLp : 0 ≤ Lp) (hlf : 0 ≤ lf)
    (hC₁ : (Eng.ccη η + 1).toReal * countKc * Ns ≤ C₁) (hC₂ : (countKp D : ℝ) ≤ C₂) :
    XNorm00Restr (2 * η ^ 8) Bx K (clsFnR (p := p) (kind := kind) B RD hG layer hLayer σ κ0 (Lvl.top B) s) ≤
      ENNReal.ofReal (Λ * ((C₁ * Real.sqrt δ) ^ clLocalOrder2 RD hG R * Lp * lf *
        C₂ ^ (Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card)) := by
  have hX := top_boundR (p := p) (kind := kind) B RD hG layer hLayer
    (bundleFamOf B RD hG layer hLayer hR (sffOf (hprime := hprime) B RD hG layer hLayer E hord))
    (winOfExt_bundleFamOf B RD hG layer hLayer hR _) σ hL hF s (θ := 2 * η ^ 8) (by positivity) q hBx hK hq habs _ hTB
  exact wpF_top B RD hG layer hLayer hM9 q hpD (Lvl.top B)
    (card_terms_le_wt B RD hG layer hLayer hR _ (sffOf_bounded B RD hG layer hLayer E hord) _ (Lvl.top B) (Nat.le_succ _))
    hX le_rfl hΛ hNs hLp hlf hC₁ hC₂

end WaveTurbulence.VineEstS5C.P4.W13
