/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.BotCount
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Unroll
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.ClassBound

/-! # V5 FINAL (step 2a): the top-level class sum in the literal form with the bottom bundle expanded

`top_boundRB`: P4's `top_boundR` for the term multiset `Lvl.termsB` of BOT-DECOMP (the bottom bundle `psiBot` expanded into its summands).
**`wpF_classB`**: W13's `wpF_class` for `Lvl.termsB` (the families `bundleFamOf hR (sffOf ..)` and `bundleBotFamOf hR (botSffOf ..)`; the bottom
families come from `Final.botSffOf`, a copy of W13's `botSffOf` in `Final.BotCount`):

  `‖clsFnR (Lvl.top B)‖_{𝔛^{2η⁸,0,0}(Bx × K)} ≤ Λ (C₁√δ)^{n₍₂₎} Lp lf C₂^b`

from a uniform term bound `β ≤ Λ (Nₛ√δ)^{n₍₂₎} Lp lf` of the terms of `Lvl.termsB`, the absolute convergence of every term, the count
`card_termsB_le_wt` and `C₁ ≥ (ccη+1)·countKc·Nₛ`, `C₂ ≥ countKp 𝔇`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.Final
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13
open scoped ENNReal

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime) (BX : BotExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0)

/-- **`top_boundR` with the bottom bundle expanded** (`unrolled_boundR_extB` at the top level, off the two clock hyperplanes). -/
theorem top_boundRB (hW : WinOfExt B RD hG layer hLayer BE) (hWB : WinOfExtBot B RD hG layer hLayer BX) (σ : ℤˣ) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (s : ℤˣ)
    {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q) {K : Set (Fin 4 → Mom d)} (hK : K.Countable)
    (hq : ∀ tt ∈ Bx, (layer (RD.coreBranch hG a).toNode : ℝ) ≤ tt 0 ∧ tt 0 ≤ layer (RD.coreBranch hG a).toNode + 1)
    (habs : ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B), ∀ tt ∈ Bx, ∀ E ∈ K,
      LkAbs (Lvl.top B).region κ0.L κ0.base ψ tt (sumintBoundary s E))
    (β : ℝ≥0∞)
    (TermBoundR : ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B),
      XNorm00Restr θ Bx K (termFnR B σ κ0 (Lvl.top B) ψ s) ≤ β) :
    XNorm00Restr θ Bx K (clsFnR (p := p) (kind := kind) B RD hG layer hLayer σ κ0 (Lvl.top B) s) ≤
      (cutoffMultiplierConstant θ (cutQ q) + 1) *
        ((Multiset.card (Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B)) : ℝ≥0∞) * β) := by
  set q₀ : ℝ := (layer (RD.coreBranch hG a).toNode : ℝ) with hq₀
  refine (XNorm00Restr_le_openTop θ Bx q₀ K _).trans ?_
  have hsub := openTop_subset Bx q₀
  refine unrolled_boundR_extB (p := p) (kind := kind) B RD hG layer hLayer BE BX hW hWB σ hL hF (Lvl.top B) s hθ q (hsub.trans hBx) hK ?_
    (fun ψ hψ tt htt E hE => habs ψ hψ tt (hsub htt) E hE) β
    (fun ψ hψ => (XNorm00Restr_mono_set θ hsub K _).trans (TermBoundR ψ hψ))
  intro tt htt
  rw [layOf_top]
  exact strict_of_openTop hq tt htt

variable {P : WTParams} {κ0' : KPar P.d} {Bh : ℕ → ℝ} {hprime' : IsPrimeGarden G}

/-- **The top-level class sum in the literal form, bottom bundle expanded** (`wpF_class` for `Lvl.termsB`). -/
theorem wpF_classB (hM9 : VINEPARAM) (hR : RealityAll) (E : GateEnv P κ0' p Bh) (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4)
    (σ : ℤˣ) (hL : κ0'.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin P.d → ℤ => |κ0'.F k (κ0'.base + latticePoint κ0'.L n)|)
    (s : ℤˣ) {η : ℝ} (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q) {K : Set (Fin 4 → Mom P.d)}
    (hK : K.Countable)
    (hq : ∀ tt ∈ Bx, (layer (RD.coreBranch hG a).toNode : ℝ) ≤ tt 0 ∧ tt 0 ≤ layer (RD.coreBranch hG a).toNode + 1)
    (habs : ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer
        (bundleFamOf B RD hG layer hLayer hR (sffOf (hprime := hprime') B RD hG layer hLayer E hord))
        (bundleBotFamOf B RD hG layer hLayer hprime' hR (botSffOf B RD hG layer hLayer hprime' E hord))
        (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B), ∀ tt ∈ Bx, ∀ E' ∈ K,
      LkAbs (Lvl.top B).region κ0'.L κ0'.base ψ tt (sumintBoundary s E'))
    {Λ Ns δ Lp lf C₁ C₂ : ℝ} {D : ℕ} (hpD : p ≤ D)
    (hTB : ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer
        (bundleFamOf B RD hG layer hLayer hR (sffOf (hprime := hprime') B RD hG layer hLayer E hord))
        (bundleBotFamOf B RD hG layer hLayer hprime' hR (botSffOf B RD hG layer hLayer hprime' E hord))
        (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B),
      XNorm00Restr (2 * η ^ 8) Bx K (termFnR B σ κ0' (Lvl.top B) ψ s) ≤
        ENNReal.ofReal (Λ * ((Ns * Real.sqrt δ) ^ clLocalOrder2 RD hG R * Lp * lf)))
    (hΛ : 0 ≤ Λ) (hNs : 0 ≤ Ns) (hLp : 0 ≤ Lp) (hlf : 0 ≤ lf)
    (hC₁ : (Eng.ccη η + 1).toReal * countKc * Ns ≤ C₁) (hC₂ : (countKp D : ℝ) ≤ C₂) :
    XNorm00Restr (2 * η ^ 8) Bx K (clsFnR (p := p) (kind := kind) B RD hG layer hLayer σ κ0' (Lvl.top B) s) ≤
      ENNReal.ofReal (Λ * ((C₁ * Real.sqrt δ) ^ clLocalOrder2 RD hG R * Lp * lf *
        C₂ ^ (Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card)) := by
  have hX := top_boundRB (p := p) (kind := kind) B RD hG layer hLayer
    (bundleFamOf B RD hG layer hLayer hR (sffOf (hprime := hprime') B RD hG layer hLayer E hord))
    (bundleBotFamOf B RD hG layer hLayer hprime' hR (botSffOf B RD hG layer hLayer hprime' E hord))
    (winOfExt_bundleFamOf B RD hG layer hLayer hR _) (winOfExtBot_bundleBotFamOf B RD hG layer hLayer hprime' hR _)
    σ hL hF s (θ := 2 * η ^ 8) (by positivity) q hBx hK hq habs _ hTB
  exact wpF_top B RD hG layer hLayer hM9 q hpD (Lvl.top B)
    (card_termsB_le_wt B RD hG layer hLayer hprime' hR E hord _ (Lvl.top B) (Nat.le_succ _))
    hX le_rfl hΛ hNs hLp hlf hC₁ hC₂

end WaveTurbulence.VineEstS5C.P4.Final
