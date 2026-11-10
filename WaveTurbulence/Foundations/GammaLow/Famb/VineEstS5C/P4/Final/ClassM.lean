/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Export
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.ClassM
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Bot.Unroll
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Final.BotCount
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.FlatMod.Export
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W13.WPF
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.WinChain
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.ClassM` (sha256 5891a78b071d080b…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # V5 FINAL (step 2b): the modulated class sum (R58), literal form

`top_boundRBM`: the recentered observable `recFac · c ζ · lkRaw (modPsi b λ psiFuel)` of the top level (FLAT-MOD's flat form of
`Cont.twistedRecenteredModC`) obeys the finite-Minkowski bound `(cc + 1) (#terms β)` from bounds `β` of the recentered observables
`termFnR` of the modulated terms `modPsi b λ ψ`, `ψ ∈ Lvl.termsB`, and their absolute convergence (`habsM`).
**`wpF_classBM`**: W13's `wpF_top` applied to it (the count `card_termsB_le_wt`): the literal bound
`Λ (C₁√δ)^{n₍₂₎} Lp lf C₂^b` with `Λ` the λ-loss.
**`twistedRecenteredModC_bound`**: the same bound for the integrand `twistedRecenteredModC` of `VineEstCanonLayerC2M`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Final WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Final
variable {γF : ℝ}
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13
  WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W13
open scoped ENNReal

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime) (BX : BotExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0)

/-- The modulated class observable of the top level: `recFac · c ζ · lkRaw (modPsi b λ psiFuel)`. -/
noncomputable def clsFnRMΓ (lam : ℝ) (σ : ℤˣ) (κ0 : KPar d) (hprime : IsPrimeGarden G) (s : ℤˣ) :
    (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ :=
  fun tt E => recFac σ s κ0.L κ0.γ κ0.δ tt E * (LvlΓ.cstΓ B κ0 (LvlΓ.top B) *
    lkRaw (LvlΓ.top B).region κ0.L κ0.base
      (modPsi b lam (LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (Fintype.card (LvlΓ.top B).ι + 1) (LvlΓ.top B)))
      tt (sumintBoundary s E))

/-- **The modulated top-level bound** (`top_boundRB` with `modPsi b λ`). -/
theorem top_boundRBMΓ (hW : WinOfExtΓ B RD hG layer hLayer BE) (hWB : WinOfExtBotΓ B RD hG layer hLayer BX) (lam : ℝ) (σ : ℤˣ)
    (hL : κ0.L ≠ 0) (s : ℤˣ) {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q)
    {K : Set (Fin 4 → Mom d)} (hK : K.Countable)
    (hq : ∀ tt ∈ Bx, (layer (RD.coreBranch hG a).toNode : ℝ) ≤ tt 0 ∧ tt 0 ≤ layer (RD.coreBranch hG a).toNode + 1)
    (habs : ∀ ψ ∈ LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card (LvlΓ.top B).ι + 1) (LvlΓ.top B),
      ∀ tt ∈ openTop Bx (layer (RD.coreBranch hG a).toNode : ℝ), ∀ E ∈ K,
      LkAbs (LvlΓ.top B).region κ0.L κ0.base (modPsi b lam ψ) tt (sumintBoundary s E))
    (β : ℝ≥0∞)
    (TermBoundR : ∀ ψ ∈ LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card (LvlΓ.top B).ι + 1) (LvlΓ.top B),
      XNorm00Restr θ (openTop Bx (layer (RD.coreBranch hG a).toNode : ℝ)) K (termFnRΓ B σ κ0 (LvlΓ.top B) (modPsi b lam ψ) s) ≤ β) :
    XNorm00Restr θ Bx K (clsFnRMΓ (p := p) (kind := kind) B RD hG layer hLayer lam σ κ0 hprime s) ≤
      (cutoffMultiplierConstant θ (cutQ q) + 1) *
        ((Multiset.card (LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card (LvlΓ.top B).ι + 1) (LvlΓ.top B)) : ℝ≥0∞) * β) := by
  classical
  set q₀ : ℝ := (layer (RD.coreBranch hG a).toNode : ℝ) with hq₀
  refine (XNorm00Restr_le_openTop θ Bx q₀ K _).trans ?_
  have hsub := openTop_subset Bx q₀
  set T := LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card (LvlΓ.top B).ι + 1) (LvlΓ.top B) with hT
  have hmem : ∀ j : Fin T.toList.length, T.toList[j] ∈ T := fun j => Multiset.mem_toList.mp (List.getElem_mem j.2)
  have hExt : ∀ tt ∈ openTop Bx q₀, (layOf ((LvlΓ.top B).state B RD hG layer hLayer) (LvlΓ.top B).c.a : ℝ) < tt 0 ∧
      tt 0 < layOf ((LvlΓ.top B).state B RD hG layer hLayer) (LvlΓ.top B).c.a + 1 := by
    intro tt htt
    rw [layOf_topΓ]
    exact strict_of_openTop hq tt htt
  have h1 := XNorm00Restr_finsum_le hθ q (hsub.trans hBx) hK
    (fun j : Fin T.toList.length => termFnRΓ B σ κ0 (LvlΓ.top B) (modPsi b lam T.toList[j]) s)
    (clsFnRMΓ (p := p) (kind := kind) B RD hG layer hLayer lam σ κ0 hprime s) (fun tt htt E hE => by
      unfold clsFnRMΓ termFnRΓ termFnΓ
      have hlk := lkRaw_finsum (LvlΓ.top B).region κ0.L κ0.base
        (modPsi b lam (LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (Fintype.card (LvlΓ.top B).ι + 1) (LvlΓ.top B)))
        (fun j : Fin T.toList.length => modPsi b lam T.toList[j]) tt (sumintBoundary s E)
        (fun κ => Filter.Eventually.of_forall fun τ => by
          have := LvlΓ.psiFuel_eq_termsB_extΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX hW hWB
            (Fintype.card (LvlΓ.top B).ι + 1) (LvlΓ.top B) (clExtendIndices (LvlΓ.top B).region κ.1) tt
            (clLocalClock (LvlΓ.top B).region tt τ)
            ((extOf_clock_iffΓ B RD hG layer hLayer (LvlΓ.top B) tt τ).2 (hExt tt htt))
          unfold modPsi at this ⊢
          rw [this, multiset_sum_eq_fin, Finset.mul_sum])
        (fun j => habs _ (hmem j) tt htt E hE)
      rw [hlk, Finset.mul_sum, Finset.mul_sum])
  refine h1.trans (mul_le_mul' le_rfl ?_)
  calc ∑ j : Fin T.toList.length, XNorm00Restr θ (openTop Bx q₀) K (termFnRΓ B σ κ0 (LvlΓ.top B) (modPsi b lam T.toList[j]) s)
      ≤ ∑ _j : Fin T.toList.length, β := Finset.sum_le_sum fun j _ => TermBoundR _ (hmem j)
    _ = (Multiset.card T : ℝ≥0∞) * β := by
        simp [Finset.sum_const, nsmul_eq_mul, Multiset.length_toList]

/-- **The integrand of `VineEstCanonLayerC2M` is `clsFnRM`** (FLAT-MOD's flat form). -/
theorem twistedRecenteredModC_eq_clsFnRMΓ (hprime : IsPrimeGarden G) (lam : ℝ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (wBar : Mom d)
    (hL : L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |F k (wBar + latticePoint L n)|) :
    (fun (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d) => Cont.twistedRecenteredModC G a
        (canonFinsetK p kind (startStateΓ B RD hG layer hLayer) (chainStartΓ B)) L γ δ F wBar lam
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) =
      clsFnRMΓ (p := p) (kind := kind) B RD hG layer hLayer lam (G.sign a.toNode) (kparOf L γ δ F wBar) hprime (G.sign a.toNode) := by
  funext tt E
  have h := twistedRecenteredModC_eq_flatΓ (p := p) (kind := kind) B RD hG layer hLayer hprime lam (kparOf L γ δ F wBar) hL hF (tt 0) (tt 1) (tt 2)
    (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1) (sumintBoundary (G.sign a.toNode) E 2)
    (sumintBoundary (G.sign a.toNode) E 3)
  rw [P3.vec3_eta, P3.vec4_eta'] at h
  refine h.trans ?_
  rfl

variable {P : WTParams} {κ0' : KPar P.d} {Bh : ℕ → ℝ} {hprime' : IsPrimeGarden G}

/-- **The modulated top-level class sum in the literal form** (`wpF_classB` with `modPsi b λ`; `Λ` the λ-loss). -/
theorem wpF_classBMΓ (hM9 : NormalChartSupply γF) (hR : RealityAll) (E : GateEnv P κ0' p Bh) (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4)
    (lam : ℝ) (σ : ℤˣ) (hL : κ0'.L ≠ 0) (s : ℤˣ) {η : ℝ} (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q)
    {K : Set (Fin 4 → Mom P.d)} (hK : K.Countable)
    (hq : ∀ tt ∈ Bx, (layer (RD.coreBranch hG a).toNode : ℝ) ≤ tt 0 ∧ tt 0 ≤ layer (RD.coreBranch hG a).toNode + 1)
    (habs : ∀ ψ ∈ LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer
        (bundleFamOfΓ B RD hG layer hLayer hR (sffOfΓ (hprime := hprime') B RD hG layer hLayer E hord))
        (bundleBotFamOfΓ B RD hG layer hLayer hprime' hR (botSffOfΓ B RD hG layer hLayer hprime' E hord))
        (Fintype.card (LvlΓ.top B).ι + 1) (LvlΓ.top B), ∀ tt ∈ openTop Bx (layer (RD.coreBranch hG a).toNode : ℝ), ∀ E' ∈ K,
      LkAbs (LvlΓ.top B).region κ0'.L κ0'.base (modPsi b lam ψ) tt (sumintBoundary s E'))
    {Λ Ns δ Lp lf C₁ C₂ : ℝ} {D : ℕ} (hpD : p ≤ D)
    (hTB : ∀ ψ ∈ LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer
        (bundleFamOfΓ B RD hG layer hLayer hR (sffOfΓ (hprime := hprime') B RD hG layer hLayer E hord))
        (bundleBotFamOfΓ B RD hG layer hLayer hprime' hR (botSffOfΓ B RD hG layer hLayer hprime' E hord))
        (Fintype.card (LvlΓ.top B).ι + 1) (LvlΓ.top B),
      XNorm00Restr (2 * η ^ 8) (openTop Bx (layer (RD.coreBranch hG a).toNode : ℝ)) K (termFnRΓ B σ κ0' (LvlΓ.top B) (modPsi b lam ψ) s) ≤
        ENNReal.ofReal (Λ * ((Ns * Real.sqrt δ) ^ clLocalOrder2 RD hG R * Lp * lf)))
    (hΛ : 0 ≤ Λ) (hNs : 0 ≤ Ns) (hLp : 0 ≤ Lp) (hlf : 0 ≤ lf)
    (hC₁ : (Eng.ccη η + 1).toReal * countKc * Ns ≤ C₁) (hC₂ : (countKp D : ℝ) ≤ C₂) :
    XNorm00Restr (2 * η ^ 8) Bx K (clsFnRMΓ (p := p) (kind := kind) B RD hG layer hLayer lam σ κ0' hprime' s) ≤
      ENNReal.ofReal (Λ * ((C₁ * Real.sqrt δ) ^ clLocalOrder2 RD hG R * Lp * lf *
        C₂ ^ (Finset.univ.filter fun i => (assemblyShapeΓ hM9 B).nor i = false).card)) := by
  have hX := top_boundRBMΓ (p := p) (kind := kind) B RD hG layer hLayer
    (bundleFamOfΓ B RD hG layer hLayer hR (sffOfΓ (hprime := hprime') B RD hG layer hLayer E hord))
    (bundleBotFamOfΓ B RD hG layer hLayer hprime' hR (botSffOfΓ B RD hG layer hLayer hprime' E hord))
    (winOfExt_bundleFamOfΓ B RD hG layer hLayer hR _) (winOfExtBot_bundleBotFamOfΓ B RD hG layer hLayer hprime' hR _)
    lam σ hL s (θ := 2 * η ^ 8) (by positivity) q hBx hK hq habs _ hTB
  exact wpF_topΓ B RD hG layer hLayer hM9 q hpD (LvlΓ.top B)
    (card_termsB_le_wtΓ B RD hG layer hLayer hprime' hR E hord _ (LvlΓ.top B) (Nat.le_succ _))
    hX le_rfl hΛ hNs hLp hlf hC₁ hC₂

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Final
