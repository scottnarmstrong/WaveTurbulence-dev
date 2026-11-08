/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import WaveTurbulence.Foundations.VineEst.VineSpaceK.StatementDefs

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.ClassM
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.Engine
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Export

/-! The flat V5 observable with a spatial weight inside the native lattice sum.
Finite term expansion and the time-Fourier Minkowski bound retain one mass.
This module does not identify it with the original weighted LF class sum.
-/
@[expose] public section
namespace WaveTurbulence.VineSpaceK
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13
  WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal

open VineEstS5C.P4.Final

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime) (BX : BotExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0)

/-- **The modulated top-level bound** (`top_boundRB` with `modPsi b λ`). -/
theorem top_boundRBMX (m : (GNode G.tree → Fin d → ℤ) → ℂ) (hW : WinOfExt B RD hG layer hLayer BE) (hWB : WinOfExtBot B RD hG layer hLayer BX) (lam : ℝ) (σ : ℤˣ)
    (s : ℤˣ) {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q)
    {K : Set (Fin 4 → Mom d)} (hK : K.Countable)
    (hq : ∀ tt ∈ Bx, (layer (RD.coreBranch hG a).toNode : ℝ) ≤ tt 0 ∧ tt 0 ≤ layer (RD.coreBranch hG a).toNode + 1)
    (habs : ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B),
      ∀ tt ∈ openTop Bx (layer (RD.coreBranch hG a).toNode : ℝ), ∀ E ∈ K,
      LkAbs (Lvl.top B).region κ0.L κ0.base (spatialMul m (modPsi b lam ψ)) tt (sumintBoundary s E))
    (β : ℝ≥0∞)
    (TermBoundR : ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B),
      XNorm00Restr θ (openTop Bx (layer (RD.coreBranch hG a).toNode : ℝ)) K (termFnR B σ κ0 (Lvl.top B) (spatialMul m (modPsi b lam ψ)) s) ≤ β) :
    XNorm00Restr θ Bx K (flatFnRMX (p := p) (kind := kind) B RD hG layer hLayer m lam σ κ0 hprime s) ≤
      (cutoffMultiplierConstant θ (cutQ q) + 1) *
        ((Multiset.card (Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B)) : ℝ≥0∞) * β) := by
  classical
  set q₀ : ℝ := (layer (RD.coreBranch hG a).toNode : ℝ) with hq₀
  refine (XNorm00Restr_le_openTop θ Bx q₀ K _).trans ?_
  have hsub := openTop_subset Bx q₀
  set T := Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B) with hT
  have hmem : ∀ j : Fin T.toList.length, T.toList[j] ∈ T := fun j => Multiset.mem_toList.mp (List.getElem_mem j.2)
  have hExt : ∀ tt ∈ openTop Bx q₀, (layOf ((Lvl.top B).state B RD hG layer hLayer) (Lvl.top B).c.a : ℝ) < tt 0 ∧
      tt 0 < layOf ((Lvl.top B).state B RD hG layer hLayer) (Lvl.top B).c.a + 1 := by
    intro tt htt
    rw [layOf_top]
    exact strict_of_openTop hq tt htt
  have h1 := XNorm00Restr_finsum_le hθ q (hsub.trans hBx) hK
    (fun j : Fin T.toList.length => termFnR B σ κ0 (Lvl.top B) (spatialMul m (modPsi b lam T.toList[j])) s)
    (flatFnRMX (p := p) (kind := kind) B RD hG layer hLayer m lam σ κ0 hprime s) (fun tt htt E hE => by
      unfold flatFnRMX termFnR termFn
      have hlk := lkRaw_finsum (Lvl.top B).region κ0.L κ0.base
        (spatialMul m (modPsi b lam (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B))))
        (fun j : Fin T.toList.length => spatialMul m (modPsi b lam T.toList[j])) tt (sumintBoundary s E)
        (fun κ => Filter.Eventually.of_forall fun τ => by
          have := Lvl.psiFuel_eq_termsB_ext (p := p) (kind := kind) B RD hG layer hLayer BE BX hW hWB
            (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B) (clExtendIndices (Lvl.top B).region κ.1) tt
            (clLocalClock (Lvl.top B).region tt τ)
            ((extOf_clock_iff B RD hG layer hLayer (Lvl.top B) tt τ).2 (hExt tt htt))
          unfold spatialMul modPsi
          rw [this, multiset_sum_eq_fin, Finset.mul_sum, Finset.mul_sum])
        (fun j => habs _ (hmem j) tt htt E hE)
      rw [hlk, Finset.mul_sum, Finset.mul_sum])
  refine h1.trans (mul_le_mul' le_rfl ?_)
  calc ∑ j : Fin T.toList.length, XNorm00Restr θ (openTop Bx q₀) K (termFnR B σ κ0 (Lvl.top B) (spatialMul m (modPsi b lam T.toList[j])) s)
      ≤ ∑ _j : Fin T.toList.length, β := Finset.sum_le_sum fun j _ => TermBoundR _ (hmem j)
    _ = (Multiset.card T : ℝ≥0∞) * β := by
        simp [Finset.sum_const, nsmul_eq_mul, Multiset.length_toList]

variable {P : WTParams} {κ0' : KPar P.d} {Bh : ℕ → ℝ} {hprime' : IsPrimeGarden G}

/-- The weighted flat bound after the finite term count; `Λ` includes mass and temporal loss. -/
theorem wpF_flatBMX (hM9 : VINEPARAM) (hR : RealityAll) (E : GateEnv P κ0' p Bh) (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4)
    (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) (lam : ℝ) (σ : ℤˣ) (s : ℤˣ) {η : ℝ} (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q)
    {K : Set (Fin 4 → Mom P.d)} (hK : K.Countable)
    (hq : ∀ tt ∈ Bx, (layer (RD.coreBranch hG a).toNode : ℝ) ≤ tt 0 ∧ tt 0 ≤ layer (RD.coreBranch hG a).toNode + 1)
    (habs : ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer
        (bundleFamOf B RD hG layer hLayer hR (sffOf (hprime := hprime') B RD hG layer hLayer E hord))
        (bundleBotFamOf B RD hG layer hLayer hprime' hR (botSffOf B RD hG layer hLayer hprime' E hord))
        (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B), ∀ tt ∈ openTop Bx (layer (RD.coreBranch hG a).toNode : ℝ), ∀ E' ∈ K,
      LkAbs (Lvl.top B).region κ0'.L κ0'.base (spatialMul m (modPsi b lam ψ)) tt (sumintBoundary s E'))
    {Λ Ns δ Lp lf C₁ C₂ : ℝ} {D : ℕ} (hpD : p ≤ D)
    (hTB : ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer
        (bundleFamOf B RD hG layer hLayer hR (sffOf (hprime := hprime') B RD hG layer hLayer E hord))
        (bundleBotFamOf B RD hG layer hLayer hprime' hR (botSffOf B RD hG layer hLayer hprime' E hord))
        (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B),
      XNorm00Restr (2 * η ^ 8) (openTop Bx (layer (RD.coreBranch hG a).toNode : ℝ)) K (termFnR B σ κ0' (Lvl.top B) (spatialMul m (modPsi b lam ψ)) s) ≤
        ENNReal.ofReal (Λ * ((Ns * Real.sqrt δ) ^ clLocalOrder2 RD hG R * Lp * lf)))
    (hΛ : 0 ≤ Λ) (hNs : 0 ≤ Ns) (hLp : 0 ≤ Lp) (hlf : 0 ≤ lf)
    (hC₁ : (Eng.ccη η + 1).toReal * countKc * Ns ≤ C₁) (hC₂ : (countKp D : ℝ) ≤ C₂) :
    XNorm00Restr (2 * η ^ 8) Bx K (flatFnRMX (p := p) (kind := kind) B RD hG layer hLayer m lam σ κ0' hprime' s) ≤
      ENNReal.ofReal (Λ * ((C₁ * Real.sqrt δ) ^ clLocalOrder2 RD hG R * Lp * lf *
        C₂ ^ (Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card)) := by
  have hX := top_boundRBMX (p := p) (kind := kind) B RD hG layer hLayer
    (bundleFamOf B RD hG layer hLayer hR (sffOf (hprime := hprime') B RD hG layer hLayer E hord))
    (bundleBotFamOf B RD hG layer hLayer hprime' hR (botSffOf B RD hG layer hLayer hprime' E hord))
    m (winOfExt_bundleFamOf B RD hG layer hLayer hR _) (winOfExtBot_bundleBotFamOf B RD hG layer hLayer hprime' hR _)
    lam σ s (θ := 2 * η ^ 8) (by positivity) q hBx hK hq habs _ hTB
  exact wpF_top B RD hG layer hLayer hM9 q hpD (Lvl.top B)
    (card_termsB_le_wt B RD hG layer hLayer hprime' hR E hord _ (Lvl.top B) (Nat.le_succ _))
    hX le_rfl hΛ hNs hLp hlf hC₁ hC₂

end WaveTurbulence.VineSpaceK
