/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.VineEst.VineSpaceK.StatementDefs
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.Engine
/-! Structural pullback across the certificate's existential engine assembly. -/
@[expose] public section
noncomputable section
namespace WaveTurbulence.VineSpaceK
open MeasureTheory DegenVine DegenVinePar VineEstS5C VineEstS5C.P2 VineEstS5C.P3
  VineEstS5C.P4 VineEstS5C.P4.W2 VineEstS3Par.Eng RegRed Reg.Skeleton VineParamContract
  VineEstS2 VineEstS3 VineEstS4 VineEstS5A TTree
open scoped ENNReal
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem enginePullback_one (R : CLRegionData G U a b) (L : ℝ) (base : Mom d) :
    EnginePullback R L base (fun _ => 1) 1 := by
  intro n hM9 B hL
  exact ⟨CharMix.one _ _, by simp, fun _ _ _ => by simp⟩

/-- Generic ψ is sufficient *once* its common-data map has the engine pullback.
Rows, domains, modulation and all R78 row constants are unchanged. -/
theorem termCertW_mul {A : ℝ} {P : WTParams} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) (hG : G.IsPlain) (κ0 : KPar P.d) (lv : Lvl B)
    (ψ : PsiT G P.d) {Bx : Set (Fin 3 → ℝ)} {K : Set (Fin 4 → Mom P.d)} {β' : ℝ≥0∞}
    (hc : TermCertW (A := A) B hG κ0 lv ψ Bx K β')
    (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) {mass : ℝ}
    (hpull : EnginePullback lv.region P.L κ0.base m mass) :
    TermCertW (A := A) B hG κ0 lv (spatialMul m ψ) Bx K (ENNReal.ofReal mass * β') := by
  obtain ⟨n', hM9, B', W, wN, wDec, bk, cons, g, g', Z, Rw, hL, hAe, hrow, hw, hBx, hK, hinv, hd, hb⟩ := hc
  have hpullW : EnginePullback lv.region P.L W.wBar m mass := by
    rw [hw]
    exact hpull
  obtain ⟨N, hmass, he⟩ := hpullW n' hM9 B' hL
  change CharMix (engDatum hM9 B' hG W wN wDec bk cons g g').S P.d at N
  refine ⟨n', hM9, B', W, wN, wDec, bk, cons, g, g', addMix Z N, Rw, hL, hAe, hrow, hw, hBx, hK, ?_, ?_, ?_⟩
  · intro t β' κ u hu
    simp only [spatialMul]
    rw [hinv t β' κ u hu]
  · intro tt htt β hβ hE
    apply freeDict_mul hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ
      (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) tt) ψ m wN wDec bk cons g g'
      Z.Mx N (allCR Rw) (hd tt htt β hβ hE)
    exact he β hβ
  · rw [addMix_pre]
    have key := mul_le_mul' (ENNReal.ofReal_le_ofReal hmass) hb
    refine le_trans (le_of_eq ?_) key
    ac_rfl
end WaveTurbulence.VineSpaceK
