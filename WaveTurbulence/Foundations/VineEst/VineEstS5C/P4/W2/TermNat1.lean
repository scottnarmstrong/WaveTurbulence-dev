/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatCert
public import WaveTurbulence.Foundations.VineEst.VineEstS3.EpsLabels
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Facts
public import WaveTurbulence.Foundations.Vine.DegenVine.Degenerate

/-! # P4-W2 (session 12, step 1a): the character mixture of the sign `ε` and the free-domain dictionary of a native term

`exists_mix_native`: a `CharMix` of mass `3^{|U|}` whose value at every integer boundary is the sign `clRegionalEpsilon` of the decoration
(`exists_eps_mix` + `clRegionalEpsilon_eq_epsOf`).  `freeDict_native_NE`: `freeDict_native` for an ARBITRARY term `ψ0` with the native row form
`RowFormNE .. ∅ ∅` on the native clock domain (the form is all that the proof used of `psiNat`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **The sign `ε` as a character mixture** of mass `3^{|U|}`. -/
theorem exists_mix_native (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {L : ℝ} (hL : L ≠ 0) (base : Mom d) :
    ∃ N : CharMix (assemblyShape hM9 B) d, N.mass = 3 ^ (clLocalOrder1 R + 1) ∧
      ∀ (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
        (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)),
        N.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x =
          (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ) := by
  classical
  obtain ⟨N, hmass, hval⟩ := exists_eps_mix (ι := ↥U) (S := (assemblyShape hM9 B)) (L := L) hL
    (fun v : ↥U => WaveTurbulence.DegenVine.labelRef (sourceSumintDatum hM9 B hG W) (childLabel hM9 B hG v.1 0))
    (fun v : ↥U => WaveTurbulence.DegenVine.labelRef (sourceSumintDatum hM9 B hG W) (childLabel hM9 B hG v.1 1))
    (fun v : ↥U => WaveTurbulence.DegenVine.labelRef (sourceSumintDatum hM9 B hG W) (childLabel hM9 B hG v.1 2)) base
  refine ⟨N, by rw [hmass, card_U_eq B], fun β hβ x => ?_⟩
  rw [hval (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))
    (fun k => ⟨β (sumintBoundaryPermutation (G.sign a.toNode) k), rfl⟩) x,
    clRegionalEpsilon_eq_epsOf hM9 B hG W hL base β hβ x]
  unfold WaveTurbulence.DegenVine.epsOf
  congr 1
  exact Finset.prod_congr rfl fun i _ => by
    have h0 := WaveTurbulence.DegenVine.labelRef_val (sourceSumintDatum hM9 B hG W) L x
      (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))
    exact congr (congr (congrArg epsMom (h0 _)) (h0 _)) (h0 _)

/-- **`FreeDict` of the modulated native summand with the family of native rows.** -/
theorem freeDict_native_NE (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (htt : tt ∈ WaveTurbulence.VineEstS3.Eng.outBox (sourceSumintDatum hM9 B hG W))
    (ψ ψ0 : PsiT G d) (lam : ℝ)
    (hψ : ∀ x t u, ψ x t u = Complex.exp (((Real.pi * lam * u b : ℝ) : ℂ) * Complex.I) * ψ0 x t u)
    (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop)
    (Xq : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ)
    (hNE : RowFormNE RD hG L γ δ F layer hLayer R base ψ0 Dm ∅ ∅ Xq)
    (hDm : ∀ t u, u a = t 0 → (Dm t u ↔ ClDom R (fun v => layer (RD.coreBranch hG v).toNode) t u))
    (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    {θ : ℝ} (Rw : ∀ ρ : Row (engDatum hM9 B hG W wN wDec bk
        (consX hM9 B (fun v => layer (RD.coreBranch hG v).toNode) ∅ ∅) g g'),
      RowData (engDatum hM9 B hG W wN wDec bk (consX hM9 B (fun v => layer (RD.coreBranch hG v).toNode) ∅ ∅) g g') θ ρ)
    (hRW : ∀ ρ (cl : Fin 3 → ℝ), ![cl 0, cl 1] ∈ rowBx hM9 B RD hG layer hLayer W L γ δ F ρ → ∀ r k,
      (Rw ρ).W cl r k = (assemblyClocked hM9 B RD hG W L γ δ F layer hLayer).W ρ ![cl 0, cl 1] k)
    (hRS : ∀ ρ i, (Rw ρ).slot i = natSlot hM9 B hG ρ i)
    (Mx : CharMix (assemblyShape hM9 B) d)
    (hpar : ∀ v, W.param v =
      if v = (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩ : (assemblyShape hM9 B).TVar) then lam else 0)
    (hMx : ∀ x, Mx.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x =
      (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ))
    (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hok : ConstraintsOK hM9 B W)
    (hWc : W.constraints = assemblyTimeConstraints hM9 B ∪
      layerOrderPairs (assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)))
    (hbk : ∀ i, bk i ≠ 1 ∧ bk i ≠ 2)
    (hp : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      tt 1 ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩))
    (hn : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      tt 2 ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩)) :
    FreeDict hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk
      (consX hM9 B (fun v => layer (RD.coreBranch hG v).toNode) ∅ ∅) g g' Mx (allCR Rw) := by
  classical
  refine freeDict_of_NE hM9 B RD hG W hL γ δ η F layer hLayer base β hβ tt ψ ψ0 lam hψ Dm ∅ ∅ Xq hNE ?_ wN wDec bk ∅ g g' Mx
    (allCR Rw) hpar hMx hq hp hn ?_ ?_
  · intro t u hu
    exact (hDm t u hu).trans (domX_empty R _ t u).symm
  · intro x
    exact Filter.Eventually.of_forall fun τ _ h => absurd ⟨by simp, by simp⟩ h
  · intro x
    refine Filter.Eventually.of_forall fun τ hτ => ?_
    have hτ' := (mem_engTimeDom_iff' hM9 B hG W wN wDec bk _ g g' tt τ).mp hτ
    rw [consX_empty, ← hWc] at hτ'
    have hτs : τ ∈ (sourceSumintDatum hM9 B hG W).timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) :=
      (mem_srcTimeDom_iff' hM9 B hG W tt τ).mpr hτ'
    simpa using hrow_native_allCR hM9 B hG W wN wDec bk _ g g' RD L γ δ F layer hLayer Rw hRW hRS hL η base β hβ tt x τ hbk
      (fun ρ => rows_clock_mem hM9 B RD hG layer hLayer W hok L γ δ F tt htt τ hτs ρ)

end WaveTurbulence.VineEstS5C.P4.W2
