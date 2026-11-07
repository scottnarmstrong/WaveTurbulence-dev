/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.DomEng
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.FreeRow
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowNE

/-! # P4-W2 (session 10, step 4.2): the free-domain dictionary of a native-except term

`freeDict_of_NE`: `FreeDict` for a term `e^{πiλu_b} ψ₀` whose row form is native except at the exceptional pairs and branches
(`RowFormNE`, with clock domain `DomX` off the exceptional parent conditions), for the engine datum with the constraints `consX`.  The
engine domain is `DomX` plus the extra pairs `add` and the exceptional order edges (`engDom_to_domX`, `domX_to_engDom`); the term
vanishes where these fail (`hcontract`); the row identity `hrow` is the only remaining input.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **`FreeDict` of a native-except term** (see the module docstring). -/
theorem freeDict_of_NE (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (ψ ψ0 : PsiT G d) (lam : ℝ)
    (hψ : ∀ x t u, ψ x t u = Complex.exp (((Real.pi * lam * u b : ℝ) : ℂ) * Complex.I) * ψ0 x t u)
    (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop) (Pex : Finset (SourcePair G)) (Bex : Finset (GBranch G.tree))
    (Xq : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ)
    (hNE : RowFormNE RD hG L γ δ F layer hLayer R base ψ0 Dm Pex Bex Xq)
    (hDm : ∀ t u, u a = t 0 → (Dm t u ↔ DomX R (fun v => layer (RD.coreBranch hG v).toNode) Bex (t 0) (t 1) (t 2) u))
    (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (add : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (Mx : CharMix (assemblyShape hM9 B) d)
    (cr : ClockedRows3 (engDatum hM9 B hG W wN wDec bk
      (consX hM9 B (fun v => layer (RD.coreBranch hG v).toNode) Bex add) g g'))
    (hpar : ∀ v, W.param v =
      if v = (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩ : (assemblyShape hM9 B).TVar) then lam else 0)
    (hMx : ∀ x, Mx.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x =
      (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ))
    (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hp : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      tt 1 ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩))
    (hn : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      tt 2 ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩))
    (hcontract : ∀ x, ∀ᵐ τ : (assemblyShape hM9 B).TVar → ℝ,
      DomX R (fun v => layer (RD.coreBranch hG v).toNode) Bex (tt 0) (tt 1) (tt 2)
        (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) →
      ¬ ((∀ c ∈ add, τ c.1 < τ c.2) ∧ ∀ v ∈ Bex, ∃ y ∈ U, y ≠ a ∧
          clLocalClock R tt (assemblyClockEquiv hM9 B τ) v < clLocalClock R tt (assemblyClockEquiv hM9 B τ) y) →
      (∏ p ∈ clRegionalPairs hG U, (if p ∈ Pex then Xq p tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ))
            (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
          else qRow RD hG L γ δ F layer hLayer base (tt 0) (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
            (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) p)) *
        (∏ v ∈ U.erase a, (if v ∈ Bex then 1 else tRow RD hG L γ δ F layer hLayer base (tt 0)
            (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
            (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) v)) = 0)
    (hrow : ∀ x, ∀ᵐ τ : (assemblyShape hM9 B).TVar → ℝ,
      τ ∈ (engDatum hM9 B hG W wN wDec bk (consX hM9 B (fun v => layer (RD.coreBranch hG v).toNode) Bex add) g g').timeDom
        (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) →
      (∏ p ∈ clRegionalPairs hG U, (if p ∈ Pex then Xq p tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ))
            (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
          else qRow RD hG L γ δ F layer hLayer base (tt 0) (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
            (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) p)) *
        (∏ v ∈ U.erase a, (if v ∈ Bex then 1 else tRow RD hG L γ δ F layer hLayer base (tt 0)
            (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
            (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) v)) =
      ((kind1Pref (D := engDatum hM9 B hG W wN wDec bk (consX hM9 B (fun v => layer (RD.coreBranch hG v).toNode) Bex add) g g')
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) : ℝ) : ℂ) * k2c bk η τ *
        ∏ ρ, cr.W ρ (cr.clock τ tt ρ)
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1)
          (rowMom (engDatum hM9 B hG W wN wDec bk (consX hM9 B (fun v => layer (RD.coreBranch hG v).toNode) Bex add) g g') L x
            (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) ρ)) :
    FreeDict hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk
      (consX hM9 B (fun v => layer (RD.coreBranch hG v).toNode) Bex add) g g' Mx cr := by
  classical
  have hae : ∀ᵐ τ : (assemblyShape hM9 B).TVar → ℝ, ∀ s, τ s ≠ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode) s ∧
      τ s ≠ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode) s + 1 := by
    rw [ae_all_iff]
    intro s
    exact (Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) s _).and
      (Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) s _)
  have hup : ∀ τ : (assemblyShape hM9 B).TVar → ℝ, (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) a = tt 0 :=
    fun τ => clLocalClock_upper R tt _
  refine freeDict_of_rowForm hM9 B hG W hL γ δ η base β hβ tt ψ ψ0 lam hψ hNE wN wDec bk _ g g' Mx cr hpar hMx ?_ ?_ ?_
  · filter_upwards [hae] with τ hτ hmem
    refine (hDm _ _ (hup τ)).mpr (engDom_to_domX hM9 B (fun v => layer (RD.coreBranch hG v).toNode) Bex add (assemblyShape_I_pos hM9 B) tt τ hτ ?_)
    have := (mem_engTimeDom_iff' hM9 B hG W wN wDec bk (consX hM9 B (fun v => layer (RD.coreBranch hG v).toNode) Bex add) g g' tt τ).mp hmem
    rwa [hq] at this
  · intro x
    filter_upwards [hcontract x] with τ hc hD hnot
    refine hc ((hDm _ _ (hup τ)).mp hD) fun hex => hnot ?_
    rw [mem_engTimeDom_iff' hM9 B hG W wN wDec bk (consX hM9 B (fun v => layer (RD.coreBranch hG v).toNode) Bex add) g g' tt τ, hq]
    exact domX_to_engDom hM9 B (fun v => layer (RD.coreBranch hG v).toNode) Bex add (assemblyShape_I_pos hM9 B) tt τ hp hn ((hDm _ _ (hup τ)).mp hD) hex.2 hex.1
  · exact hrow

end WaveTurbulence.VineEstS5C.P4.W2
