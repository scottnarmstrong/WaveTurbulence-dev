/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowMatch
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LeafChild

/-! # P4-W2 (N2(c) native case): the engine time domain and the dictionary of the native summand

* `mem_engTimeDom_iff`: with the source windows (`W.q = assemblyTimeQ`) and the native constraints (`assemblyTimeConstraints`), the time
  domain of the engine datum is `assemblyTimeDomain`.
* `kind1Pref_eq_one`, `k2c_eq_one`: no kind-1 / kind-2 block, no prefactor.
* **`freeDict_psiNat`**: the free-domain dictionary `FreeDict` of the modulated native summand `e^{πiλu_b} psiNat` of the region, with the
  native rows `natCR3`, the native constraints, the parameter `λ` at the clock of `b`, and the sign mixture `Mx` (any `CharMix` whose value is
  `ε`); the exterior clocks obey the leaf-child conditions `hp`, `hn` of V4/V5-CONT (`t' ≤ q_b` at a leaf lower child).  This is the
  dictionary of the terms without an operative member (`psiBase`), and the model of the general case.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B
open scoped ENNReal

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

section
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
  (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
  (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)

/-- The engine time domain with the source windows and the native constraints is `assemblyTimeDomain`. -/
theorem mem_engTimeDom_iff (layer0 : GBranch G.tree → ℕ) (hq : W.q = assemblyTimeQ hM9 B layer0)
    (hc : cons = assemblyTimeConstraints hM9 B) (tt : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ) :
    τ ∈ (engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) ↔
      τ ∈ assemblyTimeDomain hM9 B layer0 (assemblyShape_I_pos hM9 B) tt := by
  subst hc
  cases W with
  | mk wK wL g0 g0' param q constraints badKind qOut centre wBar =>
    dsimp only at hq
    subst hq
    exact Iff.rfl

theorem kind1Pref_eq_one (hbk : ∀ i, bk i ≠ 1) (E : Fin 4 → Mom d) :
    kind1Pref (D := engDatum hM9 B hG W wN wDec bk cons g g') E = 1 := by
  unfold kind1Pref
  have : (Finset.univ.filter fun i => (engDatum hM9 B hG W wN wDec bk cons g g').S.nor i = false ∧
      (engDatum hM9 B hG W wN wDec bk cons g g').badKind i = 1) = ∅ :=
    Finset.filter_false_of_mem fun i _ h => hbk i h.2
  rw [this, Finset.card_empty, pow_zero]

end

theorem k2c_eq_one {S : WaveTurbulence.SumintShape} (bk : Fin S.I → Fin 4) (hbk : ∀ i, bk i ≠ 2) (η : ℝ) (τ : S.TVar → ℝ) :
    k2c bk η τ = 1 :=
  Finset.prod_eq_one fun i _ => dite_eq_right_iff.mpr fun h => absurd h.2.1 (hbk i)

/-- **The dictionary of the modulated native summand** (N2 for the terms without an operative member). -/
theorem freeDict_psiNat (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (ψ : PsiT G d) (lam : ℝ)
    (hψ : ∀ x t u, ψ x t u = Complex.exp (((Real.pi * lam * u b : ℝ) : ℂ) * Complex.I) *
      psiNat RD hG R L γ δ F layer hLayer base x t u)
    (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (Mx : CharMix (assemblyShape hM9 B) d)
    (hpar : ∀ v, W.param v =
      if v = (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩ : (assemblyShape hM9 B).TVar) then lam else 0)
    (hMx : ∀ x, Mx.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x =
      (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ))
    (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hbk : ∀ i, bk i ≠ 1 ∧ bk i ≠ 2)
    (hp : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      tt 1 ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩))
    (hn : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      tt 2 ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩)) :
    FreeDict hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk (assemblyTimeConstraints hM9 B) g g' Mx
      (natCR3 hM9 B hG W wN wDec bk (assemblyTimeConstraints hM9 B) g g' RD L γ δ F layer hLayer) := by
  set layer0 : GBranch G.tree → ℕ := fun v => layer (RD.coreBranch hG v).toNode with hlayer0
  have hiff := mem_engTimeDom_iff hM9 B hG W wN wDec bk (assemblyTimeConstraints hM9 B) g g' layer0 hq rfl tt
  refine freeDict_of_rowForm hM9 B hG W hL γ δ η base β hβ tt ψ _ lam hψ
    (rowForm_psiNat RD hG R L γ δ F layer hLayer base) wN wDec bk (assemblyTimeConstraints hM9 B) g g' Mx _ hpar hMx
    ?_ ?_ ?_
  · -- the engine domain lies in the native domain (a.e.: off the window boundaries)
    have hae : ∀ᵐ τ : (assemblyShape hM9 B).TVar → ℝ, ∀ s, τ s ≠ assemblyTimeQ hM9 B layer0 s ∧
        τ s ≠ assemblyTimeQ hM9 B layer0 s + 1 := by
      rw [ae_all_iff]
      intro s
      exact (Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) s _).and
        (Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) s _)
    filter_upwards [hae] with τ hτ hmem
    exact (mem_clLocalTimeDomain_iff R layer0 tt _).mp
      (source_of_assemblyTimeDomain hM9 B (assemblyShape_I_pos hM9 B) layer0 tt τ ((hiff τ).mp hmem) hτ)
  · -- the native domain lies in the engine domain (the leaf-child conditions `hp`, `hn`)
    intro x
    refine Filter.Eventually.of_forall fun τ hD hnot => absurd ((hiff τ).mpr ?_) hnot
    exact assemblyTimeDomain_of_source' hM9 B (assemblyShape_I_pos hM9 B) layer0 tt τ hp hn
      ((mem_clLocalTimeDomain_iff R layer0 tt _).mpr hD)
  · -- the native rows
    intro x
    refine Filter.Eventually.of_forall fun τ _ => ?_
    rw [kind1Pref_eq_one hM9 B hG W wN wDec bk _ g g' (fun i => (hbk i).1),
      k2c_eq_one bk (fun i => (hbk i).2), Complex.ofReal_one, one_mul, one_mul]
    have h := hrow_of_rowwise (a := a) hM9 B hG
      (fun p => qRow RD hG L γ δ F layer hLayer base (tt 0)
        (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
        (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) p)
      (fun v => tRow RD hG L γ δ F layer hLayer base (tt 0)
        (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
        (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) v)
      (fun ρ => (natCR3 hM9 B hG W wN wDec bk (assemblyTimeConstraints hM9 B) g g' RD L γ δ F layer hLayer).W ρ
        ((natCR3 hM9 B hG W wN wDec bk (assemblyTimeConstraints hM9 B) g g' RD L γ δ F layer hLayer).clock τ tt ρ)
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
          sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1)
        (rowMom (engDatum hM9 B hG W wN wDec bk (assemblyTimeConstraints hM9 B) g g') L x
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) ρ))
      (fun _ => 1) (fun _ => 1)
      (fun v => ((qRow_eq_natCR3 hM9 B hG W wN wDec bk (assemblyTimeConstraints hM9 B) g g' RD L γ δ F layer hLayer base
          (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) tt τ
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) v).trans
        (congrArg ((natCR3 hM9 B hG W wN wDec bk (assemblyTimeConstraints hM9 B) g g' RD L γ δ F layer hLayer).W (Sum.inl v) ((natCR3 hM9 B hG W wN wDec bk (assemblyTimeConstraints hM9 B) g g' RD L γ δ F layer hLayer).clock τ tt (Sum.inl v))
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1))
          (pairMom_eq hM9 B hG W wN wDec bk (assemblyTimeConstraints hM9 B) g g' hL base β hβ x v).symm)).trans
        (one_mul _).symm)
      (fun v => ((tRow_eq_natCR3 hM9 B hG W wN wDec bk (assemblyTimeConstraints hM9 B) g g' RD L γ δ F layer hLayer base
          (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) tt τ
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) v).trans
        (congrArg ((natCR3 hM9 B hG W wN wDec bk (assemblyTimeConstraints hM9 B) g g' RD L γ δ F layer hLayer).W (Sum.inr v) ((natCR3 hM9 B hG W wN wDec bk (assemblyTimeConstraints hM9 B) g g' RD L γ δ F layer hLayer).clock τ tt (Sum.inr v))
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1))
          (branchMom_eq hM9 B hG W wN wDec bk (assemblyTimeConstraints hM9 B) g g' hL base β hβ x v).symm)).trans
        (one_mul _).symm)
    simp only [Finset.prod_const_one, mul_one, one_mul] at h
    exact h

end WaveTurbulence.VineEstS5C.P4.W2
