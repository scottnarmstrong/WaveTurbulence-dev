/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Dict3
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.TimeDomMeas

/-! # P2: `ExprAbs ⇒ LkAbs` (dictionary for the absolute convergence of an unrolled term)

`lkAbs_of_exprAbs`: if the clocked expression of the engine converges absolutely (`ExprAbs`, delivered by `vineLevel_abs`) then the local sum-integral
`lkRaw` of the summand `ψ` converges absolutely (`P3.LkAbs`: every decoration integrable, the integrals summable), under the dictionary hypotheses `DictHyp`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The indicator of the clock domain and of the assembly time domain agree a.e. -/
theorem indicator_clockDomain_ae (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hI : 0 < (assemblyShape hM9 B).I)
    (layerB : GBranch G.tree → ℕ) (t : Fin 3 → ℝ)
    (hb1 : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching)
    (hb2 : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching)
    (f : ((assemblyShape hM9 B).TVar → ℝ) → ℂ) :
    (assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R layerB t).indicator f =ᵐ[volume]
      (assemblyTimeDomain hM9 B layerB hI t).indicator f := by
  have hae : ∀ᵐ τ : (assemblyShape hM9 B).TVar → ℝ, ∀ s, τ s ≠ assemblyTimeQ hM9 B layerB s ∧
      τ s ≠ assemblyTimeQ hM9 B layerB s + 1 := by
    rw [ae_all_iff]
    intro s
    exact (Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) s _).and
      (Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) s _)
  filter_upwards [hae] with τ hτ
  by_cases hmem : τ ∈ assemblyTimeDomain hM9 B layerB hI t
  · rw [Set.indicator_of_mem hmem]
    exact Set.indicator_of_mem (s := assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R layerB t)
      (source_of_assemblyTimeDomain hM9 B hI layerB t τ hmem hτ) f
  · rw [Set.indicator_of_notMem hmem]
    refine Set.indicator_of_notMem (s := assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R layerB t)
      (fun h => hmem ?_) f
    exact assemblyTimeDomain_of_source hM9 B hI layerB t τ hb1 hb2 h

theorem lkAbs_of_exprAbs (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (Φ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → CLInternalTime R → ℂ)
    (WKg : (assemblyShape hM9 B).VIdx → (Fin 3 → ℝ) → CLInternalTime R → Mom d → Mom d → ℂ)
    (WLg : (assemblyShape hM9 B).VIdx → (Fin 3 → ℝ) → CLInternalTime R → Mom d → ℂ)
    (layer0 : GBranch G.tree → ℕ) (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d) (hΦ : RowFactorizationR hM9 B hG L base Φ WKg WLg)
    (hq : W.q = assemblyTimeQ hM9 B layer0) (hc : W.constraints = assemblyTimeConstraints hM9 B)
    (hb1 : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching)
    (hb2 : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching)
    (ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
    (hψ : ∀ (β' : Fin 4 → Mom d) (κ : CLLocalDecoration R L base β') (t : Fin 3 → ℝ) (τ : CLInternalTime R),
      ψ (clExtendIndices R κ.1) t (clLocalClock R t τ) = clLocalSummandGen R Φ layer0 L γ δ base β' t κ τ)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (Mx : CharMix (assemblyShape hM9 B) d) (cr : ClockedRows3 (engDatum hM9 B hG W wN wDec bk cons g g'))
    (hD : DictHyp hM9 B hG W hL γ δ η base β hβ tt WKg WLg wN wDec bk cons g g' Mx cr)
    (hE : ExprAbs Mx cr (assemblyShape_I_pos hM9 B) L γ (2 * δ) η tt
      (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))) :
    P3.LkAbs R L base ψ tt (sumintBoundary (G.sign a.toNode)
      (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))) := by
  classical
  obtain ⟨hMx, hint, hsub, hvan⟩ := hD
  rw [sumintBoundary_invol]
  set e := clNormalizedChainEquiv hL B base β hβ hM9 with he
  set c : ℂ := recFac (G.sign a.toNode) (G.sign a.toNode) L γ δ tt
    (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) with hcdef
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have hcEq : c = Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * tt 0 *
      boundaryEnergyFromMomenta (G.sign a.toNode) (base + latticePoint L (β 0)) (base + latticePoint L (β 1))
        (base + latticePoint L (β 2)) (base + latticePoint L (β 3)) : ℝ) : ℂ) * Complex.I) := by
    simp only [hcdef, recFac, sumintBoundary_invol]
  have key : ∀ (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (τ : (assemblyShape hM9 B).TVar → ℝ),
      c * ψ (clExtendIndices R (e.symm x).1) tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) =
        (clRegionalEpsilon G U (clExtendIndices R (e.symm x).1) : ℂ) *
        ((assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R layer0 tt).indicator
          (fun τ => signedPhase (sourceSumintDatum hM9 B hG W)
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2*δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (tt 0) τ *
            ∏ v, (WKg v tt (assemblyClockEquiv hM9 B τ) (bgap (G.sign a.toNode) L base β)
                ((sourceSumintDatum hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              WLg v tt (assemblyClockEquiv hM9 B τ)
                ((sourceSumintDatum hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v))) τ) := by
    intro x τ
    rw [hψ _ (e.symm x) tt (assemblyClockEquiv hM9 B τ), hcEq]
    have h1 := clLocalSummandGen_recenter B.isBlock R Φ layer0 L γ δ base (fun j => base + latticePoint L (β j)) tt
      (e.symm x) (assemblyClockEquiv hM9 B τ)
    have h2 := clLocalRecenteredSummandGenR_sumint hM9 B hG Φ WKg WLg layer0 W hpar hbad hL γ δ η base hΦ β hβ x tt τ
    exact h1.trans h2
  set S := (sourceSumintDatum hM9 B hG W).timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) with hS
  set S' := (engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) with hS'
  have hSm : MeasurableSet S := WaveTurbulence.VineEstS3.Eng.measurableSet_timeDom _ _ _ _ _
  have hS'm : MeasurableSet S' := WaveTurbulence.VineEstS3Par.Eng.measurableSet_timeDom _ _ _ _ _
  have hSeq : S = assemblyTimeDomain hM9 B layer0 (assemblyShape_I_pos hM9 B) tt :=
    timeDom_eq_assemblyTimeDomain hM9 B hG W layer0 hq hc (assemblyShape_I_pos hM9 B) tt
  set kk : ℂ := ((kind1Pref (D := engDatum hM9 B hG W wN wDec bk cons g g')
    (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) : ℝ) : ℂ) with hkk
  have hGint : ∀ x, IntegrableOn (fun τ => signedPhase (sourceSumintDatum hM9 B hG W)
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2*δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (tt 0) τ *
            ∏ v, (WKg v tt (assemblyClockEquiv hM9 B τ) (bgap (G.sign a.toNode) L base β)
                ((sourceSumintDatum hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              WLg v tt (assemblyClockEquiv hM9 B τ)
                ((sourceSumintDatum hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v))) S := by
    intro x
    have h1 := ((hE.1 x).const_mul kk).congr (hint x)
    have h2 : IntegrableOn (fun τ => signedPhase (sourceSumintDatum hM9 B hG W)
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2*δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (tt 0) τ *
            ∏ v, (WKg v tt (assemblyClockEquiv hM9 B τ) (bgap (G.sign a.toNode) L base β)
                ((sourceSumintDatum hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              WLg v tt (assemblyClockEquiv hM9 B τ)
                ((sourceSumintDatum hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v))) (S \ S') :=
      (integrableOn_zero).congr_fun_ae ((ae_restrict_iff' (hSm.diff hS'm)).2
        (by filter_upwards [hvan x] with τ h hτ; exact (h hτ.1 hτ.2).symm))
    rw [← Set.union_sdiff_cancel hsub]
    exact IntegrableOn.union h1 h2
  have hfun : ∀ x, ((fun τ => ψ (clExtendIndices R (e.symm x).1) tt (clLocalClock R tt τ)) ∘ assemblyClockEquiv hM9 B) =
      fun τ' => c⁻¹ * ((clRegionalEpsilon G U (clExtendIndices R (e.symm x).1) : ℂ) *
        (assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R layer0 tt).indicator
          (fun τ => signedPhase (sourceSumintDatum hM9 B hG W)
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2*δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (tt 0) τ *
            ∏ v, (WKg v tt (assemblyClockEquiv hM9 B τ) (bgap (G.sign a.toNode) L base β)
                ((sourceSumintDatum hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              WLg v tt (assemblyClockEquiv hM9 B τ)
                ((sourceSumintDatum hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v))) τ') := by
    intro x
    funext τ'
    simp only [Function.comp]
    rw [← key x τ', ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  refine ⟨fun κ => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ : ∃ x, κ = e.symm x := ⟨e κ, (e.symm_apply_apply κ).symm⟩
    rw [← (assemblyClock_measurePreserving hM9 B).integrable_comp_emb (assemblyClockEquiv hM9 B).measurableEmbedding, hfun x]
    refine Integrable.const_mul (Integrable.const_mul ?_ _) _
    refine Integrable.congr ?_ (indicator_clockDomain_ae hM9 B (assemblyShape_I_pos hM9 B) layer0 tt hb1 hb2 _).symm
    rw [← hSeq]
    exact (integrable_indicator_iff hSm).2 (hGint x)
  · have hval : ∀ x, ∫ τ : CLInternalTime R, ψ (clExtendIndices R (e.symm x).1) tt (clLocalClock R tt τ) =
        (c⁻¹ * kk) * (Mx.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x *
          ∫ τ in S', clockedIntegrand3 cr L γ (2 * δ) η x
            (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) tt τ) := by
      intro x
      rw [assemblyClock_integral hM9 B (fun τ => ψ (clExtendIndices R (e.symm x).1) tt (clLocalClock R tt τ))]
      show ∫ τ, ((fun τ => ψ (clExtendIndices R (e.symm x).1) tt (clLocalClock R tt τ)) ∘ assemblyClockEquiv hM9 B) τ = _
      rw [hfun x, integral_const_mul, integral_const_mul,
        integral_clockDomain_eq hM9 B (assemblyShape_I_pos hM9 B) layer0 tt hb1 hb2, ← hSeq, ← hMx x]
      have key2 := setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := volume) hSm.nullMeasurableSet hsub
        (f := fun τ => signedPhase (sourceSumintDatum hM9 B hG W)
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2*δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (tt 0) τ *
            ∏ v, (WKg v tt (assemblyClockEquiv hM9 B τ) (bgap (G.sign a.toNode) L base β)
                ((sourceSumintDatum hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              WLg v tt (assemblyClockEquiv hM9 B τ)
                ((sourceSumintDatum hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v)))
        (by filter_upwards [hvan x] with τ h hτ; exact h hτ.1 hτ.2)
      erw [key2]
      have key3 : ∫ τ in S', (fun τ => signedPhase (sourceSumintDatum hM9 B hG W)
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2*δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (tt 0) τ *
            ∏ v, (WKg v tt (assemblyClockEquiv hM9 B τ) (bgap (G.sign a.toNode) L base β)
                ((sourceSumintDatum hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              WLg v tt (assemblyClockEquiv hM9 B τ)
                ((sourceSumintDatum hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v))) τ = kk * ∫ τ in S', clockedIntegrand3 cr L γ (2 * δ) η x
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) tt τ := by
        rw [← integral_const_mul]
        exact integral_congr_ae ((hint x).mono fun τ h => h.symm)
      erw [key3]
      ring
    have hsum := (hE.2.mul_left (c⁻¹ * kk))
    have : Summable fun x => ∫ τ : CLInternalTime R, ψ (clExtendIndices R (e.symm x).1) tt (clLocalClock R tt τ) := by
      refine hsum.congr fun x => ?_
      exact (hval x).symm
    refine (Equiv.summable_iff e.symm).1 ?_
    exact this

end WaveTurbulence.VineEstS5C.P2
