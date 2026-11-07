/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Kernel
public import WaveTurbulence.Foundations.VineEst.VineEstS3.EpsLabels
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ConstraintsOK

/-! # Leaf lower children (TARGET vineest Step 3, the case `u_{21}` or `u_{22}` a leaf)

The kernel `K̃^U` does not depend on the time of an excluded lower child that is a leaf (`clLocalClock_congr`,
`clLocalTimeDomain_congr`, `clRecenteredLocalKernel_congr`), and the source clock domain is the `sumint` input domain
(up to a null set) as soon as the dummy time of a leaf child is at most the lower window end of the lower joint
(`assemblyTimeDomain_of_source'`, `integral_clockDomain_eq'`, `vineChain_eq_sumintForm'`, which drop `hb1/hb2` of V4).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.LGSpine VineParamContract TTree Reg
  Reg.Skeleton RegRed MeasureTheory
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The clocks do not see `t 1` (resp. `t 2`) when the excluded lower child is a leaf. -/
theorem clLocalClock_congr (R : CLRegionData G U a b) (t t' : Fin 3 → ℝ) (h0 : t 0 = t' 0)
    (hp : (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching ∨ t 1 = t' 1)
    (hn : (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching ∨ t 2 = t' 2)
    (τ : CLInternalTime R) : clLocalClock R t τ = clLocalClock R t' τ := by
  classical
  funext v
  unfold clLocalClock
  by_cases ha : v = a
  · simp only [ha, dite_true, h0]
  · by_cases hv : v ∈ U
    · simp only [ha, hv, dite_true, dite_false]
    · simp only [ha, hv, dite_false]
      by_cases h1 : v.toNode = b.child R.positive
      · have hb : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching := by
          have := v.2
          rw [← (congrArg Subtype.val h1)]
          exact this
        simp only [h1, ite_true]
        rcases hp with h | h
        · exact absurd hb h
        · exact h
      · simp only [h1, ite_false]
        by_cases h2 : v.toNode = b.child R.negative
        · have hb : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching := by
            have := v.2
            rw [← (congrArg Subtype.val h2)]
            exact this
          simp only [h2, ite_true]
          rcases hn with h | h
          · exact absurd hb h
          · exact h
        · simp only [h2, ite_false]



theorem clLocalTimeDomain_congr (R : CLRegionData G U a b) (layerB : GBranch G.tree → ℕ) (t t' : Fin 3 → ℝ)
    (h0 : t 0 = t' 0)
    (hp : (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching ∨ t 1 = t' 1)
    (hn : (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching ∨ t 2 = t' 2) :
    clLocalTimeDomain R layerB t = clLocalTimeDomain R layerB t' := by
  have hc := clLocalClock_congr R t t' h0 hp hn
  ext τ
  unfold clLocalTimeDomain
  simp only [Set.mem_ofPred_eq, hc, h0]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · constructor
    · intro h hb; rcases hp with h' | h'
      · exact absurd hb h'
      · rw [← h']; exact h hb
    · intro h hb; rcases hp with h' | h'
      · exact absurd hb h'
      · rw [h']; exact h hb
  · constructor
    · intro h hb; rcases hn with h' | h'
      · exact absurd hb h'
      · rw [← h']; exact h hb
    · intro h hb; rcases hn with h' | h'
      · exact absurd hb h'
      · rw [h']; exact h hb

theorem clLocalSummand_congr (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (boundary : Fin 4 → Mom d)
    (t t' : Fin 3 → ℝ) (h0 : t 0 = t' 0)
    (hp : (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching ∨ t 1 = t' 1)
    (hn : (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching ∨ t 2 = t' 2)
    (κ : CLLocalDecoration R L base boundary) (τ : CLInternalTime R) :
    clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ =
      clLocalSummand D hG R L γ δ F layer hLayer base boundary t' κ τ := by
  have hc := clLocalClock_congr R t t' h0 hp hn
  have hd := clLocalTimeDomain_congr R (fun v => layer (D.coreBranch hG v).toNode) t t' h0 hp hn
  unfold clLocalSummand clLocalStarProduct
  simp only [hc, hd, h0]

theorem clRecenteredLocalKernel_congr (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (tU tP tN tP' tN' : ℝ) (e f g h : Mom d)
    (hp : (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching ∨ tP = tP')
    (hn : (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching ∨ tN = tN') :
    clRecenteredLocalKernel D hG R L γ δ F layer hLayer base tU tP tN e f g h =
      clRecenteredLocalKernel D hG R L γ δ F layer hLayer base tU tP' tN' e f g h := by
  unfold clRecenteredLocalKernel clLocalKernel
  congr 2
  refine tsum_congr fun κ => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  exact clLocalSummand_congr D hG R L γ δ F layer hLayer base ![e,f,g,h] ![tU,tP,tN] ![tU,tP',tN'] rfl hp hn κ τ


variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n)

/-- Source clock domain `⊆` sumint input domain, when each excluded lower child is a branch or its (dummy) time is
at most the lower window end `q_b` of the lower joint (so `t' ≤ q_b < τ_b`). -/
theorem assemblyTimeDomain_of_source' (hI : 0 < (assemblyShape hM9 B).I) (layerB : GBranch G.tree → ℕ)
    (t : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ)
    (hp : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      t 1 ≤ assemblyTimeQ hM9 B layerB (.inl ⟨⟨0,hI⟩,0⟩))
    (hn : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      t 2 ≤ assemblyTimeQ hM9 B layerB (.inl ⟨⟨0,hI⟩,0⟩))
    (h : assemblyClockEquiv hM9 B τ ∈ clLocalTimeDomain R layerB t) :
    τ ∈ assemblyTimeDomain hM9 B layerB hI t := by
  obtain ⟨hmain, hpos, hneg⟩ := h
  have hslot : ∀ s, (assemblyClockEquiv hM9 B τ) (assemblyClockAtomEquiv hM9 B s) = τ s :=
    fun s => assemblyClock_apply_slot hM9 B t τ s
  have hlt : ∀ s, τ s < t 0 := by
    intro s
    have hs' := Finset.mem_erase.mp (assemblyClockAtomEquiv hM9 B s).2
    have hyp : ∀ v ∈ U, v ≠ a → clLocalClock R t (assemblyClockEquiv hM9 B τ) v <
        parentClock (t 0) (clLocalClock R t (assemblyClockEquiv hM9 B τ)) v.toNode := by
      intro v hv hva
      have hv' : v ∈ clInteriorBranches R := Finset.mem_erase.mpr ⟨hva, hv⟩
      have e := clLocalClock_internal R t (assemblyClockEquiv hM9 B τ) ⟨v, hv'⟩
      have := (hmain ⟨v, hv'⟩).2.2.2
      rwa [← e] at this
    have h0 := interior_clock_lt_top B.isBlock R (t 0) (clLocalClock R t (assemblyClockEquiv hM9 B τ))
      (clLocalClock_upper R t _) hyp _ _ rfl hs'.2 hs'.1
    rwa [clLocalClock_slot hM9 B t τ s] at h0
  have hb : (assemblyClockAtomEquiv hM9 B (.inl ⟨⟨0,hI⟩,0⟩)).1 = b := assemblyClockAtom_first hM9 B hI
  have hbclock : clLocalClock R t (assemblyClockEquiv hM9 B τ) b = τ (.inl ⟨⟨0,hI⟩,0⟩) := by
    have := clLocalClock_slot hM9 B t τ (.inl ⟨⟨0,hI⟩,0⟩)
    rwa [hb] at this
  have hw0 : (assemblyTimeQ hM9 B layerB (.inl ⟨⟨0,hI⟩,0⟩) : ℝ) < τ (.inl ⟨⟨0,hI⟩,0⟩) := by
    have h := hmain (assemblyClockAtomEquiv hM9 B (.inl ⟨⟨0,hI⟩,0⟩))
    rw [hslot] at h
    exact h.1
  refine ⟨fun s => ?_, ?_, fun c hc => ?_⟩
  · have h := hmain (assemblyClockAtomEquiv hM9 B s)
    rw [hslot s] at h
    exact ⟨h.1.le, h.2.1.le, hlt s⟩
  · rw [max_lt_iff]
    refine ⟨?_, ?_⟩
    · rcases hp with hb1 | hle
      · rw [← hbclock]; exact hpos hb1
      · exact lt_of_le_of_lt hle hw0
    · rcases hn with hb2 | hle
      · rw [← hbclock]; exact hneg hb2
      · exact lt_of_le_of_lt hle hw0
  · have h1 := (hmain (assemblyClockAtomEquiv hM9 B c.1)).2.2.2
    rw [hslot c.1, constraint_parent_clock hM9 B t τ c hc] at h1
    exact h1

theorem integral_clockDomain_eq' (hI : 0 < (assemblyShape hM9 B).I) (layerB : GBranch G.tree → ℕ)
    (t : Fin 3 → ℝ)
    (hp : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      t 1 ≤ assemblyTimeQ hM9 B layerB (.inl ⟨⟨0,hI⟩,0⟩))
    (hn : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      t 2 ≤ assemblyTimeQ hM9 B layerB (.inl ⟨⟨0,hI⟩,0⟩))
    (f : ((assemblyShape hM9 B).TVar → ℝ) → ℂ) :
    ∫ τ, (assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R layerB t).indicator f τ =
      ∫ τ in assemblyTimeDomain hM9 B layerB hI t, f τ := by
  rw [← integral_indicator (measurableSet_assemblyTimeDomain hM9 B hI layerB t)]
  refine integral_congr_ae ?_
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
    exact assemblyTimeDomain_of_source' hM9 B hI layerB t τ hp hn h



/-- `vineChain_eq_sumintForm` without `hb1/hb2`: the lower children may be leaves provided their dummy times do not
exceed the lower window end of the lower joint. -/
theorem vineChain_eq_sumintForm' (D : ReconstructionData G) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer)
    (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (D.coreBranch hG v).toNode))
    (hok : ConstraintsOK hM9 B W)
    (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (t : Fin 3 → ℝ)
    (hp : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      t 1 ≤ assemblyTimeQ hM9 B (fun v => layer (D.coreBranch hG v).toNode)
        (.inl ⟨⟨0,assemblyShape_I_pos hM9 B⟩,0⟩))
    (hn : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      t 2 ≤ assemblyTimeQ hM9 B (fun v => layer (D.coreBranch hG v).toNode)
        (.inl ⟨⟨0,assemblyShape_I_pos hM9 B⟩,0⟩)) :
    clRecenteredLocalKernel D hG R L γ δ F layer hLayer base (t 0) (t 1) (t 2)
      (base+latticePoint L (β 0)) (base+latticePoint L (β 1))
      (base+latticePoint L (β 2)) (base+latticePoint L (β 3)) =
    (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R *
      ∑' x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ),
        (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ) *
        ∫ τ in (sourceSumintDatum hM9 B hG W).timeDom (assemblyShape_I_pos hM9 B) (t 0) (t 1) (t 2),
          signedPhase (sourceSumintDatum hM9 B hG W)
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2*δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (t 0) τ *
            ∏ v, (assemblyWK hM9 B D hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
                ((sourceSumintDatum hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              assemblyWL hM9 B D hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
                ((sourceSumintDatum hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v)) := by
  rw [clLocalKernel_reindexed hL hM9 B D hG γ δ F layer hLayer base β hβ t]
  congr 1
  refine tsum_congr (fun x => ?_)
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun τ =>
    clLocalRecenteredSummand_sumint hM9 B D hG W hpar hbad hL γ δ η F layer hLayer base β hβ x t τ)),
    integral_const_mul,
    integral_clockDomain_eq' hM9 B (assemblyShape_I_pos hM9 B) _ t hp hn,
    ← setIntegral_timeDom_eq_assembly hM9 B hG W _ hq hok]


open WaveTurbulence.DegenVine in
/-- **The kernel as `coupling^{n₁} ζ · clockedExprEps`** at points of the `sumint` output set. -/
theorem kernel_eq_clockedExprEps' (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer)
    (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hok : ConstraintsOK hM9 B W)
    (tt : Fin 3 → ℝ)
    (hp : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      tt 1 ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0,assemblyShape_I_pos hM9 B⟩,0⟩))
    (hn : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      tt 2 ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0,assemblyShape_I_pos hM9 B⟩,0⟩)) (E : Fin 4 → Mom d)
    (hE : ∀ c, ∃ nv : Fin d → ℤ, E c = W.wBar + latticePoint L nv) (hgap : E 0 - E 1 = E 3 - E 2) :
    clRecenteredLocalKernel RD hG R L γ δ F layer hLayer W.wBar (tt 0) (tt 1) (tt 2)
        (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3) =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        clockedExprEps (fun v : ↥U => childLabel hM9 B hG v.1 0) (fun v : ↥U => childLabel hM9 B hG v.1 1)
          (fun v : ↥U => childLabel hM9 B hG v.1 2) (assemblyClocked hM9 B RD hG W L γ δ F layer hLayer)
          (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) (assemblyShape_I_pos hM9 B) L γ (2 * δ) η tt E := by
  obtain ⟨β, hβ, rfl⟩ := outSet_exists_beta hL (G.sign a.toNode) W.wBar E hE hgap
  have hfun : (fun c => sumintBoundary (G.sign a.toNode)
      (sumintBoundary (G.sign a.toNode) (fun j => W.wBar + latticePoint L (β j))) c) =
      fun j => W.wBar + latticePoint L (β j) := by
    rw [sumintBoundary_invol]
  have h0 := vineChain_eq_sumintForm' hM9 B RD hG W hpar hbad hL γ δ η F layer hLayer hq hok W.wBar β hβ tt hp hn
  have e0 : sumintBoundary (G.sign a.toNode)
      (sumintBoundary (G.sign a.toNode) (fun j => W.wBar + latticePoint L (β j))) 0 =
      W.wBar + latticePoint L (β 0) := by rw [sumintBoundary_invol]
  have e1 : sumintBoundary (G.sign a.toNode)
      (sumintBoundary (G.sign a.toNode) (fun j => W.wBar + latticePoint L (β j))) 1 =
      W.wBar + latticePoint L (β 1) := by rw [sumintBoundary_invol]
  have e2 : sumintBoundary (G.sign a.toNode)
      (sumintBoundary (G.sign a.toNode) (fun j => W.wBar + latticePoint L (β j))) 2 =
      W.wBar + latticePoint L (β 2) := by rw [sumintBoundary_invol]
  have e3 : sumintBoundary (G.sign a.toNode)
      (sumintBoundary (G.sign a.toNode) (fun j => W.wBar + latticePoint L (β j))) 3 =
      W.wBar + latticePoint L (β 3) := by rw [sumintBoundary_invol]
  rw [e0, e1, e2, e3, h0]
  unfold clockedExprEps
  congr 1
  refine tsum_congr fun x => ?_
  rw [clRegionalEpsilon_eq_epsOf hM9 B hG W hL W.wBar β hβ x]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  exact (clockedIntegrand_assembly hM9 B RD hG W L γ δ F layer hLayer _ _ γ (2 * δ) η x _ tt τ).symm


end WaveTurbulence.VineEstS3
