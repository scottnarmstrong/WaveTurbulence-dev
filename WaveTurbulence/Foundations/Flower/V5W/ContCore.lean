/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W.Clocked
public import WaveTurbulence.Foundations.Flower.V5W.RowData

/-! # V5W-0, row 0c (part 2): continuity of the recentered weighted member kernel

Weighted copies of main's `Cont.clockedExprEpsM`, `continuousOn_clockedExprEpsM`, `kernelMod_eq_clockedExprEpsM`,
`clLocalSummand_congr`, `clRecenteredLocalKernelModC_congr` and `clRecenteredMod_continuousOn` (Cont/ModKernel,
Cont/ModCore, VineEstS3/LeafChild):

* `clockedExprEpsMX`: the clocked expression with a bounded multiplier `mx x` of the lattice point inside the lattice sum
  (the region multiplier of the member, in normalized chain coordinates) and the time factor `m` (the R58 modulation);
* `kernelFW_eq_clockedExprEpsMX`: the recentered weighted member kernel at an output `E = sumintBoundary ζ (w̄ + β)`;
* `clRecenteredFW_continuousOn`: continuity in the three exterior clocks on the closed output cube, for every output.
  The coherent rows are bounded by main's gates (`coupleRow_leaf_le`, `treeRow_leaf_le`), the incoherent rows by
  INC-TOP's `TopIncoherentDecayAtR` (finite `XNormRestr`, hence pointwise decay by `norm_le_decay_of_XNormRestr`), with
  the time continuity of row 0a (`continuous_coupleLeavesTop_time`, `continuous_treeLeavesTop_time`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.DegenVine WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory Filter
  Topology
open WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineC
  WaveTurbulence.Flower.Stage1W
open scoped ENNReal

section Expr
variable {d : ℕ}

/-- The clocked expression with a multiplier `mx x` of the lattice point and a factor `m tt τ` in the time integrand. -/
def clockedExprEpsMX {ι : Type*} [Fintype ι] {D : SumintDatum d} (l₁ l₂ l₃ : ι → Row D ⊕ Fin 4)
    (cr : ClockedRows D) (coreFirstSign coreSign : Fin D.S.I → ℤˣ) (hI : 0 < D.S.I) (L γ δ η : ℝ)
    (mx : (D.S.VIdx → (Fin d → ℤ)) → ℂ) (m : (Fin 3 → ℝ) → (D.S.TVar → ℝ) → ℂ) (tt : Fin 3 → ℝ)
    (E : Fin 4 → Mom d) : ℂ :=
  ∑' x : D.S.VIdx → (Fin d → ℤ), (epsOf D L l₁ l₂ l₃ x E : ℂ) * mx x *
    ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2), m tt τ * clockedIntegrand cr coreFirstSign coreSign L γ δ η x E tt τ

theorem continuousOn_clockedExprEpsMX {ι : Type*} [Fintype ι] {D : SumintDatum d} (hbad : ∀ i, D.badKind i ≠ 2)
    (l₁ l₂ l₃ : ι → Row D ⊕ Fin 4) (cr : ClockedRows D) (cfs cs : Fin D.S.I → ℤˣ) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (E : Fin 4 → Mom d) (mx : (D.S.VIdx → (Fin d → ℤ)) → ℂ) (Cm : ℝ) (hCm : 0 ≤ Cm)
    (hmx : ∀ x, ‖mx x‖ ≤ Cm) (m : (Fin 3 → ℝ) → (D.S.TVar → ℝ) → ℂ)
    (hm : Continuous fun p : (Fin 3 → ℝ) × (D.S.TVar → ℝ) => m p.1 p.2) (hm1 : ∀ tt τ, ‖m tt τ‖ ≤ 1)
    (hcont : ∀ ρ k, Continuous fun c => cr.W ρ c k)
    (C : Set (Fin 3 → ℝ)) (Bx : (D.S.VIdx → (Fin d → ℤ)) → ℝ) (hBx : Summable Bx) (hBx0 : ∀ x, 0 ≤ Bx x)
    (hbd : ∀ x, ∀ tt ∈ C, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2),
      ∏ ρ, ‖cr.W ρ (cr.clock τ tt ρ) (rowMom D L x E ρ)‖ ≤ Bx x) :
    ContinuousOn (fun tt => clockedExprEpsMX l₁ l₂ l₃ cr cfs cs hI L γ δ η mx m tt E) C := by
  unfold clockedExprEpsMX
  have hjoint := fun x => (hm.mul (continuous_integrand_joint hbad cr cfs cs L γ δ η x E hcont))
  have hnorm : ∀ x tt (htt : tt ∈ C) τ (hτ : τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2)),
      ‖m tt τ * clockedIntegrand cr cfs cs L γ δ η x E tt τ‖ ≤ Bx x := by
    intro x tt htt τ hτ
    unfold clockedIntegrand
    rw [norm_mul, norm_mul, norm_prod]
    calc ‖m tt τ‖ * (‖signedPhase D cfs cs L γ δ η x (E 0 - E 1) (tt 0) τ‖ *
          ∏ ρ, ‖cr.W ρ (cr.clock τ tt ρ) (rowMom D L x E ρ)‖)
        ≤ 1 * (1 * ∏ ρ, ‖cr.W ρ (cr.clock τ tt ρ) (rowMom D L x E ρ)‖) := by
          refine mul_le_mul (hm1 tt τ) (mul_le_mul_of_nonneg_right
            (norm_signedPhase_le D hbad cfs cs L γ δ η x _ _ _) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
            (by positivity) zero_le_one
      _ ≤ Bx x := by rw [one_mul, one_mul]; exact hbd x tt htt τ hτ
  refine continuousOn_tsum (u := fun x => Cm * Bx x) (fun x => ?_) (hBx.mul_left Cm) (fun x tt htt => ?_)
  · refine continuousOn_const.mul (continuousOn_timeDom_integral D hI C
      (fun tt τ => m tt τ * clockedIntegrand cr cfs cs L γ δ η x E tt τ) (hjoint x) (Bx x) ?_)
    intro tt htt τ hτ
    exact hnorm x tt htt τ hτ
  · rw [norm_mul, norm_mul]
    have hε : ‖((epsOf D L l₁ l₂ l₃ x E : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_epsOf_le_one D L l₁ l₂ l₃ x E
    have hI' : ‖∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2), m tt τ * clockedIntegrand cr cfs cs L γ δ η x E tt τ‖ ≤
        Bx x := by
      have hvol : volume (D.timeDom hI (tt 0) (tt 1) (tt 2)) < ⊤ :=
        lt_of_le_of_lt (volume_timeDom_le D hI _ _ _) ENNReal.one_lt_top
      have := norm_setIntegral_le_of_norm_le_const (μ := volume) hvol
        (C := Bx x) (f := fun τ => m tt τ * clockedIntegrand cr cfs cs L γ δ η x E tt τ)
        (fun τ hτ => hnorm x tt htt τ hτ)
      refine this.trans ?_
      have : (volume.real (D.timeDom hI (tt 0) (tt 1) (tt 2))) ≤ 1 := by
        have h1 := volume_timeDom_le D hI (tt 0) (tt 1) (tt 2)
        simp only [Measure.real]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h1)
      exact mul_le_of_le_one_right (hBx0 x) this
    calc _ ≤ 1 * Cm * Bx x := mul_le_mul (mul_le_mul hε (hmx x) (norm_nonneg _) zero_le_one) hI' (norm_nonneg _)
          (by positivity)
      _ = Cm * Bx x := by ring

end Expr

section Ident
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **The recentered weighted member kernel as `coupling^{n₁} ζ · clockedExprEpsMX`**, at an output
`E = sumintBoundary ζ (w̄ + β)` (copy of `Cont.kernelMod_eq_clockedExprEpsM`). -/
theorem kernelFW_eq_clockedExprEpsMX (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (pw : ℕ) (g : Mom d → ℂ)
    (RD : ReconstructionData G) (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (γ δ η lam : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer)
    (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hok : ConstraintsOK hM9 B W) (m : (GNode G.tree → Fin d → ℤ) → ℂ)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (hp : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      tt 1 ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩))
    (hn : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      tt 2 ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩)) :
    recPhase (G.sign a.toNode) L γ δ (tt 0) (W.wBar + latticePoint L (β 0)) (W.wBar + latticePoint L (β 1))
        (W.wBar + latticePoint L (β 2)) (W.wBar + latticePoint L (β 3)) *
      clLocalKernelFW pw g RD hG R L γ δ F layer hLayer W.wBar m (modW lam) (tt 0) (tt 1) (tt 2)
        (W.wBar + latticePoint L (β 0)) (W.wBar + latticePoint L (β 1))
        (W.wBar + latticePoint L (β 2)) (W.wBar + latticePoint L (β 3)) =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        clockedExprEpsMX (fun v : ↥U => childLabel hM9 B hG v.1 0) (fun v : ↥U => childLabel hM9 B hG v.1 1)
          (fun v : ↥U => childLabel hM9 B hG v.1 2) (assemblyClockedFW hM9 B RD hG W pw g L γ δ F layer hLayer)
          (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) (assemblyShape_I_pos hM9 B) L γ (2 * δ) η
          (fun x => m (clExtendIndices R ((clNormalizedChainEquiv hL B W.wBar β hβ hM9).symm x).1))
          (fun (_ : Fin 3 → ℝ) (τ : (sourceSumintDatum hM9 B hG W).S.TVar → ℝ) =>
            Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩) : ℝ) : ℂ) * Complex.I)) tt
          (sumintBoundary (G.sign a.toNode) (fun j => W.wBar + latticePoint L (β j))) := by
  rw [vineChainFW_eq_sumintForm' hM9 B pw g RD hG W hpar hbad hL γ δ η F layer hLayer hq hok W.wBar m lam β hβ tt
    hp hn]
  unfold clockedExprEpsMX
  congr 1
  refine tsum_congr fun x => ?_
  rw [clRegionalEpsilon_eq_epsOf hM9 B hG W hL W.wBar β hβ x]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  beta_reduce
  congr 1
  exact (clockedIntegrand_assemblyFW hM9 B RD hG W pw g L γ δ F layer hLayer _ _ γ (2 * δ) η x _ tt τ).symm

end Ident

section Congr
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clLocalSummandFW_congr (pw : ℕ) (g : Mom d → ℂ) (D : ReconstructionData G) (hG : G.IsPlain)
    (R : CLRegionData G U a b) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (boundary : Fin 4 → Mom d)
    (t t' : Fin 3 → ℝ) (h0 : t 0 = t' 0)
    (hp : (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching ∨ t 1 = t' 1)
    (hn : (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching ∨ t 2 = t' 2)
    (κ : CLLocalDecoration R L base boundary) (τ : CLInternalTime R) :
    clLocalSummandFW pw g D hG R L γ δ F layer hLayer base boundary t κ τ =
      clLocalSummandFW pw g D hG R L γ δ F layer hLayer base boundary t' κ τ := by
  have hc := clLocalClock_congr R t t' h0 hp hn
  have hd := clLocalTimeDomain_congr R (fun v => layer (D.coreBranch hG v).toNode) t t' h0 hp hn
  unfold clLocalSummandFW clLocalStarProductFW
  simp only [hc, hd, h0]

/-- The recentered weighted kernel does not see the time of a leaf lower child. -/
theorem recPhase_clLocalKernelFW_congr (pw : ℕ) (g : Mom d → ℂ) (D : ReconstructionData G) (hG : G.IsPlain)
    (R : CLRegionData G U a b) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (m : (GNode G.tree → Fin d → ℤ) → ℂ) (W : ℝ → ℂ)
    (tU tP tN tP' tN' : ℝ) (e f g' h : Mom d)
    (hp : (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching ∨ tP = tP')
    (hn : (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching ∨ tN = tN') :
    recPhase (G.sign a.toNode) L γ δ tU e f g' h *
        clLocalKernelFW pw g D hG R L γ δ F layer hLayer base m W tU tP tN e f g' h =
      recPhase (G.sign a.toNode) L γ δ tU e f g' h *
        clLocalKernelFW pw g D hG R L γ δ F layer hLayer base m W tU tP' tN' e f g' h := by
  congr 1
  unfold clLocalKernelFW
  congr 1
  refine tsum_congr fun κ => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  have h0 : ![tU, tP, tN] 0 = ![tU, tP', tN'] 0 := rfl
  have e1 := clLocalClock_congr R ![tU, tP, tN] ![tU, tP', tN'] h0 hp hn τ
  have e2 := clLocalSummandFW_congr pw g D hG R L γ δ F layer hLayer base ![e, f, g', h] ![tU, tP, tN]
    ![tU, tP', tN'] rfl hp hn κ τ
  simp only [e1, e2]

end Congr

section Rows
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
  (W : SumintWeightClockData (assemblyShape hM9 B) d)

theorem exists_lt_ofReal {X : ℝ≥0∞} (hX : X ≠ ⊤) : ∃ M : ℝ, 0 < M ∧ X < ENNReal.ofReal M := by
  refine ⟨X.toReal + 1, add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg one_pos, ?_⟩
  calc X = ENNReal.ofReal X.toReal := (ENNReal.ofReal_toReal hX).symm
    _ < ENNReal.ofReal (X.toReal + 1) :=
      (ENNReal.ofReal_lt_ofReal_iff (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg one_pos)).2 (by linarith)

/-- The root parent layers of the incoherent couple row of a `sumint` row are its clock-slot layers. -/
theorem coupleRootParents_rowQ (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (pw : ℕ)
    (v : (assemblyShape hM9 B).VIdx) :
    coupleRootParents pw RD hG layer hLayer (assemblyPairOf hM9 B hG v).1 0 =
        (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).1 ∧
      coupleRootParents pw RD hG layer hLayer (assemblyPairOf hM9 B hG v).1 1 =
        (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).2 := by
  rw [rowQ_inl_eq hM9 B RD hG layer hLayer W hq hqo L γ δ F v]
  have hp := pairLeaf_ne (a := a) hG (assemblyPairOf hM9 B hG v)
  have h1 := (clRegionalPair_realization hG _ (assemblyPairOf hM9 B hG v).2).1
  have h2 := (clRegionalPair_realization hG _ (assemblyPairOf hM9 B hG v).2).2
  obtain ⟨n1, _⟩ := cl_realization_parent B.isBlock R _ h1 hp.1
  obtain ⟨n2, _⟩ := cl_realization_parent B.isBlock R _ h2 hp.2
  constructor
  · rw [coupleRootParents_zero RD hG layer hLayer pw _ _ _ (Mole.parent_child_eq_node _ n1).symm]
    simp [pairQ, parentCoreLayer, n1]
  · rw [coupleRootParents_one RD hG layer hLayer pw _ _ _ (Mole.parent_child_eq_node _ n2).symm]
    simp [pairQ, parentCoreLayer, n2]

/-- The root parent layer of the incoherent tree row of a `sumint` row is its first clock-slot layer. -/
theorem treeRootParent_rowQ (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (pw : ℕ)
    (v : (assemblyShape hM9 B).VIdx) :
    treeRootParent pw RD hG layer hLayer (assemblyBranchOf hM9 B v).1 =
      (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).1 := by
  rw [rowQ_inr_eq hM9 B RD hG layer hLayer W hq hqo L γ δ F v]
  have hbr := (branch_mem_clRealizationNodes (assemblyBranchOf hM9 B v).1).mpr
    (Finset.mem_erase.mp (assemblyBranchOf hM9 B v).2).2
  have hne := interior_ne (assemblyBranchOf hM9 B v)
  obtain ⟨hn, _⟩ := cl_realization_parent B.isBlock R _ hbr hne
  rw [treeRootParent_eq RD hG layer hLayer pw _ _ _ (Mole.parent_child_eq_node _ hn).symm]
  simp [branchQ, parentCoreLayer, hn]

variable (pw : ℕ) (g : Mom d → ℂ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)

theorem assemblyClockedFW_inl_coh (v : (assemblyShape hM9 B).VIdx)
    (hc : coupleIncoh RD hG layer hLayer (assemblyPairOf hM9 B hG v).1 = 0) :
    (assemblyClockedFW hM9 B RD hG W pw g L γ δ F layer hLayer).W (Sum.inl v) =
      (assemblyClocked hM9 B RD hG W L γ δ F layer hLayer).W (Sum.inl v) := by
  funext c k
  show coupleRowFW pw g RD hG L γ δ F layer hLayer (assemblyPairOf hM9 B hG v).1 (c 0) (c 1) k = _
  unfold coupleRowFW
  rw [if_pos hc]
  rfl

theorem assemblyClockedFW_inr_coh (v : (assemblyShape hM9 B).VIdx)
    (hc : treeIncoh RD hG layer hLayer (assemblyBranchOf hM9 B v).1 = 0) :
    (assemblyClockedFW hM9 B RD hG W pw g L γ δ F layer hLayer).W (Sum.inr v) =
      (assemblyClocked hM9 B RD hG W L γ δ F layer hLayer).W (Sum.inr v) := by
  funext c k
  show treeRowFW pw g RD hG L γ δ F layer hLayer (assemblyBranchOf hM9 B v).1 (c 0) (c 1) k = _
  unfold treeRowFW
  rw [if_pos hc]
  rfl

theorem assemblyClockedFW_inl_incoh (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (v : (assemblyShape hM9 B).VIdx)
    (hc : coupleIncoh RD hG layer hLayer (assemblyPairOf hM9 B hG v).1 ≠ 0) :
    (assemblyClockedFW hM9 B RD hG W pw g L γ δ F layer hLayer).W (Sum.inl v) =
      fun ts k => coupleLeavesTopR L γ δ pw (fun _ => g) (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).1
        (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).2 (rowCoupleLG hM9 B RD hG layer hLayer v)
        (layerProfiles (rowCoupleLG hM9 B RD hG layer hLayer v) F) (ts 0) (ts 1) k := by
  obtain ⟨e0, e1⟩ := coupleRootParents_rowQ hM9 B RD hG layer hLayer W hq hqo L γ δ F pw v
  funext c k
  show coupleRowFW pw g RD hG L γ δ F layer hLayer (assemblyPairOf hM9 B hG v).1 (c 0) (c 1) k = _
  unfold coupleRowFW
  rw [if_neg hc, e0, e1]
  rfl

theorem assemblyClockedFW_inr_incoh (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (v : (assemblyShape hM9 B).VIdx)
    (hc : treeIncoh RD hG layer hLayer (assemblyBranchOf hM9 B v).1 ≠ 0) :
    (assemblyClockedFW hM9 B RD hG W pw g L γ δ F layer hLayer).W (Sum.inr v) =
      fun ts k => treeLeavesTop L γ δ pw g (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).1
        (rowTreeLG hM9 B RD hG layer hLayer v) (layerProfiles (rowTreeLG hM9 B RD hG layer hLayer v) F)
        (ts 0) (ts 1) k := by
  have e0 := treeRootParent_rowQ hM9 B RD hG layer hLayer W hq hqo L γ δ F pw v
  funext c k
  show treeRowFW pw g RD hG L γ δ F layer hLayer (assemblyBranchOf hM9 B v).1 (c 0) (c 1) k = _
  unfold treeRowFW
  rw [if_neg hc, e0]
  rfl

end Rows

end WaveTurbulence.Flower.V5W
