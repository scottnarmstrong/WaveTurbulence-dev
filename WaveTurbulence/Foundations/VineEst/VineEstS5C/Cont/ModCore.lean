/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.ModKernel

/-! # V5-CONT (R58), core for the modulated kernel

`clockedExprEpsM`, `continuousOn_clockedExprEpsM`, `kernelMod_eq_clockedExprEpsM`, and
`clRecenteredMod_continuousOn`: the modulated recentered kernel `clRecenteredLocalKernelModC` is continuous in the three
exterior clocks on the closed cube, for every `E` of the output set (same hypotheses as `clRecentered_continuousOn`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.Cont
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine
  WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory Filter Topology
open scoped ENNReal

section Expr
variable {d : ℕ}

/-- The clocked expression with a factor `m tt τ` in the time integrand. -/
noncomputable def clockedExprEpsM {ι : Type*} [Fintype ι] {D : SumintDatum d} (l₁ l₂ l₃ : ι → Row D ⊕ Fin 4)
    (cr : ClockedRows D) (coreFirstSign coreSign : Fin D.S.I → ℤˣ) (hI : 0 < D.S.I) (L γ δ η : ℝ)
    (m : (Fin 3 → ℝ) → (D.S.TVar → ℝ) → ℂ) (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d) : ℂ :=
  ∑' x : D.S.VIdx → (Fin d → ℤ), (epsOf D L l₁ l₂ l₃ x E : ℂ) * ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2),
    m tt τ * clockedIntegrand cr coreFirstSign coreSign L γ δ η x E tt τ

/-- The modulation factor in `sumint` coordinates: `e^{πiλ τ_{slot 0}}`. -/
theorem continuous_mlow {D : SumintDatum d} (lam : ℝ) (hI : 0 < D.S.I) :
    Continuous fun p : (Fin 3 → ℝ) × (D.S.TVar → ℝ) =>
      Complex.exp (((Real.pi * lam * p.2 (.inl ⟨⟨0, hI⟩, 0⟩) : ℝ) : ℂ) * Complex.I) := by
  fun_prop

theorem norm_mlow_le {D : SumintDatum d} (lam : ℝ) (hI : 0 < D.S.I) (_tt : Fin 3 → ℝ) (τ : D.S.TVar → ℝ) :
    ‖Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, hI⟩, 0⟩) : ℝ) : ℂ) * Complex.I)‖ ≤ 1 :=
  (Complex.norm_exp_ofReal_mul_I _).le

theorem continuousOn_clockedExprEpsM {ι : Type*} [Fintype ι] {D : SumintDatum d} (hbad : ∀ i, D.badKind i ≠ 2)
    (l₁ l₂ l₃ : ι → Row D ⊕ Fin 4) (cr : ClockedRows D) (cfs cs : Fin D.S.I → ℤˣ) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (E : Fin 4 → Mom d) (m : (Fin 3 → ℝ) → (D.S.TVar → ℝ) → ℂ)
    (hm : Continuous fun p : (Fin 3 → ℝ) × (D.S.TVar → ℝ) => m p.1 p.2) (hm1 : ∀ tt τ, ‖m tt τ‖ ≤ 1)
    (hcont : ∀ ρ k, Continuous fun c => cr.W ρ c k)
    (C : Set (Fin 3 → ℝ)) (Bx : (D.S.VIdx → (Fin d → ℤ)) → ℝ) (hBx : Summable Bx) (hBx0 : ∀ x, 0 ≤ Bx x)
    (hbd : ∀ x, ∀ tt ∈ C, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2),
      ∏ ρ, ‖cr.W ρ (cr.clock τ tt ρ) (rowMom D L x E ρ)‖ ≤ Bx x) :
    ContinuousOn (fun tt => clockedExprEpsM l₁ l₂ l₃ cr cfs cs hI L γ δ η m tt E) C := by
  unfold clockedExprEpsM
  have hjoint := fun x => (hm.mul (continuous_integrand_joint hbad cr cfs cs L γ δ η x E hcont))
  have hnorm : ∀ x tt (htt : tt ∈ C) τ (hτ : τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2)),
      ‖m tt τ * clockedIntegrand cr cfs cs L γ δ η x E tt τ‖ ≤ Bx x := by
    intro x tt htt τ hτ
    unfold clockedIntegrand
    rw [norm_mul, norm_mul, norm_prod]
    calc ‖m tt τ‖ * (‖signedPhase D cfs cs L γ δ η x (E 0 - E 1) (tt 0) τ‖ * ∏ ρ, ‖cr.W ρ (cr.clock τ tt ρ) (rowMom D L x E ρ)‖)
        ≤ 1 * (1 * ∏ ρ, ‖cr.W ρ (cr.clock τ tt ρ) (rowMom D L x E ρ)‖) := by
          refine mul_le_mul (hm1 tt τ) (mul_le_mul_of_nonneg_right
            (norm_signedPhase_le D hbad cfs cs L γ δ η x _ _ _) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
            (by positivity) zero_le_one
      _ ≤ Bx x := by rw [one_mul, one_mul]; exact hbd x tt htt τ hτ
  refine continuousOn_tsum (u := Bx) (fun x => ?_) hBx (fun x tt htt => ?_)
  · refine continuousOn_const.mul (continuousOn_timeDom_integral D hI C
      (fun tt τ => m tt τ * clockedIntegrand cr cfs cs L γ δ η x E tt τ) (hjoint x) (Bx x) ?_)
    intro tt htt τ hτ
    exact hnorm x tt htt τ hτ
  · rw [norm_mul]
    have hε : ‖((epsOf D L l₁ l₂ l₃ x E : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_epsOf_le_one D L l₁ l₂ l₃ x E
    have hI' : ‖∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2), m tt τ * clockedIntegrand cr cfs cs L γ δ η x E tt τ‖ ≤ Bx x := by
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
    calc _ ≤ 1 * Bx x := mul_le_mul hε hI' (norm_nonneg _) zero_le_one
      _ = Bx x := one_mul _

end Expr

section Ident
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **The modulated kernel as `coupling^{n₁} ζ · clockedExprEpsM`** at points of the `sumint` output set. -/
theorem kernelMod_eq_clockedExprEpsM (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (γ δ η lam : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer)
    (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hok : ConstraintsOK hM9 B W) (tt : Fin 3 → ℝ)
    (hp : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      tt 1 ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩))
    (hn : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      tt 2 ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩)) (E : Fin 4 → Mom d)
    (hE : ∀ c, ∃ nv : Fin d → ℤ, E c = W.wBar + latticePoint L nv) (hgap : E 0 - E 1 = E 3 - E 2) :
    clRecenteredLocalKernelModC RD hG R L γ δ F layer hLayer W.wBar lam (tt 0) (tt 1) (tt 2)
        (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3) =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        clockedExprEpsM (fun v : ↥U => childLabel hM9 B hG v.1 0) (fun v : ↥U => childLabel hM9 B hG v.1 1)
          (fun v : ↥U => childLabel hM9 B hG v.1 2) (assemblyClockedS hM9 B RD hG W L γ δ F layer hLayer)
          (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) (assemblyShape_I_pos hM9 B) L γ (2 * δ) η
          (fun (tt : Fin 3 → ℝ) (τ : (sourceSumintDatum hM9 B hG W).S.TVar → ℝ) =>
            Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩) : ℝ) : ℂ) * Complex.I)) tt E := by
  obtain ⟨β, hβ, rfl⟩ := outSet_exists_beta hL (G.sign a.toNode) W.wBar E hE hgap
  have h0 := vineChainMod_eq_sumintForm' hM9 B RD hG W hpar hbad hL γ δ η F layer hLayer hq hok W.wBar lam β hβ tt hp hn
  have e0 : ∀ j : Fin 4, sumintBoundary (G.sign a.toNode)
      (sumintBoundary (G.sign a.toNode) (fun j => W.wBar + latticePoint L (β j))) j =
      W.wBar + latticePoint L (β j) := fun j => by rw [sumintBoundary_invol]
  rw [e0 0, e0 1, e0 2, e0 3, h0]
  unfold clockedExprEpsM
  congr 1
  refine tsum_congr fun x => ?_
  rw [clRegionalEpsilon_eq_epsOf hM9 B hG W hL W.wBar β hβ x]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  beta_reduce
  congr 1
  exact (clockedIntegrand_assembly hM9 B RD hG W L γ δ F layer hLayer _ _ γ (2 * δ) η x _ tt τ).symm

end Ident

/-- **V5-CONT core.**  Continuity of the recentered local kernel in `(t₀,t₁,t₂)` on the closed cube, for each output
momentum of the output set.  Hypotheses are those of `step3AtLeafH` that concern the rows (gates, eligibility) and the
two leaf-child time conditions; the bad clause, the order bound and the engine bound are not needed. -/
theorem clRecenteredMod_continuousOn {P : WTParams} (lam : ℝ)
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
    (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
    {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
    (qOut : Fin 3 → ℕ) (centre : Fin 4 → Mom P.d) (wBar : Mom P.d)
    (badKind : Fin (assemblyShape hM9 B).I → Fin 4) (hbad2 : ∀ i, badKind i ≠ 2)
    (hel : ∀ v, CoupleEligible hM9 B RD hG (step3W hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.δ
          h layer hLayer (P.N (p + 1) ^ 4) p v ∧
        TreeEligible hM9 B RD hG (step3W hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.δ
          h layer hLayer (P.N (p + 1) ^ 4) p v)
    (hq1 : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      (qOut 1 : ℝ) ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩))
    (hq2 : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      (qOut 2 : ℝ) ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩)) :
    ∀ E ∈ outSet (step3D hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.η,
      ContinuousOn (fun tt : Fin 3 → ℝ => clRecenteredLocalKernelModC (rowSel := VineEst.RowSel.plain) RD hG R P.L P.γ P.δ h layer hLayer wBar lam
          (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
          (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3))
        (cubeSet (step3D hM9 B RD hG layer hLayer badKind qOut centre wBar).qOut) := by
  classical
  have hL0 : 0 < P.L := by linarith
  set W := step3W hM9 B RD hG layer hLayer badKind qOut centre wBar with hW
  set D := sourceSumintDatum hM9 B hG W with hD
  have hI := assemblyShape_I_pos hM9 B
  have hbad2' : ∀ i, D.badKind i ≠ 2 := fun i => hbad2 i
  have hqq : ∀ v, (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 ≤
      (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1 := fun v => (hel v).2.1
  have hres : ∀ ρ, XNormRestr (6 * P.η ^ 6) (30 * P.d) (rowOrder D ρ)
      (rowBx hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ) Set.univ
      ((assemblyClockedS hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ) <
      ENNReal.ofReal (2 * rowBoundH hM9 B RD hG layer hLayer P Bh W ρ) := by
    intro ρ
    rcases ρ with v | v
    · have h1 := coupleRow_leaf_le W hgate hinc hd hη6 hη2 hC hδ.le hL hw hp hB hlay v (hel v).1
      have hx : 0 < rowBoundH hM9 B RD hG layer hLayer P Bh W (Sum.inl v) :=
        mul_pos (rowB_pos hC hδ hL0 _ _) (rowCostH_pos hBpos hlay W _)
      refine h1.trans_lt ?_
      change ENNReal.ofReal (rowBoundH hM9 B RD hG layer hLayer P Bh W (Sum.inl v)) < _
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    · have h1 := treeRow_leaf_le W hgate hinc hd hη6 hη2 hC hδ.le hL hw hp hB hlay v (hel v).2
      have hx : 0 < rowBoundH hM9 B RD hG layer hLayer P Bh W (Sum.inr v) :=
        mul_pos (rowB_pos hC hδ hL0 _ _) (rowCostH_pos hBpos hlay W _)
      refine h1.trans_lt ?_
      change ENNReal.ofReal (rowBoundH hM9 B RD hG layer hLayer P Bh W (Sum.inr v)) < _
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hrb : ∀ ρ, 0 < rowBoundH hM9 B RD hG layer hLayer P Bh W ρ := by
    intro ρ; rcases ρ with v | v <;> exact mul_pos (rowB_pos hC hδ hL0 _ _) (rowCostH_pos hBpos hlay W _)
  have hrowdec : ∀ ρ (c : Fin 2 → ℝ), c ∈ closure (interior (rowBx hM9 B RD hG layer hLayer W P.L P.γ P.δ
      h ρ)) → ∀ k, ‖(assemblyClockedS hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ c k‖ ≤
      (2 * rowBoundH hM9 B RD hG layer hLayer P Bh W ρ) * decayWt D (30 * P.d) ρ k := by
    intro ρ c hc k
    have h := norm_le_decay_of_XNormRestr (θ := 6 * P.η ^ 6) (by positivity) (30 * P.d) (Eng.rowOrder D ρ) _ _
      (2 * rowBoundH hM9 B RD hG layer hLayer P Bh W ρ) (hres ρ) c hc k
      (rows_continuousH hB hd hL hlay W ρ k)
    rcases ρ with v | v
    · exact h
    · simpa [decayWt, Eng.rowOrder] using h
  set Bx : (D.S.VIdx → (Fin P.d → ℤ)) → (Fin 4 → Mom P.d) → ℝ := fun x E =>
    (∏ ρ, 2 * rowBoundH hM9 B RD hG layer hLayer P Bh W ρ) * ∏ ρ, decayWt D (30 * P.d) ρ (rowMom D P.L x E ρ)
    with hBx
  have hBxs : ∀ E, Summable fun x => Bx x E := fun E =>
    (summable_decayWt D hL0 (by omega : P.d + 1 ≤ 30 * P.d) E).mul_left _
  have hBx0 : ∀ x E, 0 ≤ Bx x E := fun x E =>
    mul_nonneg (Finset.prod_nonneg fun ρ _ => by have := hrb ρ; linarith)
      (Finset.prod_nonneg fun ρ _ => decayWt_nonneg D _ ρ _)
  have hbd : ∀ E x, ∀ tt ∈ cubeSet D.qOut, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2),
      ∏ ρ, ‖(assemblyClockedS hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ
        ((assemblyClockedS hM9 B RD hG W P.L P.γ P.δ h layer hLayer).clock τ tt ρ)
        (rowMom D P.L x E ρ)‖ ≤ Bx x E := by
    intro E x tt htt τ hτ
    calc _ ≤ ∏ ρ, ((2 * rowBoundH hM9 B RD hG layer hLayer P Bh W ρ) *
            decayWt D (30 * P.d) ρ (rowMom D P.L x E ρ)) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun ρ _ =>
            hrowdec ρ _ (rowBx_closure hM9 B RD hG layer hLayer W P.L P.γ P.δ h hqq ρ
              (rows_clock_mem_cube hM9 B RD hG layer hLayer W
                (step3W_ok hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.δ h tt htt τ hτ ρ)) _)
      _ = Bx x E := Finset.prod_mul_distrib
  have hcontI : ∀ E : Fin 4 → Mom P.d, ContinuousOn (fun tt => ((coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 R *
      clLocalZeta R) * clockedExprEpsM (D := D) (fun v : ↥U => childLabel hM9 B hG v.1 0)
        (fun v : ↥U => childLabel hM9 B hG v.1 1) (fun v : ↥U => childLabel hM9 B hG v.1 2)
        (assemblyClockedS hM9 B RD hG W P.L P.γ P.δ h layer hLayer)
        (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) hI P.L P.γ (2 * P.δ) P.η (fun (_ : Fin 3 → ℝ) (τ : D.S.TVar → ℝ) => Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, hI⟩, 0⟩) : ℝ) : ℂ) * Complex.I)) tt E) (cubeSet D.qOut) := by
    intro E
    exact continuousOn_const.mul (continuousOn_clockedExprEpsM hbad2' _ _ _ _ _ _ hI P.L P.γ (2 * P.δ) P.η E (fun (_ : Fin 3 → ℝ) (τ : D.S.TVar → ℝ) => Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, hI⟩, 0⟩) : ℝ) : ℂ) * Complex.I))
      (continuous_mlow lam hI) (norm_mlow_le lam hI)
      (fun ρ k => rows_continuousH hB hd hL hlay W ρ k) (cubeSet D.qOut) (fun x => Bx x E)
      (hBxs E) (fun x => hBx0 x E) (hbd E))
  intro E hE
  set b1 : Prop := (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching with hb1
  set b2 : Prop := (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching with hb2
  have hcomp : ContinuousOn (fun tt => ((coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 R *
      clLocalZeta R) * clockedExprEpsM (D := D) (fun v : ↥U => childLabel hM9 B hG v.1 0)
        (fun v : ↥U => childLabel hM9 B hG v.1 1) (fun v : ↥U => childLabel hM9 B hG v.1 2)
        (assemblyClockedS hM9 B RD hG W P.L P.γ P.δ h layer hLayer)
        (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) hI P.L P.γ (2 * P.δ) P.η (fun (_ : Fin 3 → ℝ) (τ : D.S.TVar → ℝ) => Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, hI⟩, 0⟩) : ℝ) : ℂ) * Complex.I))
        (leafT D.qOut b1 b2 tt) E) (cubeSet D.qOut) :=
    (hcontI E).comp (continuous_leafT D.qOut b1 b2).continuousOn (mapsTo_leafT_cubeSet D.qOut b1 b2)
  refine hcomp.congr fun tt _ => ?_
  have hl0 := leafT_zero D.qOut b1 b2 tt
  have hl1 := leafT_one D.qOut b1 b2 tt
  have hl2 := leafT_two D.qOut b1 b2 tt
  have hcongr := clRecenteredLocalKernelModC_congr RD hG R P.L P.γ P.δ h layer hLayer wBar lam
    (tt 0) (tt 1) (tt 2) (leafT D.qOut b1 b2 tt 1) (leafT D.qOut b1 b2 tt 2)
    (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
    (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)
    (by by_cases h : b1
        · exact Or.inl h
        · exact Or.inr (by rw [hl1]; simp [h]))
    (by by_cases h : b2
        · exact Or.inl h
        · exact Or.inr (by rw [hl2]; simp [h]))
  refine hcongr.trans ?_
  have hk := kernelMod_eq_clockedExprEpsM hM9 B RD hG W (fun _ => rfl) hbad2' (L := P.L) hL0.ne' P.γ P.δ P.η lam
    h layer hLayer rfl (step3W_ok hM9 B RD hG layer hLayer badKind qOut centre wBar) (leafT D.qOut b1 b2 tt)
    (by by_cases h : b1
        · right; rw [hl1]; simp only [h, ite_true]
          rcases hq1 with h' | h'
          · exact absurd h' h
          · exact h'
        · left; exact not_not.1 h)
    (by by_cases h : b2
        · right; rw [hl2]; simp only [h, ite_true]
          rcases hq2 with h' | h'
          · exact absurd h' h
          · exact h'
        · left; exact not_not.1 h)
    E (fun c => (hE.1 c).1) hE.2.1
  rw [hl0] at hk
  exact hk.trans (by ring)

end WaveTurbulence.VineEstS5C.Cont
