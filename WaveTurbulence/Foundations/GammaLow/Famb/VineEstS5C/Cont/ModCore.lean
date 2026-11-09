/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.ModKernel
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.ModCore
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Step3AtH
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Cont.ModKernel
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.ModCore` (sha256 84e2e7f02f7d2623…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

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
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.Cont
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.Cont
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3
  WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory Filter Topology
open scoped ENNReal

section Expr
variable {d : ℕ}

end Expr

section Ident
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **The modulated kernel as `coupling^{n₁} ζ · clockedExprEpsM`** at points of the `sumint` output set. -/
theorem kernelMod_eq_clockedExprEpsMΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (γ δ η lam : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer)
    (hq : W.q = assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hok : ConstraintsOKΓ hM9 B W) (tt : Fin 3 → ℝ)
    (hp : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      tt 1 ≤ assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩))
    (hn : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      tt 2 ≤ assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩)) (E : Fin 4 → Mom d)
    (hE : ∀ c, ∃ nv : Fin d → ℤ, E c = W.wBar + latticePoint L nv) (hgap : E 0 - E 1 = E 3 - E 2) :
    clRecenteredLocalKernelModC RD hG R L γ δ F layer hLayer W.wBar lam (tt 0) (tt 1) (tt 2)
        (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3) =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        clockedExprEpsM (fun v : ↥U => childLabelΓ hM9 B hG v.1 0) (fun v : ↥U => childLabelΓ hM9 B hG v.1 1)
          (fun v : ↥U => childLabelΓ hM9 B hG v.1 2) (assemblyClockedSΓ hM9 B RD hG W L γ δ F layer hLayer)
          (assemblyCoreFirstSignΓ hM9 B) (assemblyCoreSignΓ hM9 B) (assemblyShape_I_posΓ hM9 B) L γ (2 * δ) η
          (fun (tt : Fin 3 → ℝ) (τ : (sourceSumintDatumΓ hM9 B hG W).S.TVar → ℝ) =>
            Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩) : ℝ) : ℂ) * Complex.I)) tt E := by
  obtain ⟨β, hβ, rfl⟩ := outSet_exists_beta hL (G.sign a.toNode) W.wBar E hE hgap
  have h0 := vineChainMod_eq_sumintForm'Γ hM9 B RD hG W hpar hbad hL γ δ η F layer hLayer hq hok W.wBar lam β hβ tt hp hn
  have e0 : ∀ j : Fin 4, sumintBoundary (G.sign a.toNode)
      (sumintBoundary (G.sign a.toNode) (fun j => W.wBar + latticePoint L (β j))) j =
      W.wBar + latticePoint L (β j) := fun j => by rw [sumintBoundary_invol]
  rw [e0 0, e0 1, e0 2, e0 3, h0]
  unfold clockedExprEpsM
  congr 1
  refine tsum_congr fun x => ?_
  rw [clRegionalEpsilon_eq_epsOfΓ hM9 B hG W hL W.wBar β hβ x]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  beta_reduce
  congr 1
  exact (clockedIntegrand_assemblyΓ hM9 B RD hG W L γ δ F layer hLayer _ _ γ (2 * δ) η x _ tt τ).symm

end Ident

/-- **V5-CONT core.**  Continuity of the recentered local kernel in `(t₀,t₁,t₂)` on the closed cube, for each output
momentum of the output set.  Hypotheses are those of `step3AtLeafH` that concern the rows (gates, eligibility) and the
two leaf-child time conditions; the bad clause, the order bound and the engine bound are not needed. -/
theorem clRecenteredMod_continuousOnΓ {P : WTParams} (lam : ℝ)
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
    (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
    {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {n : ℕ} (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
    (qOut : Fin 3 → ℕ) (centre : Fin 4 → Mom P.d) (wBar : Mom P.d)
    (badKind : Fin (assemblyShapeΓ hM9 B).I → Fin 4) (hbad2 : ∀ i, badKind i ≠ 2)
    (hel : ∀ v, CoupleEligibleΓ hM9 B RD hG (step3WΓ hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.δ
          h layer hLayer (P.N (p + 1) ^ 4) p v ∧
        TreeEligibleΓ hM9 B RD hG (step3WΓ hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.δ
          h layer hLayer (P.N (p + 1) ^ 4) p v)
    (hq1 : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      (qOut 1 : ℝ) ≤ assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩))
    (hq2 : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      (qOut 2 : ℝ) ≤ assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩)) :
    ∀ E ∈ outSet (step3DΓ hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.η,
      ContinuousOn (fun tt : Fin 3 → ℝ => clRecenteredLocalKernelModC (rowSel := VineEst.RowSel.plain) RD hG R P.L P.γ P.δ h layer hLayer wBar lam
          (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
          (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3))
        (cubeSet (step3DΓ hM9 B RD hG layer hLayer badKind qOut centre wBar).qOut) := by
  classical
  have hL0 : 0 < P.L := by linarith
  set W := step3WΓ hM9 B RD hG layer hLayer badKind qOut centre wBar with hW
  set D := sourceSumintDatumΓ hM9 B hG W with hD
  have hI := assemblyShape_I_posΓ hM9 B
  have hbad2' : ∀ i, D.badKind i ≠ 2 := fun i => hbad2 i
  have hqq : ∀ v, (rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 ≤
      (rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1 := fun v => (hel v).2.1
  have hres : ∀ ρ, XNormRestr (6 * P.η ^ 6) (30 * P.d) (rowOrder D ρ)
      (rowBxΓ hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ) Set.univ
      ((assemblyClockedSΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ) <
      ENNReal.ofReal (2 * rowBoundHΓ hM9 B RD hG layer hLayer P Bh W ρ) := by
    intro ρ
    rcases ρ with v | v
    · have h1 := coupleRow_leaf_leΓ W hgate hinc hd hη6 hη2 hC hδ.le hL hw hp hB hlay v (hel v).1
      have hx : 0 < rowBoundHΓ hM9 B RD hG layer hLayer P Bh W (Sum.inl v) :=
        mul_pos (rowB_pos hC hδ hL0 _ _) (rowCostH_posΓ hBpos hlay W _)
      refine h1.trans_lt ?_
      change ENNReal.ofReal (rowBoundHΓ hM9 B RD hG layer hLayer P Bh W (Sum.inl v)) < _
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    · have h1 := treeRow_leaf_leΓ W hgate hinc hd hη6 hη2 hC hδ.le hL hw hp hB hlay v (hel v).2
      have hx : 0 < rowBoundHΓ hM9 B RD hG layer hLayer P Bh W (Sum.inr v) :=
        mul_pos (rowB_pos hC hδ hL0 _ _) (rowCostH_posΓ hBpos hlay W _)
      refine h1.trans_lt ?_
      change ENNReal.ofReal (rowBoundHΓ hM9 B RD hG layer hLayer P Bh W (Sum.inr v)) < _
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hrb : ∀ ρ, 0 < rowBoundHΓ hM9 B RD hG layer hLayer P Bh W ρ := by
    intro ρ; rcases ρ with v | v <;> exact mul_pos (rowB_pos hC hδ hL0 _ _) (rowCostH_posΓ hBpos hlay W _)
  have hrowdec : ∀ ρ (c : Fin 2 → ℝ), c ∈ closure (interior (rowBxΓ hM9 B RD hG layer hLayer W P.L P.γ P.δ
      h ρ)) → ∀ k, ‖(assemblyClockedSΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ c k‖ ≤
      (2 * rowBoundHΓ hM9 B RD hG layer hLayer P Bh W ρ) * decayWt D (30 * P.d) ρ k := by
    intro ρ c hc k
    have h := norm_le_decay_of_XNormRestr (θ := 6 * P.η ^ 6) (by positivity) (30 * P.d) (Eng.rowOrder D ρ) _ _
      (2 * rowBoundHΓ hM9 B RD hG layer hLayer P Bh W ρ) (hres ρ) c hc k
      (rows_continuousHΓ hB hd hL hlay W ρ k)
    rcases ρ with v | v
    · exact h
    · simpa [decayWt, Eng.rowOrder] using h
  set Bx : (D.S.VIdx → (Fin P.d → ℤ)) → (Fin 4 → Mom P.d) → ℝ := fun x E =>
    (∏ ρ, 2 * rowBoundHΓ hM9 B RD hG layer hLayer P Bh W ρ) * ∏ ρ, decayWt D (30 * P.d) ρ (rowMom D P.L x E ρ)
    with hBx
  have hBxs : ∀ E, Summable fun x => Bx x E := fun E =>
    (summable_decayWt D hL0 (by omega : P.d + 1 ≤ 30 * P.d) E).mul_left _
  have hBx0 : ∀ x E, 0 ≤ Bx x E := fun x E =>
    mul_nonneg (Finset.prod_nonneg fun ρ _ => by have := hrb ρ; linarith)
      (Finset.prod_nonneg fun ρ _ => decayWt_nonneg D _ ρ _)
  have hbd : ∀ E x, ∀ tt ∈ cubeSet D.qOut, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2),
      ∏ ρ, ‖(assemblyClockedSΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ
        ((assemblyClockedSΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer).clock τ tt ρ)
        (rowMom D P.L x E ρ)‖ ≤ Bx x E := by
    intro E x tt htt τ hτ
    calc _ ≤ ∏ ρ, ((2 * rowBoundHΓ hM9 B RD hG layer hLayer P Bh W ρ) *
            decayWt D (30 * P.d) ρ (rowMom D P.L x E ρ)) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun ρ _ =>
            hrowdec ρ _ (rowBx_closureΓ hM9 B RD hG layer hLayer W P.L P.γ P.δ h hqq ρ
              (rows_clock_mem_cubeΓ hM9 B RD hG layer hLayer W
                (step3W_okΓ hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.δ h tt htt τ hτ ρ)) _)
      _ = Bx x E := Finset.prod_mul_distrib
  have hcontI : ∀ E : Fin 4 → Mom P.d, ContinuousOn (fun tt => ((coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 R *
      clLocalZeta R) * clockedExprEpsM (D := D) (fun v : ↥U => childLabelΓ hM9 B hG v.1 0)
        (fun v : ↥U => childLabelΓ hM9 B hG v.1 1) (fun v : ↥U => childLabelΓ hM9 B hG v.1 2)
        (assemblyClockedSΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer)
        (assemblyCoreFirstSignΓ hM9 B) (assemblyCoreSignΓ hM9 B) hI P.L P.γ (2 * P.δ) P.η (fun (_ : Fin 3 → ℝ) (τ : D.S.TVar → ℝ) => Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, hI⟩, 0⟩) : ℝ) : ℂ) * Complex.I)) tt E) (cubeSet D.qOut) := by
    intro E
    exact continuousOn_const.mul (continuousOn_clockedExprEpsM hbad2' _ _ _ _ _ _ hI P.L P.γ (2 * P.δ) P.η E (fun (_ : Fin 3 → ℝ) (τ : D.S.TVar → ℝ) => Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, hI⟩, 0⟩) : ℝ) : ℂ) * Complex.I))
      (continuous_mlow lam hI) (norm_mlow_le lam hI)
      (fun ρ k => rows_continuousHΓ hB hd hL hlay W ρ k) (cubeSet D.qOut) (fun x => Bx x E)
      (hBxs E) (fun x => hBx0 x E) (hbd E))
  intro E hE
  set b1 : Prop := (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching with hb1
  set b2 : Prop := (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching with hb2
  have hcomp : ContinuousOn (fun tt => ((coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 R *
      clLocalZeta R) * clockedExprEpsM (D := D) (fun v : ↥U => childLabelΓ hM9 B hG v.1 0)
        (fun v : ↥U => childLabelΓ hM9 B hG v.1 1) (fun v : ↥U => childLabelΓ hM9 B hG v.1 2)
        (assemblyClockedSΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer)
        (assemblyCoreFirstSignΓ hM9 B) (assemblyCoreSignΓ hM9 B) hI P.L P.γ (2 * P.δ) P.η (fun (_ : Fin 3 → ℝ) (τ : D.S.TVar → ℝ) => Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, hI⟩, 0⟩) : ℝ) : ℂ) * Complex.I))
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
  have hk := kernelMod_eq_clockedExprEpsMΓ hM9 B RD hG W (fun _ => rfl) hbad2' (L := P.L) hL0.ne' P.γ P.δ P.η lam
    h layer hLayer rfl (step3W_okΓ hM9 B RD hG layer hLayer badKind qOut centre wBar) (leafT D.qOut b1 b2 tt)
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

end WaveTurbulence.GammaLow.Famb.VineEstS5C.Cont
