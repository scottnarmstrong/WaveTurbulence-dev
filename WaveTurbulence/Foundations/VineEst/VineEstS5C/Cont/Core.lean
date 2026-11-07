/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Step3AtH

/-! # V5-CONT, core: continuity of the recentered local kernel in the three exterior clocks

`clRecentered_continuousOn`: at one state `(B, RD, hG, layer)` with the row eligibility of Step 3 (`CoupleEligible`,
`TreeEligible` for every row), for every output momentum `E` of the output set the recentered local kernel
`clRecenteredLocalKernel` (written at the boundary `sumintBoundary (G.sign a) E`) is continuous in `(t₀,t₁,t₂)` on the
closed cube `cubeSet qOut`.  The proof is the continuity half of `step3AtLeafH` (`hcontI` of `Step3AtH`): the kernel is the
clocked expression at the effective clocks `leafT` (a leaf lower child does not see its clock), the clocked expression is
continuous on the cube by dominated convergence over the lattice sum (`continuousOn_clockedExprEps`), the majorant being
the decay of the rows (`hres` from the gates, `rows_continuousH`).  No `BadClause`, no order hypothesis and no smallness of
`C₁` are used.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.Cont
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine
  WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory
open scoped ENNReal

/-- The effective output times `leafT` are continuous in `t` (the case split is on propositions, not on `t`). -/
theorem continuous_leafT (q : Fin 3 → ℕ) (b1 b2 : Prop) [Decidable b1] [Decidable b2] :
    Continuous (leafT q b1 b2) := by
  unfold leafT
  by_cases h1 : b1 <;> by_cases h2 : b2 <;> simp only [h1, h2, ite_true, ite_false] <;> fun_prop

/-- `leafT` maps the cube to itself. -/
theorem mapsTo_leafT_cubeSet (q : Fin 3 → ℕ) (b1 b2 : Prop) [Decidable b1] [Decidable b2] :
    Set.MapsTo (leafT q b1 b2) (cubeSet q) (cubeSet q) := by
  intro t ht i
  unfold leafT
  by_cases h1 : b1 <;> by_cases h2 : b2 <;> simp only [h1, h2, ite_true, ite_false]
  · by_cases hi2 : i = 2
    · subst hi2; simp
    · by_cases hi1 : i = 1
      · subst hi1; simp
      · simpa [Function.update_of_ne hi1, Function.update_of_ne hi2] using ht i
  · by_cases hi2 : i = 1
    · subst hi2; simp
    · simpa [Function.update_of_ne hi2] using ht i
  · by_cases hi2 : i = 2
    · subst hi2; simp
    · simpa [Function.update_of_ne hi2] using ht i
  · exact ht i

/-- **V5-CONT core.**  Continuity of the recentered local kernel in `(t₀,t₁,t₂)` on the closed cube, for each output
momentum of the output set.  Hypotheses are those of `step3AtLeafH` that concern the rows (gates, eligibility) and the
two leaf-child time conditions; the bad clause, the order bound and the engine bound are not needed. -/
theorem clRecentered_continuousOn {P : WTParams}
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
      ContinuousOn (fun tt : Fin 3 → ℝ => clRecenteredLocalKernel RD hG R P.L P.γ P.δ h layer hLayer wBar
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
      ((assemblyClocked hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ) <
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
      h ρ)) → ∀ k, ‖(assemblyClocked hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ c k‖ ≤
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
      ∏ ρ, ‖(assemblyClocked hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ
        ((assemblyClocked hM9 B RD hG W P.L P.γ P.δ h layer hLayer).clock τ tt ρ)
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
      clLocalZeta R) * clockedExprEps (D := D) (fun v : ↥U => childLabel hM9 B hG v.1 0)
        (fun v : ↥U => childLabel hM9 B hG v.1 1) (fun v : ↥U => childLabel hM9 B hG v.1 2)
        (assemblyClocked hM9 B RD hG W P.L P.γ P.δ h layer hLayer)
        (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) hI P.L P.γ (2 * P.δ) P.η tt E) (cubeSet D.qOut) := by
    intro E
    exact continuousOn_const.mul (continuousOn_clockedExprEps hbad2' _ _ _ _ _ _ hI P.L P.γ (2 * P.δ) P.η E
      (fun ρ k => rows_continuousH hB hd hL hlay W ρ k) (cubeSet D.qOut) (fun x => Bx x E)
      (hBxs E) (fun x => hBx0 x E) (hbd E))
  intro E hE
  set b1 : Prop := (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching with hb1
  set b2 : Prop := (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching with hb2
  have hcomp : ContinuousOn (fun tt => ((coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 R *
      clLocalZeta R) * clockedExprEps (D := D) (fun v : ↥U => childLabel hM9 B hG v.1 0)
        (fun v : ↥U => childLabel hM9 B hG v.1 1) (fun v : ↥U => childLabel hM9 B hG v.1 2)
        (assemblyClocked hM9 B RD hG W P.L P.γ P.δ h layer hLayer)
        (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) hI P.L P.γ (2 * P.δ) P.η
        (leafT D.qOut b1 b2 tt) E) (cubeSet D.qOut) :=
    (hcontI E).comp (continuous_leafT D.qOut b1 b2).continuousOn (mapsTo_leafT_cubeSet D.qOut b1 b2)
  refine hcomp.congr fun tt _ => ?_
  have hl0 := leafT_zero D.qOut b1 b2 tt
  have hl1 := leafT_one D.qOut b1 b2 tt
  have hl2 := leafT_two D.qOut b1 b2 tt
  have hcongr := clRecenteredLocalKernel_congr RD hG R P.L P.γ P.δ h layer hLayer wBar
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
  have hk := kernel_eq_clockedExprEps' hM9 B RD hG W (fun _ => rfl) hbad2' (L := P.L) hL0.ne' P.γ P.δ P.η
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
