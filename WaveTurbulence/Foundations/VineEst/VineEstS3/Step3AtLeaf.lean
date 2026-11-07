/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Data
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Kernel
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3At
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LeafChild
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockedCont
public import WaveTurbulence.Foundations.VineEst.VineEstS3.PointwiseDecay
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LeafTrace
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LeafWire

/-! # Step 3 at a fixed parameter `P`: the engine bound for the vine-chain kernel with `ε`

`step3At` (TARGET vineest Step 3, L1826-L1870, before the constant bookkeeping): at parameters `P` for which the
`sumint` statement (with the `ε`-mixture, DEGEN-VINE), the 30d Prop 6.1 gate and B2.2 hold, the recentered kernel of a
vine chain, seen as a function of the output times and of the boundary vector in the `sumint` convention, obeys

`‖K̃^U‖_{𝔛^{2η⁸,0,0}} ≤ (δ/2L^{d-γ})^{n₁} (cc_η+1) 3^{|U|} K₀ Σ ∏ L^{wE g} ∏ (Cfs · 2 B_ρ)`,

with `B_ρ = rowB P n_ρ g_ρ`, `n_ρ` the half order and `g_ρ` the incoherency index of the regular object of row `ρ`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine WaveTurbulence.LGSpine
  VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory
open scoped ENNReal

/-- **TARGET vineest Step 3, engine form, leaf lower children allowed.** -/
theorem step3AtLeaf {A : ℝ} {P : WTParams} (hdb : SumintMixDoubledAt A P) (hA : 6561 ≤ A)
    (hgate : CoherentGateAt P) (hinc : IncoherentGateAt P)
    (hd : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) :
    ∀ {p : ℕ}, p < P.D → ∀ {Rin : ℕ → Mom P.d → ℝ},
      (∀ r ≤ p, InputRemainder P (Rin r) r) →
      ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
        {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
        (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer), (∀ x, layer x ≤ p) →
      ∀ (qOut : Fin 3 → ℕ) (centre : Fin 4 → Mom P.d) (wBar : Mom P.d)
        (badKind : Fin (assemblyShape hM9 B).I → Fin 4), (∀ c, qOut c ≤ p) → (∀ i, badKind i = 0 ∨ badKind i = 3) →
      BadClause (step3D hM9 B RD hG layer hLayer badKind qOut centre wBar) →
      (∀ v, CoupleEligible hM9 B RD hG (step3W hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.δ
          (inputsF P Rin) layer hLayer (P.N (p + 1) ^ 4) p v ∧
        TreeEligible hM9 B RD hG (step3W hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.δ
          (inputsF P Rin) layer hLayer (P.N (p + 1) ^ 4) p v) →
      clLocalOrder1 R ≤ P.N 1 ^ 4 →
      (qOut 1 : ℝ) ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩) →
      (qOut 2 : ℝ) ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩) →
      XNorm00Restr (2 * P.η ^ 8) (outBox (step3D hM9 B RD hG layer hLayer badKind qOut centre wBar))
        (outSet (step3D hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.η)
        (fun tt E => clRecenteredLocalKernel (rowSel := VineEst.RowSel.plain) RD hG R P.L P.γ P.δ (inputsF P Rin) layer hLayer wBar
          (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
          (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
        Regref.traceConst (r := 3) (2 * P.η ^ 8) chiUnit ^ 2 *
          step3Bound P (CfsOf P.d P.η) hM9 B RD hG layer hLayer badKind qOut centre wBar := by
  classical
  have hL0 : 0 < P.L := by linarith
  have hη1 : P.η ≤ 1 := by linarith
  intro p hp Rin hR w G U a b R n hM9 B RD hG layer hLayer hlay qOut centre wBar badKind hqOut hbk hbad hel hM hq1 hq2
  set W := step3W hM9 B RD hG layer hLayer badKind qOut centre wBar with hW
  set D := sourceSumintDatum hM9 B hG W with hD
  have hI := assemblyShape_I_pos hM9 B
  have hno : ∀ i, D.badKind i ≠ 1 := fun i => by
    show badKind i ≠ 1
    rcases hbk i with h | h <;> rw [h] <;> decide
  have hbad2 : ∀ i, D.badKind i ≠ 2 := fun i => by
    show badKind i ≠ 2
    rcases hbk i with h | h <;> rw [h] <;> decide
  have hq : ∀ v, W.q v + 1 ≤ P.D := fun v =>
    Nat.succ_le_of_lt (lt_of_le_of_lt (hlay _) hp)
  have hqo : ∀ c, W.qOut c + 1 ≤ P.D := fun c => Nat.succ_le_of_lt (lt_of_le_of_lt (hqOut c) hp)
  have hAdm := admissible_source hM9 B hG W (L := P.L) (γ := P.γ) (η := P.η) hA hq hqo hbad
  have hMD : D.S.M ≤ P.N 1 ^ 4 := by
    rw [show D.S.M = clLocalOrder1 R from assemblyShape_M hM9 B]; exact hM
  have hqq : ∀ v, (rowQ hM9 B RD hG W P.L P.γ P.δ (inputsF P Rin) layer hLayer (Sum.inr v)).2 ≤
      (rowQ hM9 B RD hG W P.L P.γ P.δ (inputsF P Rin) layer hLayer (Sum.inr v)).1 := fun v => (hel v).2.1
  have hres : ∀ ρ, XNormRestr (6 * P.η ^ 6) (30 * P.d) (rowOrder D ρ)
      (rowBx hM9 B RD hG layer hLayer W P.L P.γ P.δ (inputsF P Rin) ρ) Set.univ
      ((assemblyClockedS hM9 B RD hG W P.L P.γ P.δ (inputsF P Rin) layer hLayer).W ρ) <
      ENNReal.ofReal (2 * rowBound hM9 B RD hG layer hLayer P W ρ) := by
    intro ρ
    rcases ρ with v | v
    · have h1 := coupleRow_le W hgate hinc hd hη6 hη2 hC hδ.le hL hw hp hR hlay v (hel v).1
      have hx : 0 < rowBound hM9 B RD hG layer hLayer P W (Sum.inl v) := rowB_pos hC hδ hL0 _ _
      refine h1.trans_lt ?_
      change ENNReal.ofReal (rowBound hM9 B RD hG layer hLayer P W (Sum.inl v)) < _
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    · have h1 := treeRow_le W hgate hinc hd hη6 hη2 hC hδ.le hL hw hp hR hlay v (hel v).2
      have hx : 0 < rowBound hM9 B RD hG layer hLayer P W (Sum.inr v) := rowB_pos hC hδ hL0 _ _
      refine h1.trans_lt ?_
      change ENNReal.ofReal (rowBound hM9 B RD hG layer hLayer P W (Sum.inr v)) < _
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hcl := clockedBoundEps_cfs hdb hL0 hη0 hη1 (by linarith) hδ hd hI (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B)
    (fun v : ↥U => childLabel hM9 B hG v.1 0) (fun v : ↥U => childLabel hM9 B hG v.1 1)
    (fun v : ↥U => childLabel hM9 B hG v.1 2) hno hbad2 hAdm hMD
    (assemblyClockedS hM9 B RD hG W P.L P.γ P.δ (inputsF P Rin) layer hLayer)
    (rowBx hM9 B RD hG layer hLayer W P.L P.γ P.δ (inputsF P Rin))
    (rowQx hM9 B RD hG layer hLayer W P.L P.γ P.δ (inputsF P Rin))
    (fun ρ => ENNReal.ofReal (2 * rowBound hM9 B RD hG layer hLayer P W ρ))
    (rowBx_subset_cell hM9 B RD hG layer hLayer W P.L P.γ P.δ (inputsF P Rin))
    (rowBx_closure hM9 B RD hG layer hLayer W P.L P.γ P.δ (inputsF P Rin) hqq)
    (fun ρ k => rows_continuous hM9 B RD hG layer hLayer hd hL hR hlay W ρ k) hres
    (fun _ => ENNReal.ofReal_ne_top)
    (fun tt htt τ hτ ρ => rows_clock_mem hM9 B RD hG layer hLayer W (step3W_ok hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.δ (inputsF P Rin) tt htt τ hτ ρ)
  have hcpl : 0 < coupling P.d P.L P.γ P.δ := by
    unfold coupling; positivity
  have hnorm : ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R‖ₑ =
      ENNReal.ofReal ((coupling P.d P.L P.γ P.δ) ^ clLocalOrder1 R) := by
    rw [← ofReal_norm_eq_enorm, norm_mul, norm_clLocalZeta, mul_one, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hcpl.le]
  -- continuity of the clocked expression on the closed cube of output times, with a summable majorant
  have hrb : ∀ ρ, 0 < rowBound hM9 B RD hG layer hLayer P W ρ := by
    intro ρ; rcases ρ with v | v <;> exact rowB_pos hC hδ hL0 _ _
  have hrowdec : ∀ ρ (c : Fin 2 → ℝ), c ∈ closure (interior (rowBx hM9 B RD hG layer hLayer W P.L P.γ P.δ
      (inputsF P Rin) ρ)) → ∀ k, ‖(assemblyClockedS hM9 B RD hG W P.L P.γ P.δ (inputsF P Rin) layer hLayer).W ρ c k‖ ≤
      (2 * rowBound hM9 B RD hG layer hLayer P W ρ) * decayWt D (30 * P.d) ρ k := by
    intro ρ c hc k
    have h := norm_le_decay_of_XNormRestr (θ := 6 * P.η ^ 6) (by positivity) (30 * P.d) (Eng.rowOrder D ρ) _ _
      (2 * rowBound hM9 B RD hG layer hLayer P W ρ) (hres ρ) c hc k
      (rows_continuous hM9 B RD hG layer hLayer hd hL hR hlay W ρ k)
    rcases ρ with v | v
    · exact h
    · simpa [decayWt, Eng.rowOrder] using h
  set Bx : (D.S.VIdx → (Fin P.d → ℤ)) → (Fin 4 → Mom P.d) → ℝ := fun x E =>
    (∏ ρ, 2 * rowBound hM9 B RD hG layer hLayer P W ρ) * ∏ ρ, decayWt D (30 * P.d) ρ (rowMom D P.L x E ρ) with hBx
  have hBxs : ∀ E, Summable fun x => Bx x E := fun E =>
    (summable_decayWt D hL0 (by omega : P.d + 1 ≤ 30 * P.d) E).mul_left _
  have hBx0 : ∀ x E, 0 ≤ Bx x E := fun x E =>
    mul_nonneg (Finset.prod_nonneg fun ρ _ => by have := hrb ρ; linarith)
      (Finset.prod_nonneg fun ρ _ => decayWt_nonneg D _ ρ _)
  have hbd : ∀ E x, ∀ tt ∈ cubeSet D.qOut, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2),
      ∏ ρ, ‖(assemblyClockedS hM9 B RD hG W P.L P.γ P.δ (inputsF P Rin) layer hLayer).W ρ
        ((assemblyClockedS hM9 B RD hG W P.L P.γ P.δ (inputsF P Rin) layer hLayer).clock τ tt ρ)
        (rowMom D P.L x E ρ)‖ ≤ Bx x E := by
    intro E x tt htt τ hτ
    calc _ ≤ ∏ ρ, ((2 * rowBound hM9 B RD hG layer hLayer P W ρ) * decayWt D (30 * P.d) ρ (rowMom D P.L x E ρ)) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun ρ _ =>
            hrowdec ρ _ (rowBx_closure hM9 B RD hG layer hLayer W P.L P.γ P.δ (inputsF P Rin) hqq ρ
              (rows_clock_mem_cube hM9 B RD hG layer hLayer W (step3W_ok hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.δ (inputsF P Rin) tt htt τ hτ ρ)) _)
      _ = Bx x E := Finset.prod_mul_distrib
  have hcontI : ∀ E : Fin 4 → Mom P.d, ContinuousOn (fun tt => ((coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 R *
      clLocalZeta R) * clockedExprEps (D := D) (fun v : ↥U => childLabel hM9 B hG v.1 0)
        (fun v : ↥U => childLabel hM9 B hG v.1 1) (fun v : ↥U => childLabel hM9 B hG v.1 2)
        (assemblyClockedS hM9 B RD hG W P.L P.γ P.δ (inputsF P Rin) layer hLayer)
        (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) hI P.L P.γ (2 * P.δ) P.η tt E) (cubeSet D.qOut) := by
    intro E
    exact continuousOn_const.mul (continuousOn_clockedExprEps hbad2 _ _ _ _ _ _ hI P.L P.γ (2 * P.δ) P.η E
      (fun ρ k => rows_continuous hM9 B RD hG layer hLayer hd hL hR hlay W ρ k) (cubeSet D.qOut) (fun x => Bx x E)
      (hBxs E) (fun x => hBx0 x E) (hbd E))
  classical
  have hker := XNorm00Restr_leaf (θ := 2 * P.η ^ 8) (by positivity) D (outSet D P.L P.γ P.η)
    (fun tt E => ((coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R) *
      clockedExprEps (D := D) (fun v : ↥U => childLabel hM9 B hG v.1 0) (fun v : ↥U => childLabel hM9 B hG v.1 1)
        (fun v : ↥U => childLabel hM9 B hG v.1 2) (assemblyClockedS hM9 B RD hG W P.L P.γ P.δ (inputsF P Rin) layer hLayer)
        (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) hI P.L P.γ (2 * P.δ) P.η tt E)
    (fun tt E => clRecenteredLocalKernel RD hG R P.L P.γ P.δ (inputsF P Rin) layer hLayer wBar
          (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
          (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3))
    ((b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching)
    ((b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching)
    (fun E _ => hcontI E) (fun tt htt E hE => by
      set b1 : Prop := (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching with hb1
      set b2 : Prop := (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching with hb2
      have hl0 := leafT_zero D.qOut b1 b2 tt
      have hl1 := leafT_one D.qOut b1 b2 tt
      have hl2 := leafT_two D.qOut b1 b2 tt
      have hcongr := clRecenteredLocalKernel_congr RD hG R P.L P.γ P.δ (inputsF P Rin) layer hLayer wBar
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
      have hk := kernel_eq_clockedExprEps' hM9 B RD hG W (fun _ => rfl) hbad2 (L := P.L) hL0.ne' P.γ P.δ P.η
        (inputsF P Rin) layer hLayer rfl (step3W_ok hM9 B RD hG layer hLayer badKind qOut centre wBar) (leafT D.qOut b1 b2 tt)
        (by by_cases h : b1
            · right; rw [hl1]; simp only [h, if_true]; exact hq1
            · left; exact not_not.1 h)
        (by by_cases h : b2
            · right; rw [hl2]; simp only [h, if_true]; exact hq2
            · left; exact not_not.1 h)
        E (fun c => (hE.1 c).1) hE.2.1
      rw [hl0] at hk
      exact hk.trans (by ring))
  refine hker.trans (mul_le_mul' le_rfl ((XNorm00Restr_const_mul_le _ _ _ _ _).trans ?_))
  rw [hnorm]
  exact mul_le_mul_right hcl _

end WaveTurbulence.VineEstS3
