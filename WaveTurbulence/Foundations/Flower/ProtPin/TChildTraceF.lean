/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildTrace
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildFix

/-! # D3 PROT-PIN (P7): the root-trace bound with the multi-layer coherent gate

`TcTraceUF θ Ct`: `TcTraceU` with the prefix fact `TcFC P` (FILT-COH at a constant `≤ C₁`) and the SIGNED ambient
`TcCplAmbS` of the traced couple. `TcTraceOnF θ Ct C`: its restriction to the traced couples with `C Q LGc j p`.
`tc_traceUF_of_cases`: from the three cases. Proved here: `tcT1M` (from `tc_trace_t1_move`) and `tcT1F`
(`tc_trace_t1_fix` from `tc_t1_fix`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- `TcTraceOn` with `TcFC` and the signed ambient. -/
def TcTraceOnF (θ Ct : ℝ) (Cnd : RegCpl → (LGc : LayeredGarden 2) → Fin 2 → ℕ → Prop) : Prop :=
  ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) (_hFC : TcFC P)
    (_hC11 : 1 ≤ P.C₁) (_hθc : PieceLoss P θ 0)
    {p : ℕ} (_hp : p < P.D) {nr : ℕ} (_hn : nr ≤ P.N (p + 1) ^ 4) (Q : RegCpl) (LGc : LayeredGarden 2)
    (_hwf : Q.wf = true) (_hsz : Q.size = 2 * nr) (_hdec : Q.Decodes LGc.garden) (_hle : ∀ a, LGc.layer a ≤ p)
    (_hamb : TcCplAmbS p Q LGc) (j : Fin 2) (_hj : layerAt LGc (j, []) = p)
    (_hjb : ([] : TTree.Path) ∈ (LGc.garden.tree j).branching) (_hC : Cnd Q LGc j p) {s : ℝ} (_hps : (p : ℝ) < s)
    (_hsp : s < p + 1)
    (Hc : LeafProfiles 2 P.d) (Bc : (Fin 2 × TTree.Path) → NNReal) (_hHc : LeafwiseControlled LGc Hc Bc)
    (S : Finset (GNode LGc.garden.tree)) (ω : GNode LGc.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LGc.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LGc.garden.tree)) (M : GBranch LGc.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LGc.garden.tree)) (Mu : GBranch LGc.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (k : Mom P.d),
    rn θ (win p) (fun y => kernelProt P.L P.γ P.δ LGc Hc
        (gateM S ω F M Fu Mu) (fun b => if b.1.1 = j then s else y 0) 0 (trFix j s) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (Ct * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 *
        (P.C₁ ^ 3 * rb P (nr - 1) (LGc.incoherency Q.links)) * leafSizeProduct LGc Bc * starCost S cω))) *
          tcWt P.L k

/-- **The root-trace bound with the multi-layer coherent gate.** -/
def TcTraceUF (θ Ct : ℝ) : Prop := TcTraceOnF θ Ct (fun _ _ _ _ => True)

theorem tcTraceOnF_mono {θ Ct Ct' : ℝ} {Cnd : RegCpl → (LGc : LayeredGarden 2) → Fin 2 → ℕ → Prop}
    (hle : Ct ≤ Ct') (h : TcTraceOnF θ Ct Cnd) : TcTraceOnF θ Ct' Cnd := by
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle' hamb j hj hjb hC s hps hsp Hc Bc hHc S ω
    cω hpres F M hM Fu Mu hMu k
  refine (h K hFC hC11 hθc hp hn Q LGc hwf hsz hdec hle' hamb j hj hjb hC hps hsp Hc Bc hHc S ω cω hpres F M hM Fu Mu
    hMu k).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle ?_)) le_rfl)
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have := rb_nonneg hC1 K.hδ hL0 (nr - 1) (LGc.incoherency Q.links)
  have := starCost_nonneg' S cω
  have : 0 ≤ leafSizeProduct LGc Bc := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  positivity

/-- `C₁² ≤ C₁³` in the root-trace bound. -/
theorem tc_rhs_C3 {P : WTParams} {r l cs : ℝ} (hC11 : 1 ≤ P.C₁) (hL0 : 0 ≤ P.L) (hr : 0 ≤ r)
    (hl : 0 ≤ l) (hcs : 0 ≤ cs) :
    P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 2 * r) * l * cs) ≤
      P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * r) * l * cs) := by
  have h23 : P.C₁ ^ 2 ≤ P.C₁ ^ 3 := pow_le_pow_right₀ hC11 (by norm_num)
  have hc2 : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 := sq_nonneg _
  gcongr

theorem tc_ofReal_mono_Ct (Ct : ℝ) {X Y : ℝ} (hX : 0 ≤ X) (h : X ≤ Y) :
    ENNReal.ofReal (Ct * X) ≤ ENNReal.ofReal (Ct * Y) := by
  rcases le_or_gt 0 Ct with hC | hC
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h hC)
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hC.le hX)]
    exact zero_le

/-- A case proved without the extra prefix facts. -/
theorem tcTraceOnF_of {θ Ct : ℝ} {Cnd : RegCpl → (LGc : LayeredGarden 2) → Fin 2 → ℕ → Prop}
    (h : TcTraceOn θ Ct Cnd) : TcTraceOnF θ Ct Cnd := by
  intro P C₁a C₂a C₁b C₂b K _ hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle hamb j hj hjb hC s hps hsp Hc Bc hHc S ω
    cω hpres F M hM Fu Mu hMu k
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hr := rb_nonneg (by linarith) K.hδ hL0 (nr - 1) (LGc.incoherency Q.links)
  have hl : 0 ≤ leafSizeProduct LGc Bc := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hcs := starCost_nonneg' S cω
  have hX : 0 ≤ P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 2 * rb P (nr - 1) (LGc.incoherency Q.links)) *
      leafSizeProduct LGc Bc * starCost S cω) := by
    have : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 := sq_nonneg _
    have : 0 ≤ P.C₁ := by linarith
    positivity
  exact (h K hθc hp hn Q LGc hwf hsz hdec hle hamb.amb j hj hjb hC hps hsp Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu
    k).trans (mul_le_mul' (tc_ofReal_mono_Ct Ct hX (tc_rhs_C3 hC11 hL0 hr hl hcs)) le_rfl)

/-- **`TcTraceUF` from its three cases.** -/
theorem tc_traceUF_of_cases {θ Ct : ℝ} (h1 : TcTraceOnF θ Ct tcT1M) (h2 : TcTraceOnF θ Ct tcT1F)
    (h3 : TcTraceOnF θ Ct tcT2) : TcTraceUF θ Ct := by
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle hamb j hj hjb _ s hps hsp Hc Bc hHc S ω
    cω hpres F M hM Fu Mu hMu k
  cases Q with
  | triv =>
    exfalso
    have ht := tree_of_decodes hdec j
    split_ifs at ht <;> rw [ht] at hjb <;> simp [RegCpl.trees, TTree.branching] at hjb
  | type1 c Q₁ Q₂ Q₃ =>
    have hpl : layerAt LGc (t1sw j, []) ≤ p := by
      have hm : ([] : TTree.Path) ∈ (LGc.garden.tree (t1sw j)).nodes := TTree.nil_mem_nodes _
      rw [layerAt_node LGc (⟨(t1sw j, []), hm⟩ : GNode LGc.garden.tree)]
      exact hle _
    rcases hpl.lt_or_eq with hlt | heq
    · exact h2 K hFC hC11 hθc hp hn _ LGc hwf hsz hdec hle hamb j hj hjb ⟨⟨c, Q₁, Q₂, Q₃, rfl⟩, hlt⟩ hps hsp Hc Bc
        hHc S ω cω hpres F M hM Fu Mu hMu k
    · exact h1 K hFC hC11 hθc hp hn _ LGc hwf hsz hdec hle hamb j hj hjb ⟨⟨c, Q₁, Q₂, Q₃, rfl⟩, heq⟩ hps hsp Hc Bc
        hHc S ω cω hpres F M hM Fu Mu hMu k
  | type2 Xp Xm Qlp =>
    exact h3 K hFC hC11 hθc hp hn _ LGc hwf hsz hdec hle hamb j hj hjb ⟨Xp, Xm, Qlp, rfl⟩ hps hsp Hc Bc hHc
      S ω cω hpres F M hM Fu Mu hMu k

/-- **The root trace of a type-1 side couple with the partner root below `p`.** -/
theorem tc_trace_t1_fix {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) : ∃ Ct : ℝ, 0 ≤ Ct ∧ TcTraceOnF θ Ct tcT1F := by
  obtain ⟨C, hC, hfix⟩ := tc_t1_fix hθ0 hθ1
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle hamb j hj hjb hCnd s hps hsp Hc Bc hHc S
    ω cω hpres F M hM Fu Mu hMu k
  obtain ⟨⟨c, Q₁, Q₂, Q₃, rfl⟩, hpart⟩ := hCnd
  obtain ⟨LG₁, LG₂, LG₃, h, hlA, hlB, hlC⟩ := T1Data.exists_of_decodes LGc c Q₁ Q₂ Q₃ hdec hwf
  refine (hfix K hFC hθc hp hn h hlA hlB hlC hwf hsz hle hamb j hj hpart hps hsp Hc Bc hHc S ω cω hpres
    F M hM Fu Mu hMu k).trans ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC.ne]
  exact mul_le_mul' (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (tc_rhs_C3 hC11 (by linarith [K.hL])
    (rb_nonneg (by linarith) K.hδ (by linarith [K.hL]) (nr - 1) (LGc.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links))
    (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg' S cω)))) le_rfl

/-- The two proved cases of `TcTraceUF`, with one constant. -/
theorem tc_trace_t1F {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ TcTraceOnF θ Ct tcT1M ∧ TcTraceOnF θ Ct tcT1F := by
  obtain ⟨C₁, hC₁, hM⟩ := tc_trace_t1_move hθ0 hθ1
  obtain ⟨C₂, hC₂, hF⟩ := tc_trace_t1_fix hθ0 hθ1
  exact ⟨max C₁ C₂, le_max_of_le_left hC₁, tcTraceOnF_mono (le_max_left _ _) (tcTraceOnF_of hM),
    tcTraceOnF_mono (le_max_right _ _) hF⟩

end WaveTurbulence.Flower.ProtPin
