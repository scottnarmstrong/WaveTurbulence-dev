/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildWrap
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildB

/-! # D3 PROT-PIN (P7): the root-trace bound `TcTraceU` by cases

`TcTraceOn θ Ct C`: `TcTraceU` restricted to the traced couples satisfying `C Q LGc j p`. `tc_traceU_of_cases`:
`TcTraceU` from the three cases of o104 Prop 7.4 that occur — type 1 with the partner root in layer `p` (proved here,
`tc_trace_t1_move`: `tc_t1_move` + `tc_t1_flat`), type 1 with the partner root below `p`, and type 2 (the traced
chain empty, (c±), or not, (a±)). A trivial couple has no branching root. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- `TcTraceU` restricted to the traced couples with `C Q LGc j p`. -/
def TcTraceOn (θ Ct : ℝ) (Cnd : RegCpl → (LGc : LayeredGarden 2) → Fin 2 → ℕ → Prop) : Prop :=
  ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) (_hθc : PieceLoss P θ 0)
    {p : ℕ} (_hp : p < P.D) {nr : ℕ} (_hn : nr ≤ P.N (p + 1) ^ 4) (Q : RegCpl) (LGc : LayeredGarden 2)
    (_hwf : Q.wf = true) (_hsz : Q.size = 2 * nr) (_hdec : Q.Decodes LGc.garden) (_hle : ∀ a, LGc.layer a ≤ p)
    (_hamb : TcCplAmb p Q LGc) (j : Fin 2) (_hj : layerAt LGc (j, []) = p)
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
        (P.C₁ ^ 2 * rb P (nr - 1) (LGc.incoherency Q.links)) * leafSizeProduct LGc Bc * starCost S cω))) *
          tcWt P.L k

/-- Type 1, the partner root in layer `p`. -/
def tcT1M (Q : RegCpl) (LGc : LayeredGarden 2) (j : Fin 2) (p : ℕ) : Prop :=
  (∃ c Q₁ Q₂ Q₃, Q = RegCpl.type1 c Q₁ Q₂ Q₃) ∧ layerAt LGc (t1sw j, []) = p

/-- Type 1, the partner root below `p`. -/
def tcT1F (Q : RegCpl) (LGc : LayeredGarden 2) (j : Fin 2) (p : ℕ) : Prop :=
  (∃ c Q₁ Q₂ Q₃, Q = RegCpl.type1 c Q₁ Q₂ Q₃) ∧ layerAt LGc (t1sw j, []) < p

/-- Type 2. -/
def tcT2 (Q : RegCpl) (_LGc : LayeredGarden 2) (_j : Fin 2) (_p : ℕ) : Prop :=
  ∃ Xp Xm Qlp, Q = RegCpl.type2 Xp Xm Qlp

theorem tcTraceOn_mono {θ Ct Ct' : ℝ} {Cnd : RegCpl → (LGc : LayeredGarden 2) → Fin 2 → ℕ → Prop}
    (hle : Ct ≤ Ct') (h : TcTraceOn θ Ct Cnd) : TcTraceOn θ Ct' Cnd := by
  intro P C₁a C₂a C₁b C₂b K hθc p hp nr hn Q LGc hwf hsz hdec hle' hamb j hj hjb hC s hps hsp Hc Bc hHc S ω cω
    hpres F M hM Fu Mu hMu k
  refine (h K hθc hp hn Q LGc hwf hsz hdec hle' hamb j hj hjb hC hps hsp Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu
    k).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle ?_)) le_rfl)
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have := rb_nonneg hC1 K.hδ hL0 (nr - 1) (LGc.incoherency Q.links)
  have := starCost_nonneg' S cω
  have : 0 ≤ leafSizeProduct LGc Bc := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  positivity

/-- **`TcTraceU` from its three cases.** -/
theorem tc_traceU_of_cases {θ Ct : ℝ} (h1 : TcTraceOn θ Ct tcT1M) (h2 : TcTraceOn θ Ct tcT1F)
    (h3 : TcTraceOn θ Ct tcT2) : TcTraceU θ Ct := by
  intro P C₁a C₂a C₁b C₂b K hθc p hp nr hn Q LGc hwf hsz hdec hle hamb j hj hjb s hps hsp Hc Bc hHc S ω cω
    hpres F M hM Fu Mu hMu k
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
    · exact h2 K hθc hp hn _ LGc hwf hsz hdec hle hamb j hj hjb ⟨⟨c, Q₁, Q₂, Q₃, rfl⟩, hlt⟩ hps hsp Hc Bc hHc
        S ω cω hpres F M hM Fu Mu hMu k
    · exact h1 K hθc hp hn _ LGc hwf hsz hdec hle hamb j hj hjb ⟨⟨c, Q₁, Q₂, Q₃, rfl⟩, heq⟩ hps hsp Hc Bc hHc
        S ω cω hpres F M hM Fu Mu hMu k
  | type2 Xp Xm Qlp =>
    exact h3 K hθc hp hn _ LGc hwf hsz hdec hle hamb j hj hjb ⟨Xp, Xm, Qlp, rfl⟩ hps hsp Hc Bc hHc
      S ω cω hpres F M hM Fu Mu hMu k

/-- **The root trace of a type-1 side couple with both roots in layer `p`** (o104 Prop 7.4 (b), the moving case). -/
theorem tc_trace_t1_move {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) : ∃ Ct : ℝ, 0 ≤ Ct ∧ TcTraceOn θ Ct tcT1M := by
  obtain ⟨C, hC, hmove⟩ := tc_t1_move hθ0 hθ1
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hθc p hp nr hn Q LGc hwf hsz hdec hle hamb j hj hjb hCnd s hps hsp Hc Bc hHc S ω cω
    hpres F M hM Fu Mu hMu k
  obtain ⟨⟨c, Q₁, Q₂, Q₃, rfl⟩, hpart⟩ := hCnd
  obtain ⟨LG₁, LG₂, LG₃, h, hlA, hlB, hlC⟩ := T1Data.exists_of_decodes LGc c Q₁ Q₂ Q₃ hdec hwf
  have hr : layerAt LGc ((0 : Fin 2), []) = p ∧ layerAt LGc ((1 : Fin 2), []) = p := by
    fin_cases j
    · exact ⟨hj, hpart⟩
    · exact ⟨hpart, hj⟩
  obtain ⟨hf₁, hf₂, hf₃⟩ := tc_t1_flat h hlA hlB hlC hwf hamb hr.1 hr.2
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  set R : ℝ := coupling P.d P.L P.γ P.δ ^ 2 *
    (P.C₁ ^ 2 * rb P (nr - 1) (LGc.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links)) * leafSizeProduct LGc Bc *
      starCost S cω with hR
  have hR0 : 0 ≤ R := by
    have := rb_nonneg hC1 K.hδ hL0 (nr - 1) (LGc.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links)
    have := starCost_nonneg' S cω
    have : 0 ≤ leafSizeProduct LGc Bc := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    positivity
  refine (hmove K hθc hp hn h hlA hlB hlC hwf hsz hle hr.1 hr.2 hf₁ hf₂ hf₃ j hps hsp Hc Bc hHc S ω cω hpres
    F M hM Fu Mu hMu k).trans ?_
  refine mul_le_mul' ?_ le_rfl
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC.ne]
  refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
  calc R = 1 * R := (one_mul R).symm
    _ ≤ P.L * R := mul_le_mul_of_nonneg_right hL1 hR0

end WaveTurbulence.Flower.ProtPin
