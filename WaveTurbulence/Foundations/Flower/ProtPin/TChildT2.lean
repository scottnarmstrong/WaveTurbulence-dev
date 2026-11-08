/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildT2mF
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildT2mM
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildSym
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildFinalF
public import WaveTurbulence.Foundations.Flower.ProtPin.HelperA

/-! # D3 PROT-PIN (P7): type-2 traced side couples, assembly

`tc_trace_t2m`: (c−) (`tcT2m`: traced root of tree `1`, empty `-` chain) from `tc_t2m_move` / `tc_t2m_fix`.
The two other shapes are conjugation images (`tc_traceOnF_conj`): (c+) (traced root of tree `0`, empty `+` chain) of
(c−), and (a−) (traced root of tree `1`, nonempty `-` chain) of (a+) = `tcT2a` (HelperA.lean; the helper session's
`tc2a_trace`). `tc_traceT2_of`: `TcTraceOnF θ Ct tcT2` from (c−) and (a+). `cfgUF_termChild_tree_of2`,
`cfgUF_termChild_cap_of2`: the two `CfgUF` slices of the gate from (a+) alone. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234 WaveTurbulence.ConjCoh

/-- (c−): type 2, traced root of tree `1`, empty `-` chain (then `Q_lp` is of type 1). -/
def tcT2m (Q : RegCpl) (_LGc : LayeredGarden 2) (j : Fin 2) (_p : ℕ) : Prop :=
  j = 1 ∧ ∃ (Xp : RegChain) (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl), Q = RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)

/-- (c+): type 2, traced root of tree `0`, empty `+` chain. -/
def tcT2p (Q : RegCpl) (_LGc : LayeredGarden 2) (j : Fin 2) (_p : ℕ) : Prop :=
  j = 0 ∧ ∃ (Xm : RegChain) (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl), Q = RegCpl.type2 .nil Xm (.type1 c Q₁ Q₂ Q₃)

/-- (a−): type 2, traced root of tree `1`, nonempty `-` chain. -/
def tcT2am (Q : RegCpl) (_LGc : LayeredGarden 2) (j : Fin 2) (_p : ℕ) : Prop :=
  j = 1 ∧ ∃ (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (Qlp : RegCpl),
    Q = RegCpl.type2 Xp (RegChain.pair m Qr Qg inner rest) Qlp

/-- **(c−).** -/
theorem tc_trace_t2m {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) : ∃ Ct : ℝ, 0 ≤ Ct ∧ TcTraceOnF θ Ct tcT2m := by
  obtain ⟨Cf, hCf, hfix⟩ := tc_t2m_fix hθ0 hθ1
  obtain ⟨Cm, hCm, hmove⟩ := tc_t2m_move hθ0 hθ1
  refine ⟨max Cf.toReal Cm.toReal, le_max_of_le_left ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle hamb j hj hjb hCnd s hps hsp Hc Bc hHc S
    ω cω hpres F M hM Fu Mu hMu k
  obtain ⟨rfl, Xp, c, Q₁, Q₂, Q₃, rfl⟩ := hCnd
  obtain ⟨LGX, LGQ, D, hdQ⟩ := T2mData.exists_of_decodes LGc Xp c Q₁ Q₂ Q₃ hdec hwf
  obtain ⟨LG₁, LG₂, LG₃, h, hlA, hlB, hlC⟩ := T1Data.exists_of_decodes LGQ c Q₁ Q₂ Q₃ hdQ (tc2_wf hwf).2
  have hl : layerAt LGc ((0 : Fin 2), Xp.lonePath) ≤ p := layerAt_le_of_forall_layer_le hle _
  have hR : ∀ (C : ℝ≥0∞), C < ⊤ → C ≤ ENNReal.ofReal (max Cf.toReal Cm.toReal) → ∀ X : ℝ≥0∞,
      C * X ≤ ENNReal.ofReal (max Cf.toReal Cm.toReal) * X := fun C _ hC X => mul_le_mul' hC le_rfl
  have hX0 : ∀ x : ℝ, 0 ≤ x → ∀ Y : ℝ≥0∞, ENNReal.ofReal (max Cf.toReal Cm.toReal) * ENNReal.ofReal x * Y =
      ENNReal.ofReal (max Cf.toReal Cm.toReal * x) * Y := fun x hx Y => by
    rw [ENNReal.ofReal_mul (le_max_of_le_left ENNReal.toReal_nonneg)]
  have hnn : 0 ≤ P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (nr - 1) (LGc.incoherency
      (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).links)) * leafSizeProduct LGc Bc * starCost S cω) := by
    have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
    have := rb_nonneg (by linarith : (0 : ℝ) ≤ P.C₁) K.hδ hL0 (nr - 1)
      (LGc.incoherency (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).links)
    have := starCost_nonneg' S cω
    have : 0 ≤ leafSizeProduct LGc Bc := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 := sq_nonneg _
    have : 0 ≤ P.C₁ := by linarith
    positivity
  rw [← hX0 _ hnn]
  rcases hl.lt_or_eq with hlt | heq
  · refine (hfix K hFC hθc hp hn D h hdQ hlA hlB hlC hwf hsz hdec hle hamb hj hlt hps hsp Hc Bc hHc S ω cω hpres
      F M hM Fu Mu hMu k).trans (mul_le_mul' (hR _ hCf ?_ _) le_rfl)
    exact (ENNReal.le_ofReal_iff_toReal_le hCf.ne (le_max_of_le_left ENNReal.toReal_nonneg)).2 (le_max_left _ _)
  · refine (hmove K hFC hθc hp hn D h hdQ hlA hlB hlC hwf hsz hdec hle hamb hj heq hps hsp Hc Bc hHc S ω cω hpres
      F M hM Fu Mu hMu k).trans (mul_le_mul' (hR _ hCm ?_ _) le_rfl)
    exact (ENNReal.le_ofReal_iff_toReal_le hCm.ne (le_max_of_le_left ENNReal.toReal_nonneg)).2 (le_max_right _ _)

theorem tc_conjCpl_type1 (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl) :
    ∃ (c' : MiniCplCode) (Q₁' Q₂' Q₃' : RegCpl), conjCpl (.type1 c Q₁ Q₂ Q₃) = .type1 c' Q₁' Q₂' Q₃' := by
  by_cases hc : c = 0
  · exact ⟨c, conjCpl Q₁, conjCpl Q₂, conjCpl Q₃, by simp [conjCpl, hc]⟩
  · exact ⟨c, conjCpl Q₃, conjCpl Q₂, conjCpl Q₁, by simp [conjCpl, hc]⟩

/-- **(c+) from (c−)** by conjugation. -/
theorem tc_trace_t2p {θ Ct : ℝ} (h : TcTraceOnF θ Ct tcT2m) : TcTraceOnF θ Ct tcT2p := by
  refine tc_traceOnF_conj (fun Q LGc j p hC LGbar _ => ?_) h
  obtain ⟨rfl, Xm, c, Q₁, Q₂, Q₃, rfl⟩ := hC
  obtain ⟨c', Q₁', Q₂', Q₃', he⟩ := tc_conjCpl_type1 c Q₁ Q₂ Q₃
  refine ⟨by decide, conjChain Xm, c', Q₁', Q₂', Q₃', ?_⟩
  show RegCpl.type2 (conjChain Xm) (conjChain .nil) (conjCpl (.type1 c Q₁ Q₂ Q₃)) = _
  rw [he]
  rfl

/-- **(a−) from (a+)** by conjugation. -/
theorem tc_trace_t2am {θ Ct : ℝ} (h : TcTraceOnF θ Ct tcT2a) : TcTraceOnF θ Ct tcT2am := by
  refine tc_traceOnF_conj (fun Q LGc j p hC LGbar _ => ?_) h
  obtain ⟨rfl, Xp, m, Qr, Qg, inner, rest, Qlp, rfl⟩ := hC
  exact ⟨by decide, m, conjCpl Qr, conjCpl Qg, conjChain inner, conjChain rest, conjChain Xp, conjCpl Qlp, rfl⟩

/-- A branching root of an empty chain side of a type-2 couple: the lone-pair couple is of type 1. -/
theorem tc_t2_qlp {Qlp : RegCpl} (hwf : Qlp.wf = true ∧ Qlp.isType2 = false) {T : TTree}
    (hT : T = Qlp.trees.1 ∨ T = Qlp.trees.2) (hb : ([] : TTree.Path) ∈ T.branching) :
    ∃ (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl), Qlp = .type1 c Q₁ Q₂ Q₃ := by
  cases Qlp with
  | triv =>
    exfalso
    rcases hT with rfl | rfl <;> simp [RegCpl.trees, TTree.branching] at hb
  | type1 c Q₁ Q₂ Q₃ => exact ⟨c, Q₁, Q₂, Q₃, rfl⟩
  | type2 _ _ _ => simp [RegCpl.isType2] at hwf

/-- **The type-2 case of the root-trace bound**, from (c−) and (a+). -/
theorem tc_traceT2_of {θ Ct : ℝ} (h2m : TcTraceOnF θ Ct tcT2m) (h2a : TcTraceOnF θ Ct tcT2a) :
    TcTraceOnF θ Ct tcT2 := by
  have h2p : TcTraceOnF θ Ct tcT2p := tc_trace_t2p h2m
  have h2am : TcTraceOnF θ Ct tcT2am := tc_trace_t2am h2a
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle hamb j hj hjb hC s hps hsp Hc Bc hHc S ω
    cω hpres F M hM Fu Mu hMu k
  obtain ⟨Xp, Xm, Qlp, rfl⟩ := hC
  have hwf' := hwf
  simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hwf'
  have hQ : Qlp.wf = true ∧ Qlp.isType2 = false := ⟨hwf'.1.1.2, hwf'.1.2⟩
  have ht := tree_of_decodes hdec j
  rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with rfl | rfl
  · cases Xp with
    | nil =>
      have hb : ([] : TTree.Path) ∈ Qlp.trees.1.branching := by
        have h1 := hjb
        rw [ht] at h1
        simpa [RegCpl.trees, RegChain.plug] using h1
      obtain ⟨c, Q₁, Q₂, Q₃, rfl⟩ := tc_t2_qlp hQ (Or.inl rfl) hb
      exact h2p K hFC hC11 hθc hp hn _ LGc hwf hsz hdec hle hamb 0 hj hjb
        ⟨rfl, Xm, c, Q₁, Q₂, Q₃, rfl⟩ hps hsp Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k
    | pair m Qr Qg inner rest =>
      exact h2a K hFC hC11 hθc hp hn _ LGc hwf hsz hdec hle hamb 0 hj hjb
        ⟨rfl, m, Qr, Qg, inner, rest, Xm, Qlp, rfl⟩ hps hsp Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k
  · cases Xm with
    | nil =>
      have hb : ([] : TTree.Path) ∈ Qlp.trees.2.branching := by
        have h1 := hjb
        rw [ht] at h1
        simpa [RegCpl.trees, RegChain.plug] using h1
      obtain ⟨c, Q₁, Q₂, Q₃, rfl⟩ := tc_t2_qlp hQ (Or.inr rfl) hb
      exact h2m K hFC hC11 hθc hp hn _ LGc hwf hsz hdec hle hamb 1 hj hjb
        ⟨rfl, Xp, c, Q₁, Q₂, Q₃, rfl⟩ hps hsp Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k
    | pair m Qr Qg inner rest =>
      exact h2am K hFC hC11 hθc hp hn _ LGc hwf hsz hdec hle hamb 1 hj hjb
        ⟨rfl, Xp, m, Qr, Qg, inner, rest, Qlp, rfl⟩ hps hsp Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k

/-- **(P7), trees, the `CfgUF` slice of the gate**, from the (a+) case. -/
theorem cfgUF_termChild_tree_of2 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4)
    (h2a : ∃ Ct : ℝ, 0 ≤ Ct ∧ TcTraceOnF θ Ct tcT2a) : ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgUF θ Cr selTChild := by
  obtain ⟨C₁, hC₁, hm⟩ := tc_trace_t2m hθ0 hθ1
  obtain ⟨C₂, hC₂, ha⟩ := h2a
  exact cfgUF_termChild_tree_of hθ0 hθ1 (le_max_of_le_left hC₁)
    (tc_traceT2_of (tcTraceOnF_mono (le_max_left _ _) hm) (tcTraceOnF_mono (le_max_right _ _) ha))

/-- **(P7), cap couples, the `CfgUF` slice of the gate**, from the (a+) case. -/
theorem cfgUF_termChild_cap_of2 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4)
    (h2a : ∃ Ct : ℝ, 0 ≤ Ct ∧ TcTraceOnF θ Ct tcT2a) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgUF θ Cr (fun w _ _ cfg => w = 2 ∧ ∃ i, cfg = .termChild i) := by
  obtain ⟨C₁, hC₁, hm⟩ := tc_trace_t2m hθ0 hθ1
  obtain ⟨C₂, hC₂, ha⟩ := h2a
  exact cfgUF_termChild_cap_of hθ0 hθ1 (le_max_of_le_left hC₁)
    (tc_traceT2_of (tcTraceOnF_mono (le_max_left _ _) hm) (tcTraceOnF_mono (le_max_right _ _) ha))

/-- **The gate's tree input** (`hTree` of `protBoundGate_of_termChild`), from the helper's (a+). -/
theorem cfgUF_termChild_tree_of_t2a
    (h2a : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 → ∃ Ct : ℝ, 0 ≤ Ct ∧ TcTraceOnF θ Ct tcT2a) :
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 → ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgUF θ Cr selTChild :=
  fun θ h0 h1 => cfgUF_termChild_tree_of2 h0 h1 (h2a θ h0 h1)

/-- **The gate's cap input** (`hCapTC` of `protBoundGate_of_termChild`), from the helper's (a+). -/
theorem cfgUF_termChild_cap_of_t2a
    (h2a : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 → ∃ Ct : ℝ, 0 ≤ Ct ∧ TcTraceOnF θ Ct tcT2a) :
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 → ∃ Ct : ℝ, 0 ≤ Ct ∧
      CfgUF θ Ct (fun w _ _ cfg => w = 2 ∧ ∃ i, cfg = .termChild i) :=
  fun θ h0 h1 => cfgUF_termChild_cap_of2 h0 h1 (h2a θ h0 h1)

end WaveTurbulence.Flower.ProtPin
