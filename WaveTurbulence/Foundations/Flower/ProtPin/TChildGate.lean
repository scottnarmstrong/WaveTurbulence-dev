/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildFinal
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildTrace
public import WaveTurbulence.Foundations.Flower.ProtPin.GateParts

/-! # D3 PROT-PIN (P7): the `termChild` tree slice of `CfgU`, from the two open root-trace cases

`tc_cfgU_of_traceU`: the slice `CfgU θ Cr (w = 1 ∧ cfg = termChild i)` from the root-trace bound `TcTraceU θ Ct`.
`cfgU_termChild_tree_of`: the same from the two open cases of `TcTraceU` (type 1 with the partner root below `p`,
type 2); the third case (type 1, both roots in layer `p`) is `tc_trace_t1_move`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

/-- **(P7), trees, as a `CfgU` slice**, given the root-trace bound `TcTraceU θ Ct`. -/
theorem tc_cfgU_of_traceU {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {Ct : ℝ}, 0 ≤ Ct → TcTraceU θ Ct →
      CfgU θ (Cr * Ct * 2) (fun w _ _ cfg => w = 1 ∧ ∃ i, cfg = .termChild i) := by
  obtain ⟨Cr, hCr, hfin⟩ := tc_termChild_final_of hθ0 hθ1
  refine ⟨Cr, hCr, ?_⟩
  intro Ct hCt hT P C₁a C₂a C₁b C₂b K hη CL hCL hC11 hLOE _hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb hsel
    s t hps hst htp q' _hq' S ω cω hpres F M hM Fu Mu hMu ind hind _hind1 H B hH b₀ c₀
  obtain ⟨rfl, i, rfl⟩ := hsel
  exact hfin hCt hT K (pieceLoss_eta hη) le_rfl hCL hC11 hLOE hbig2 hp hn LG X hsh hsz
    (treeAmb_of_protAmbient hamb) i hval hps hst htp q' S ω cω hpres F M hM Fu Mu hMu ind hind H B hH b₀ c₀

/-- **(P7), trees, as a `CfgU` slice**, from the two open cases of the root-trace bound. -/
theorem cfgU_termChild_tree_of {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) {Ct : ℝ} (hCt : 0 ≤ Ct)
    (hF : TcTraceOn θ Ct tcT1F) (h2 : TcTraceOn θ Ct tcT2) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgU θ Cr (fun w _ _ cfg => w = 1 ∧ ∃ i, cfg = .termChild i) := by
  obtain ⟨Cr, hCr, hcfg⟩ := tc_cfgU_of_traceU hθ0 hθ1
  obtain ⟨C₁, hC₁, hM⟩ := tc_trace_t1_move hθ0 hθ1
  set Cm : ℝ := max Ct C₁ with hCm
  have hCm0 : 0 ≤ Cm := le_max_of_le_left hCt
  have hT : TcTraceU θ Cm := tc_traceU_of_cases (tcTraceOn_mono (le_max_right _ _) hM)
    (tcTraceOn_mono (le_max_left _ _) hF) (tcTraceOn_mono (le_max_left _ _) h2)
  exact ⟨Cr * Cm * 2, by positivity, hcfg hCm0 hT⟩

end WaveTurbulence.Flower.ProtPin
