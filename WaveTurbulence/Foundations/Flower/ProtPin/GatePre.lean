/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.GateMain
public import WaveTurbulence.Foundations.Flower.ProtPin.PenPre2

/-! # D3 PROT-PIN: the slice (P4) with a nonempty prefix (`pen_final_prefix`) -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **penTerm, trees, nonempty prefix and empty interior.** -/
theorem cfgU_pen_prefix {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgU θ Cr selPenPrefix := by
  obtain ⟨Cr, h0, hf⟩ := pen_final_prefix hθ0 hθ1
  refine ⟨Cr, h0, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hη CL hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb hsel s t hps hst
    htp q' hq' S ω cω hpres F M hM Fu Mu hMu ind hind hind1 H B hH b₀ c₀
  obtain ⟨rfl, rfl, hX⟩ := hsel
  unfold selPenNoPrefix at hX
  push_neg at hX
  obtain ⟨Xp, m, Qr, Qg, inner, rfl, hin, hXp⟩ := hX
  have hinn : inner = .nil := eq_nil_of_lonePath hin
  subst hinn
  obtain ⟨LGp, LGi, LGr, LGg, D⟩ := CutTermData.exists_of_wf LG Xp m Qr Qg .nil hsh.2.1 hsh.1
  exact hf K (pieceLoss_eta hη) le_rfl hCL hC11 hLOE hbig2 hp hn D hXp hsh hsz hamb hps hst htp q' S ω cω hpres
    F M hM Fu Mu hMu ind hind H B hH b₀ c₀

end WaveTurbulence.Flower.ProtPin
