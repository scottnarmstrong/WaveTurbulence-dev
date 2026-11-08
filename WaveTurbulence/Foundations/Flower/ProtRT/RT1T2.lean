/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.RT1T2M

/-! # RT-GATE (ii), fork C: `RtOneOn` on (c−)

`type2 Xp nil (type1 c Q₁ Q₂ Q₃)` traced at the root of tree `1`: the lone port of the partner chain tree below its
window (`rt1t_t2m_fix`) or in its layer (`rt1t_t2m_move`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- Layers decrease along descendants. -/
theorem rt1t_layer_anti {w : ℕ} (LG : LayeredGarden w) {p : ℕ} (hle : ∀ a, LG.layer a ≤ p) (j : Fin w)
    (q : TTree.Path) : ∀ r : TTree.Path, q ++ r ∈ (LG.garden.tree j).nodes →
      layerAt LG (j, q ++ r) ≤ layerAt LG (j, q) := by
  intro r
  induction r using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton r i ih =>
    intro hm
    have hm' : q ++ r ∈ (LG.garden.tree j).nodes := by
      have := TTree.dropLast_mem_nodes _ hm
      rwa [← List.append_assoc, List.dropLast_concat] at this
    have h1 := tc2a_child_le LG hle (j, q ++ r) i (by simpa [addrExt, List.append_assoc] using hm)
    have e : addrExt (j, q ++ r) [i] = (j, q ++ (r ++ [i])) := by simp [addrExt]
    rw [e] at h1
    exact h1.trans (ih hm')

theorem rt1t_rtWin1 (p q' : ℕ) : rtWin p q' 1 0 = q' ∧ rtWin p q' 1 1 = p := by
  simp [rtWin]

/-- **`RtOneOn` on (c−).** -/
theorem rt1t_T2m {θ c' : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) (hc' : 0 ≤ c') :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ RtOneOn θ c' Ct rtT2m := by
  obtain ⟨Cf, hCf, hfix⟩ := rt1t_t2m_fix hθ0 hθ1
  obtain ⟨Cm, hCm, hmove⟩ := rt1t_t2m_move hθ0 hθ1
  refine ⟨Cf.toReal + Cm.toReal, add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle j hC q' hq' hamb hj hjb hr s hps hsp
    Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k
  obtain ⟨rfl, Xp, c, Q₁, Q₂, Q₃, rfl⟩ := hC
  obtain ⟨LGX, LGQ, D, hdQ⟩ := T2mData.exists_of_decodes LGc Xp c Q₁ Q₂ Q₃ hdec hwf
  obtain ⟨LG₁, LG₂, LG₃, h, hlA, hlB, hlC⟩ := T1Data.exists_of_decodes LGQ c Q₁ Q₂ Q₃ hdQ (tc2_wf hwf).2
  have hamb' : MkSlotsO.CplAmbient p q' p (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)) LGc := by
    have e := rt1t_rtWin1 p q'
    rw [e.1, e.2] at hamb
    exact hamb
  have hr0 : layerAt LGc ((0 : Fin 2), []) ≤ q' := hr
  have hlp : Xp.lonePath ∈ (LGc.garden.tree 0).nodes := by
    have := (D.gd.bot_iff ((0 : Fin 2), [])).1.2 (TTree.nil_mem_nodes _)
    simpa [botAddr] using this
  have hl : layerAt LGc ((0 : Fin 2), Xp.lonePath) ≤ q' :=
    (rt1t_layer_anti LGc hle 0 [] Xp.lonePath (by simpa using hlp)).trans hr0
  have hL1 := K.hL
  have hX := rt1t_budget_nonneg hL1 (by linarith) K.hδ c' (nr - 1)
    (LGc.incoherency (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).links)
    (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _ : 0 ≤ leafSizeProduct LGc Bc) (starCost_nonneg' S cω)
  rcases hl.lt_or_eq with hlt | heq
  · refine (hfix K hFC hc' hC11 hθc hp hn D h hdQ hlA hlB hlC hwf hsz hdec hle hq' hamb' hr0 hj hlt hps hsp
      Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k).trans ?_
    exact rt1t_conv hCf hX (le_add_of_nonneg_right ENNReal.toReal_nonneg) _
  · refine (hmove K hFC hc' hC11 hθc hp hn D h hdQ hlA hlB hlC hwf hsz hdec hle hq' hamb' hr0 hj heq hps hsp
      Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k).trans ?_
    exact rt1t_conv hCm hX (le_add_of_nonneg_left ENNReal.toReal_nonneg) _

end WaveTurbulence.Flower.ProtRT
