/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.RT1TS

/-! # RT-GATE (ii), fork C: `RtOne` from the (a+) slice

`rt1t_one_of_a`: the one-pinned couple bound `RtOne θ c' Ct` for every shape, given the (a+) slice
`RtOneOn θ c' Ct rtT2a`: type 1 (`rt1t_T1`), (c−) (`rt1t_T2m`), (c+) and (a−) by conjugation (`rt1t_T2p_of`,
`rt1t_T2am_of`); `triv` and a leaf traced root are excluded by the branching hypothesis (as D3's
`tc_traceUF_of_cases`, `tc_traceT2_of`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **The one-pinned couple bound from the (a+) slice.** -/
theorem rt1t_one_of_a (h2a : ∀ θ c' : ℝ, 0 ≤ θ → θ ≤ 1 / 4 → 0 ≤ c' → ∃ Ct : ℝ, 0 ≤ Ct ∧ RtOneOn θ c' Ct rtT2a)
    {θ c' : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) (hc' : 0 ≤ c') : ∃ Ct : ℝ, 0 ≤ Ct ∧ RtOne θ c' Ct := by
  obtain ⟨C1, hC1, h1⟩ := rt1t_T1 hθ0 hθ1 hc'
  obtain ⟨Cm, hCm, hm⟩ := rt1t_T2m hθ0 hθ1 hc'
  obtain ⟨Ca, hCa, ha⟩ := h2a θ c' hθ0 hθ1 hc'
  set Ct := max C1 (max Cm Ca) with hCt
  have h1' : RtOneOn θ c' Ct rtT1 := rtOneOn_mono (le_max_left C1 (max Cm Ca)) h1
  have hm' : RtOneOn θ c' Ct rtT2m := rtOneOn_mono ((le_max_left Cm Ca).trans (le_max_right C1 (max Cm Ca))) hm
  have ha' : RtOneOn θ c' Ct rtT2a := rtOneOn_mono ((le_max_right Cm Ca).trans (le_max_right C1 (max Cm Ca))) ha
  have hp' : RtOneOn θ c' Ct rtT2p := rt1t_T2p_of hm'
  have ham' : RtOneOn θ c' Ct rtT2am := rt1t_T2am_of ha'
  refine ⟨Ct, le_max_of_le_left hC1, rtOneOn_true ?_⟩
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle j _ q' hq' hamb hj hjb hr s hps hsp
    Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k
  cases Q with
  | triv =>
    exfalso
    have ht := tree_of_decodes hdec j
    split_ifs at ht <;> rw [ht] at hjb <;> simp [RegCpl.trees, TTree.branching] at hjb
  | type1 c Q₁ Q₂ Q₃ =>
    exact h1' K hFC hC11 hθc hp hn _ LGc hwf hsz hdec hle j ⟨c, Q₁, Q₂, Q₃, rfl⟩ hq' hamb hj hjb hr hps hsp
      Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k
  | type2 Xp Xm Qlp =>
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
        exact hp' K hFC hC11 hθc hp hn _ LGc hwf hsz hdec hle 0 ⟨rfl, Xm, c, Q₁, Q₂, Q₃, rfl⟩ hq' hamb hj hjb hr
          hps hsp Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k
      | pair m Qr Qg inner rest =>
        exact ha' K hFC hC11 hθc hp hn _ LGc hwf hsz hdec hle 0 ⟨rfl, m, Qr, Qg, inner, rest, Xm, Qlp, rfl⟩ hq'
          hamb hj hjb hr hps hsp Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k
    · cases Xm with
      | nil =>
        have hb : ([] : TTree.Path) ∈ Qlp.trees.2.branching := by
          have h1 := hjb
          rw [ht] at h1
          simpa [RegCpl.trees, RegChain.plug] using h1
        obtain ⟨c, Q₁, Q₂, Q₃, rfl⟩ := tc_t2_qlp hQ (Or.inr rfl) hb
        exact hm' K hFC hC11 hθc hp hn _ LGc hwf hsz hdec hle 1 ⟨rfl, Xp, c, Q₁, Q₂, Q₃, rfl⟩ hq' hamb hj hjb hr
          hps hsp Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k
      | pair m Qr Qg inner rest =>
        exact ham' K hFC hC11 hθc hp hn _ LGc hwf hsz hdec hle 1 ⟨rfl, Xp, m, Qr, Qg, inner, rest, Qlp, rfl⟩ hq'
          hamb hj hjb hr hps hsp Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k

example (h2a : ∀ θ c' : ℝ, 0 ≤ θ → θ ≤ 1 / 4 → 0 ≤ c' → ∃ Ct : ℝ, 0 ≤ Ct ∧ RtOneOn θ c' Ct rtT2a)
    {θ c' : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) (hc' : 0 ≤ c') : ∃ Ct : ℝ, 0 ≤ Ct ∧ RtOne θ c' Ct :=
  rt1t_one_of_a h2a hθ0 hθ1 hc'

end WaveTurbulence.Flower.ProtRT
