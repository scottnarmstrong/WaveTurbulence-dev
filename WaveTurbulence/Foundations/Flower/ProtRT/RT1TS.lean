/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.RT1T2
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildT2

/-! # RT-GATE (ii), fork C: conjugation symmetry of `RtOneOn`

D3's `tc_ambS_conj`, `tc_traceOnF_conj` (ProtPin/TChildSym.lean; copies recorded in RT1T-COPIED.md) for the windowed
ambient (the conjugate swaps the trees, the root signs and the two parent layers: `CplAmbient p q₀ q₁ ↦
CplAmbient p q₁ q₀`, `rtWin p q' j ↦ rtWin p q' (t1sw j)`) and the partner window `q'`; (c+) from (c−), (a−) from
(a+). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier ComplexConjugate
open scoped ENNReal NNReal Classical
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234 WaveTurbulence.PL234.Conj
open WaveTurbulence.Represents WaveTurbulence.ConjCoh

theorem rt1t_amb_conj {LG LGbar : LayeredGarden 2} (h : IsConjugateCouple LG LGbar) {p q₀ q₁ : ℕ} {Q : RegCpl}
    (hA : MkSlotsO.CplAmbient p q₀ q₁ Q LG) : MkSlotsO.CplAmbient p q₁ q₀ (conjCpl Q) LGbar := by
  obtain ⟨w', H, a, b, hcan, hE, hsa, hsb, hpa, hpb, hlay⟩ := hA
  obtain ⟨e, hce⟩ := exists_conj_canon hcan
  have hconj := conjLayered_isConjugateBy H e
  refine ⟨w', conjLayered H e, phi e b, phi e a, hce, embeds_conj hconj hE, ?_, ?_,
    (parAt_conj hconj p b).trans hpb, (parAt_conj hconj p a).trans hpa, ?_⟩
  · rw [nodeSign_conj hconj, hsb]; rfl
  · rw [nodeSign_conj hconj, hsa]
  · intro z
    obtain ⟨z0, rfl⟩ := (PL234.Conj.nodeEquiv h).surjective z
    rw [PL234.Conj.layer_node h, hlay z0]
    have hz : (PL234.Conj.nodeEquiv h z0).1.1 = Equiv.swap (0 : Fin 2) 1 z0.1.1 := rfl
    have hz2 : (PL234.Conj.nodeEquiv h z0).1.2 = z0.1.2 := rfl
    rw [hz2, ← layerAt_conj hconj]
    rcases Fin.exists_fin_two.1 ⟨z0.1.1, rfl⟩ with h0 | h0
    · rw [h0] at hz ⊢
      simp only [Equiv.swap_apply_left] at hz
      simp [hz, phi, addrExt]
    · rw [h0] at hz ⊢
      simp only [Equiv.swap_apply_right] at hz
      simp [hz, phi, addrExt]

/-- **Conjugation symmetry of the root-trace bound.** -/
theorem rt1t_oneOn_conj {θ c' Ct : ℝ} {C C' : RegCpl → LayeredGarden 2 → Fin 2 → Prop}
    (hCC : ∀ Q (LGc : LayeredGarden 2) j, C' Q LGc j → ∀ LGbar : LayeredGarden 2,
      IsConjugateCouple LGc LGbar → C (conjCpl Q) LGbar (t1sw j))
    (hT : RtOneOn θ c' Ct C) : RtOneOn θ c' Ct C' := by
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle j hC q' hq' hamb hj hjb hr s hps hsp Hc Bc
    hHc S ω cω hpres F M hM Fu Mu hMu k
  set LH := conjLayered LGc (Equiv.swap (0 : Fin 2) 1) with hLH
  have h : IsConjugateCouple LGc LH := conjLayered_isConjugateBy LGc (Equiv.swap (0 : Fin 2) 1)
  set ν := nodeEquiv h with hν
  set β := branchEquiv h with hβ
  have hle' : ∀ a, LH.layer a ≤ p := by
    intro a
    obtain ⟨a0, rfl⟩ := ν.surjective a
    rw [layer_node h]; exact hle a0
  have hj' : layerAt LH (t1sw j, []) = p := by
    have hm : ([] : TTree.Path) ∈ (LGc.garden.tree j).nodes := TTree.branching_subset_nodes _ hjb
    have e1 := layerAt_node LGc (⟨(j, []), hm⟩ : GNode LGc.garden.tree)
    have e2 := layerAt_node LH (ν (⟨(j, []), hm⟩ : GNode LGc.garden.tree))
    have e3 := layer_node h (⟨(j, []), hm⟩ : GNode LGc.garden.tree)
    have e4 : (ν (⟨(j, []), hm⟩ : GNode LGc.garden.tree)).1 = (t1sw j, []) := by
      show (Equiv.swap (0 : Fin 2) 1 j, ([] : TTree.Path)) = _
      rw [tc_swap_eq_t1sw]
    rw [e4] at e2
    rw [e2, e3, ← e1, hj]
  have hr' : layerAt LH (t1sw (t1sw j), []) ≤ q' := by
    have hm : ([] : TTree.Path) ∈ (LGc.garden.tree (t1sw j)).nodes := TTree.nil_mem_nodes _
    have e1 := layerAt_node LGc (⟨(t1sw j, []), hm⟩ : GNode LGc.garden.tree)
    have e2 := layerAt_node LH (ν (⟨(t1sw j, []), hm⟩ : GNode LGc.garden.tree))
    have e3 := layer_node h (⟨(t1sw j, []), hm⟩ : GNode LGc.garden.tree)
    have e4 : (ν (⟨(t1sw j, []), hm⟩ : GNode LGc.garden.tree)).1 = (t1sw (t1sw j), []) := by
      show (Equiv.swap (0 : Fin 2) 1 (t1sw j), ([] : TTree.Path)) = _
      rw [tc_swap_eq_t1sw]
    rw [e4] at e2
    rw [e2, e3, ← e1]
    exact hr
  have hamb' : MkSlotsO.CplAmbient p (rtWin p q' (t1sw j) 0) (rtWin p q' (t1sw j) 1) (conjCpl Q) LH := by
    have e : rtWin p q' (t1sw j) 0 = rtWin p q' j 1 ∧ rtWin p q' (t1sw j) 1 = rtWin p q' j 0 := by
      fin_cases j <;> simp [rtWin, t1sw]
    rw [e.1, e.2]
    exact rt1t_amb_conj h hamb
  have htt : t1sw (t1sw j) = j := by fin_cases j <;> rfl
  rw [htt] at hr'
  have hjb' : ([] : TTree.Path) ∈ (LH.garden.tree (t1sw j)).branching := by
    rw [← tc_swap_eq_t1sw, h.tree_eq]; exact hjb
  have hpres' : ∀ a ∈ S.map ν.toEmbedding, Flower.IncTop.StarPresented (30 * P.d)
      (fun y => conj (ω (ν.symm a) y)) (cω (ν.symm a)) := by
    intro a ha
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_map.1 ha
    simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    exact tc_starPresented_conj (hpres a0 ha0)
  have hM' : ∀ b ∈ F.map β.toEmbedding, P.L ≤ M (β.symm b) := by
    intro b hb
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_map.1 hb
    simpa using hM b0 hb0
  have hMu' : ∀ b ∈ Fu.map β.toEmbedding, P.L ≤ Mu (β.symm b) := by
    intro b hb
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_map.1 hb
    simpa using hMu b0 hb0
  have key := hT K hFC hC11 hθc hp hn (conjCpl Q) LH ((wf_conjCpl Q).trans hwf) ((size_conjCpl Q).trans hsz)
    (decodes_conj h hdec) hle' (t1sw j) (hCC Q LGc j hC LH h) hq' hamb' hj' hjb' (by rw [htt]; exact hr') hps hsp
    (transferProf h Hc) (transferProf h Bc) (leafwiseControlled_conj h hHc) (S.map ν.toEmbedding)
    (fun a y => conj (ω (ν.symm a) y)) (fun a => cω (ν.symm a)) hpres' (F.map β.toEmbedding)
    (fun b => M (β.symm b)) hM' (Fu.map β.toEmbedding) (fun b => Mu (β.symm b)) hMu' k
  have hker : ∀ y : Fin 1 → ℝ, kernelProt P.L P.γ P.δ LH (transferProf h Hc)
      (gateM (S.map ν.toEmbedding) (fun a y => conj (ω (ν.symm a) y)) (F.map β.toEmbedding)
        (fun b => M (β.symm b)) (Fu.map β.toEmbedding) (fun b => Mu (β.symm b)))
      (fun b => if b.1.1 = t1sw j then s else y 0) 0 (trFix (t1sw j) s) k (fun _ => 0) 0 =
      conj (kernelProt P.L P.γ P.δ LGc Hc (gateM S ω F M Fu Mu) (fun b => if b.1.1 = j then s else y 0) 0
        (trFix j s) k (fun _ => 0) 0) := by
    intro y
    refine tc_kernelProt_conj h P.L P.γ P.δ Hc _ _ (fun K => ?_) _ _ (fun b => ?_) 0 _ _ (fun b => ?_) k _ _
      (fun _ => rfl) 0
    · unfold gateM
      have hFu := tc_filtWeight_conj h Fu (fun _ => false) Mu K
      have hF := tc_filtWeight_conj h F (fun _ => false) M K
      rw [tc_starWeight_conj h S ω K, hF, hFu, map_mul, map_mul, tc_conj_filtWeight, tc_conj_filtWeight]
    · show (if Equiv.swap (0 : Fin 2) 1 b.1.1 = t1sw j then s else y 0) = if b.1.1 = j then s else y 0
      rw [tc_swap_eq_t1sw]
      fin_cases j <;> rcases Fin.exists_fin_two.1 ⟨b.1.1, rfl⟩ with hb | hb <;> simp [hb, t1sw]
    · show trFix (t1sw j) s (β b) = trFix j s b
      unfold trFix
      have e1 : (β b).1.1 = Equiv.swap (0 : Fin 2) 1 b.1.1 := rfl
      have e2 : (β b).1.2 = b.1.2 := rfl
      rw [e1, e2, tc_swap_eq_t1sw]
      fin_cases j <;> rcases Fin.exists_fin_two.1 ⟨b.1.1, rfl⟩ with hb | hb <;> simp [hb, t1sw]
  have hrn : rn θ (win (q' : ℝ)) (fun y => kernelProt P.L P.γ P.δ LGc Hc (gateM S ω F M Fu Mu)
      (fun b => if b.1.1 = j then s else y 0) 0 (trFix j s) k (fun _ => 0) 0) =
      rn θ (win (q' : ℝ)) (fun y => kernelProt P.L P.γ P.δ LH (transferProf h Hc)
        (gateM (S.map ν.toEmbedding) (fun a y => conj (ω (ν.symm a) y)) (F.map β.toEmbedding)
          (fun b => M (β.symm b)) (Fu.map β.toEmbedding) (fun b => Mu (β.symm b)))
        (fun b => if b.1.1 = t1sw j then s else y 0) 0 (trFix (t1sw j) s) k (fun _ => 0) 0) := by
    simp_rw [hker]
    unfold rn
    exact (VineEstS5C.P2.XNorm00Restr_conj θ (win (q' : ℝ)) Set.univ
      (fun t (_ : Unit) => kernelProt P.L P.γ P.δ LGc Hc (gateM S ω F M Fu Mu)
        (fun b => if b.1.1 = j then s else t 0) 0 (trFix j s) k (fun _ => 0) 0)).symm
  rw [hrn]
  refine key.trans (le_of_eq ?_)
  have hcs : starCost (S.map ν.toEmbedding) (fun a => cω (ν.symm a)) = starCost S cω := by
    unfold starCost
    rw [Finset.prod_map]
    simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
  rw [incoherency_conj h hdec, leafSizeProduct_conj h Bc, hcs]

/-- **(c+) from (c−)** by conjugation. -/
theorem rt1t_T2p_of {θ c' Ct : ℝ} (h : RtOneOn θ c' Ct rtT2m) : RtOneOn θ c' Ct rtT2p := by
  refine rt1t_oneOn_conj (fun Q LGc j hC LGbar _ => ?_) h
  obtain ⟨rfl, Xm, c, Q₁, Q₂, Q₃, rfl⟩ := hC
  obtain ⟨c'', Q₁', Q₂', Q₃', he⟩ := tc_conjCpl_type1 c Q₁ Q₂ Q₃
  refine ⟨by decide, conjChain Xm, c'', Q₁', Q₂', Q₃', ?_⟩
  show RegCpl.type2 (conjChain Xm) (conjChain .nil) (conjCpl (.type1 c Q₁ Q₂ Q₃)) = _
  rw [he]
  rfl

/-- **(a−) from (a+)** by conjugation. -/
theorem rt1t_T2am_of {θ c' Ct : ℝ} (h : RtOneOn θ c' Ct rtT2a) : RtOneOn θ c' Ct rtT2am := by
  refine rt1t_oneOn_conj (fun Q LGc j hC LGbar _ => ?_) h
  obtain ⟨rfl, Xp, m, Qr, Qg, inner, rest, Qlp, rfl⟩ := hC
  exact ⟨by decide, m, conjCpl Qr, conjCpl Qg, conjChain inner, conjChain rest, conjChain Xp, conjCpl Qlp, rfl⟩

end WaveTurbulence.Flower.ProtRT
