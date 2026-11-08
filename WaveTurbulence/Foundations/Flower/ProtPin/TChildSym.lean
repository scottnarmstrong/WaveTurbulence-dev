/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildTraceF
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.ConjNorm

/-! # D3 PROT-PIN (P7): conjugation symmetry of the root-trace bound

`tc_kernelProt_conj`: main's conjugation of leafwise kernels (`kernelLeaves_conj`) for `kernelProt` with designated
branches (the free-time integral `protTime` transported through the free branches). `tc_ambS_conj`: the signed
ambient of the conjugate couple (main's `isCoherentCoupleAt_conj_aux` without the coherence clause).
`tc_traceOnF_conj`: `TcTraceOnF` for traced couples `(Q, LGc, j)` follows from `TcTraceOnF` for
`(conjCpl Q, LGc̄, 1 - j)`: the traced kernel of the conjugate couple is the conjugate kernel, `rn` is conjugation
invariant (main `XNorm00Restr_conj`), and every quantity of the bound is conjugation invariant. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier ComplexConjugate
open scoped ENNReal NNReal Classical
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234 WaveTurbulence.PL234.Conj
open WaveTurbulence.Represents WaveTurbulence.ConjCoh

variable {w d : ℕ} {LG LH : LayeredGarden w} {e : Fin w ≃ Fin w}

theorem tc_mem_protDom_conj (h : IsConjugateBy LG LH e) (up : GBranch LG.garden.tree → ℝ)
    (up' : GBranch LH.garden.tree → ℝ) (hup : ∀ b, up' (branchEquiv h b) = up b) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (fix' : GBranch LH.garden.tree → Option ℝ)
    (hfix : ∀ b, fix' (branchEquiv h b) = fix b) (τ : GBranch LG.garden.tree → ℝ) :
    (fun b => τ ((branchEquiv h).symm b)) ∈ protDom LH up' s fix' ↔ τ ∈ protDom LG up s fix := by
  unfold protDom kDomainFix
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [← (branchEquiv h).forall_congr_right, ← (branchEquiv h).forall_congr_right]
  simp only [branch_toNode, layer_node, hup, hfix, Equiv.symm_apply_apply, loneParent_iff]
  refine and_congr (forall_congr' fun b => and_congr Iff.rfl ?_) Iff.rfl
  rw [← (branchEquiv h).forall_congr_right]
  simp only [isChildOf_iff, hfix, Equiv.symm_apply_apply]

theorem tc_protTime_conj (h : IsConjugateBy LG LH e) (L γ δ : ℝ) (up : GBranch LG.garden.tree → ℝ)
    (up' : GBranch LH.garden.tree → ℝ) (hup : ∀ b, up' (branchEquiv h b) = up b) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (fix' : GBranch LH.garden.tree → Option ℝ)
    (hfix : ∀ b, fix' (branchEquiv h b) = fix b) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LH up' s fix' (fun a => K ((nodeEquiv h).symm a)) = conj (protTime L γ δ LG up s fix K) := by
  unfold protTime
  set Φ : {b : GBranch LG.garden.tree // fix b = none} ≃ {b : GBranch LH.garden.tree // fix' b = none} :=
    (branchEquiv h).subtypeEquiv (fun b => by rw [hfix]) with hΦ
  rw [← integral_conj, ← integral_arrow_equiv Φ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  simp only
  have hext : LH.garden.extendFix fix' (fun b => σ (Φ.symm b)) =
      fun b => LG.garden.extendFix fix σ ((branchEquiv h).symm b) := by
    funext b'
    obtain ⟨b, rfl⟩ := (branchEquiv h).surjective b'
    rw [Equiv.symm_apply_apply]
    cases hb : fix b with
    | some v =>
      rw [extendFix_some LG.garden fix _ hb]
      exact extendFix_some LH.garden fix' _ (show fix' (branchEquiv h b) = some v by rw [hfix, hb])
    | none =>
      rw [extendFix_free _ _ _ ⟨b, hb⟩, extendFix_free _ _ _ ⟨branchEquiv h b, by rw [hfix, hb]⟩]
      congr 1
      exact Φ.symm_apply_apply ⟨b, hb⟩
  rw [hext]
  set τ := LG.garden.extendFix fix σ
  by_cases hD : τ ∈ protDom LG up s fix
  · rw [Set.indicator_of_mem ((tc_mem_protDom_conj h up up' hup s fix fix' hfix τ).2 hD), Set.indicator_of_mem hD]
    exact phaseProd_eq h L γ δ K τ
  · rw [Set.indicator_of_notMem (fun h' => hD ((tc_mem_protDom_conj h up up' hup s fix fix' hfix τ).1 h')),
      Set.indicator_of_notMem hD, map_zero]

/-- **`kernelProt` of a conjugate garden is the conjugate kernel.** -/
theorem tc_kernelProt_conj (h : IsConjugateBy LG LH e) (L γ δ : ℝ) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (m' : (GNode LH.garden.tree → Mom d) → ℂ)
    (hm : ∀ K, m' (fun a => K ((nodeEquiv h).symm a)) = conj (m K))
    (up : GBranch LG.garden.tree → ℝ) (up' : GBranch LH.garden.tree → ℝ) (hup : ∀ b, up' (branchEquiv h b) = up b)
    (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (fix' : GBranch LH.garden.tree → Option ℝ)
    (hfix : ∀ b, fix' (branchEquiv h b) = fix b) (k₀ : Mom d) (nroot nroot' : Fin w → (Fin d → ℤ))
    (hroot : ∀ j, nroot' (e j) = nroot j) (nfl : Fin d → ℤ) :
    kernelProt L γ δ LH (transferProf h H) m' up' s fix' k₀ nroot' nfl =
      conj (kernelProt L γ δ LG H m up s fix k₀ nroot nfl) := by
  rw [kernelProt_eq_tsum, kernelProt_eq_tsum, map_mul, map_mul, map_pow, Complex.conj_ofReal, order_eq h, zeta_eq h,
    Complex.conj_tsum, ← (decEquiv h nroot nroot' hroot nfl).tsum_eq]
  congr 1
  refine tsum_congr fun κ => ?_
  unfold protSummand
  have hd : (decEquiv h nroot nroot' hroot nfl κ).1 = fun a => κ.1 ((nodeEquiv h).symm a) := rfl
  have hc : cosetDecoration LH.garden L k₀ (decEquiv h nroot nroot' hroot nfl κ).1 =
      fun a => cosetDecoration LG.garden L k₀ κ.1 ((nodeEquiv h).symm a) := rfl
  have hκ : ∀ ℓ : GLeaf LG.garden.tree, cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode =
      cosetDecoration LG.garden L k₀ κ.1 (LG.garden.pair ℓ).toNode := fun ℓ => by
    unfold cosetDecoration
    rw [κ.2.1.2 ℓ]
  rw [hc, hd, hm, epsDec_eq h κ.1, tc_protTime_conj h L γ δ up up' hup s fix fix' hfix, prod_inputs_conj h,
    map_mul, map_mul, map_mul, Complex.conj_ofReal, map_prod]
  congr 2
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  rw [Complex.conj_ofReal, transferProf_leaf, Equiv.symm_apply_apply, LG.garden.pair_pair, leaf_toNode]
  simp only [Equiv.symm_apply_apply]
  rw [← hκ ℓ]

/-! ### The signed ambient of the conjugate couple -/

theorem tc_ambS_conj {LG LGbar : LayeredGarden 2} (h : IsConjugateCouple LG LGbar) {p : ℕ} {Q : RegCpl}
    (hA : TcCplAmbS p Q LG) : TcCplAmbS p (conjCpl Q) LGbar := by
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

theorem tc_swap_eq_t1sw (j : Fin 2) : Equiv.swap (0 : Fin 2) 1 j = t1sw j := by
  fin_cases j <;> rfl

/-- **Conjugation symmetry of the root-trace bound.** -/
theorem tc_traceOnF_conj {θ Ct : ℝ} {C C' : RegCpl → (LGc : LayeredGarden 2) → Fin 2 → ℕ → Prop}
    (hCC : ∀ Q (LGc : LayeredGarden 2) j p, C' Q LGc j p → ∀ LGbar : LayeredGarden 2,
      IsConjugateCouple LGc LGbar → C (conjCpl Q) LGbar (t1sw j) p)
    (hT : TcTraceOnF θ Ct C) : TcTraceOnF θ Ct C' := by
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle hamb j hj hjb hC s hps hsp Hc Bc hHc S ω cω
    hpres F M hM Fu Mu hMu k
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
    (decodes_conj h hdec) hle' (tc_ambS_conj h hamb) (t1sw j) hj' hjb' (hCC Q LGc j p hC LH h) hps hsp
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
  have hrn : rn θ (win p) (fun y => kernelProt P.L P.γ P.δ LGc Hc (gateM S ω F M Fu Mu)
      (fun b => if b.1.1 = j then s else y 0) 0 (trFix j s) k (fun _ => 0) 0) =
      rn θ (win p) (fun y => kernelProt P.L P.γ P.δ LH (transferProf h Hc)
        (gateM (S.map ν.toEmbedding) (fun a y => conj (ω (ν.symm a) y)) (F.map β.toEmbedding)
          (fun b => M (β.symm b)) (Fu.map β.toEmbedding) (fun b => Mu (β.symm b)))
        (fun b => if b.1.1 = t1sw j then s else y 0) 0 (trFix (t1sw j) s) k (fun _ => 0) 0) := by
    simp_rw [hker]
    unfold rn
    exact (VineEstS5C.P2.XNorm00Restr_conj θ (win p) Set.univ
      (fun t (_ : Unit) => kernelProt P.L P.γ P.δ LGc Hc (gateM S ω F M Fu Mu)
        (fun b => if b.1.1 = j then s else t 0) 0 (trFix j s) k (fun _ => 0) 0)).symm
  rw [hrn]
  refine key.trans (le_of_eq ?_)
  have hcs : starCost (S.map ν.toEmbedding) (fun a => cω (ν.symm a)) = starCost S cω := by
    unfold starCost
    rw [Finset.prod_map]
    simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
  rw [incoherency_conj h hdec, leafSizeProduct_conj h Bc, hcs]

end WaveTurbulence.Flower.ProtPin
