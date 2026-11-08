/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs
public import WaveTurbulence.Foundations.Stage1.Represents.RepConj1
public import WaveTurbulence.Foundations.VineEst.CoupleRowConj

/-! # D3 PROT-PIN (P7): the coherent couple gate in both orientations (weighted conjugation)

FILT-COH's `FiltCoherentBoundAt` bounds a coherent couple `IsCoherentCoupleAt p q q'` only for `q' ≤ q`. For `q < q'`
the conjugate couple (`conjCpl Q` on `conjLayered LG (swap 0 1)`) is coherent at `(p, q', q)` (main
`isCoherentCoupleAt_conj`), and the WEIGHTED kernel of the conjugate garden, with the transported profiles, star weights
`conj ∘ ω` and filters, is the conjugate kernel with the clocks exchanged (`tc_kernelLeavesW_conj`, the weighted form of
main's `kernelLeaves_conj`); `XNormRestr` is invariant under swap-and-conjugate. Result: `tc_coh_any`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory ComplexConjugate
open scoped ENNReal Classical

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs TTree WaveTurbulence.PL234 WaveTurbulence.PL234.Conj
open WaveTurbulence.Represents WaveTurbulence.ConjCoh

variable {w d : ℕ} {LG LH : LayeredGarden w} {e : Fin w ≃ Fin w}

/-- **The weighted leafwise kernel of a conjugate garden is the conjugate kernel.** -/
theorem tc_kernelLeavesW_conj (h : IsConjugateBy LG LH e) (L γ δ : ℝ) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (up' : GBranch LH.garden.tree → ℝ) (hup : ∀ b, up' (branchEquiv h b) = up b)
    (s : ℝ) (k₀ : Mom d) (nroot nroot' : Fin w → (Fin d → ℤ)) (hroot : ∀ j, nroot' (e j) = nroot j)
    (nfl : Fin d → ℤ) (m : (GNode LG.garden.tree → Mom d) → ℂ) (m' : (GNode LH.garden.tree → Mom d) → ℂ)
    (hm : ∀ K, m' (fun a => K ((nodeEquiv h).symm a)) = conj (m K)) :
    Flower.Stage1W.kernelLeavesW L γ δ LH (transferProf h H) up' s k₀ nroot' nfl m' =
      conj (Flower.Stage1W.kernelLeavesW L γ δ LG H up s k₀ nroot nfl m) := by
  unfold Flower.Stage1W.kernelLeavesW
  rw [map_mul, map_mul, map_pow, Complex.conj_ofReal, order_eq h, zeta_eq h, Complex.conj_tsum,
    ← (decEquiv h nroot nroot' hroot nfl).tsum_eq]
  congr 1
  refine tsum_congr fun κ => ?_
  rw [map_mul, ← summand_leaves_eq h L γ δ H up up' hup s k₀ nroot nroot' hroot nfl κ]
  congr 1
  have hc : cosetDecoration LH.garden L k₀ (decEquiv h nroot nroot' hroot nfl κ).1 =
      fun a => cosetDecoration LG.garden L k₀ κ.1 ((nodeEquiv h).symm a) := rfl
  rw [hc]
  exact hm _

/-- Couples: the conjugate garden exchanges the clocks. -/
theorem tc_coupleW_conj {LG LH : LayeredGarden 2} (h : IsConjugateCouple LG LH) (L γ δ : ℝ) (H : LeafProfiles 2 d)
    (t s : ℝ) (k : Mom d) (m : (GNode LG.garden.tree → Mom d) → ℂ) (m' : (GNode LH.garden.tree → Mom d) → ℂ)
    (hm : ∀ K, m' (fun a => K ((nodeEquiv h).symm a)) = conj (m K)) :
    Flower.Stage1W.kernelLeavesW L γ δ LH (transferProf h H) (fun b => if b.1.1 = 0 then s else t) 0 k
        (fun _ => 0) 0 m' =
      conj (Flower.Stage1W.kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0 m) := by
  refine tc_kernelLeavesW_conj h L γ δ H _ _ (fun b => ?_) 0 k _ _ (fun _ => rfl) 0 m m' hm
  rcases b with ⟨⟨i, p⟩, hp⟩
  show (if Equiv.swap (0 : Fin 2) 1 i = 0 then s else t) = if i = 0 then t else s
  fin_cases i <;> simp

/-! ### Transport of the multiplier data -/

theorem tc_starNode_conj (h : IsConjugateBy LG LH e) (a : GNode LG.garden.tree) (s : Fin 4) :
    Flower.IncTop.starNode (nodeEquiv h a) s = nodeEquiv h (Flower.IncTop.starNode a s) := by
  unfold Flower.IncTop.starNode
  by_cases hb : a.1.2 ∈ (LG.garden.tree a.1.1).branching
  · have hb' : (nodeEquiv h a).1.2 ∈ (LH.garden.tree (nodeEquiv h a).1.1).branching := by
      show a.1.2 ∈ (LH.garden.tree (e a.1.1)).branching
      rw [h.tree_eq]; exact hb
    rw [dite_eq_left_of_eq_true (eq_true hb'), dite_eq_left_of_eq_true (eq_true hb)]
    refine Fin.cases rfl (fun j => ?_) s
    simp only [Fin.cases_succ]
    exact branch_child h ⟨a.1, hb⟩ j
  · have hb' : (nodeEquiv h a).1.2 ∉ (LH.garden.tree (nodeEquiv h a).1.1).branching := by
      show a.1.2 ∉ (LH.garden.tree (e a.1.1)).branching
      rw [h.tree_eq]; exact hb
    rw [dite_eq_right_of_eq_false (eq_false hb'), dite_eq_right_of_eq_false (eq_false hb)]

theorem tc_starWeight_conj (h : IsConjugateBy LG LH e) (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ) (K : GNode LG.garden.tree → Mom d) :
    Flower.IncTop.starWeight (S.map (nodeEquiv h).toEmbedding)
        (fun a' y => conj (ω ((nodeEquiv h).symm a') y)) (fun a => K ((nodeEquiv h).symm a)) =
      conj (Flower.IncTop.starWeight S ω K) := by
  unfold Flower.IncTop.starWeight
  rw [Finset.prod_map, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
  congr 2
  unfold Flower.IncTop.starMomenta
  congr 1
  funext s
  rw [tc_starNode_conj h a s]
  show K ((nodeEquiv h).symm (nodeEquiv h _)) = _
  rw [Equiv.symm_apply_apply]

theorem tc_filtWeight_conj (h : IsConjugateBy LG LH e) (F : Finset (GBranch LG.garden.tree))
    (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ) (K : GNode LG.garden.tree → Mom d) :
    filtWeight (F.map (branchEquiv h).toEmbedding) (fun b => ann ((branchEquiv h).symm b))
        (fun b => M ((branchEquiv h).symm b)) (fun a => K ((nodeEquiv h).symm a)) = filtWeight F ann M K := by
  unfold filtWeight
  rw [Finset.prod_map]
  refine Finset.prod_congr rfl fun b _ => ?_
  simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
  rw [omega_eq h K b]

theorem tc_conj_filtWeight {G : Garden w} (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool)
    (M : GBranch G.tree → ℝ) (K : GNode G.tree → Mom d) : conj (filtWeight F ann M K) = filtWeight F ann M K := by
  unfold filtWeight
  rw [map_prod]
  exact Finset.prod_congr rfl fun _ _ => Complex.conj_ofReal _

/-- The conjugate of a presented star weight is presented, with the same moment. -/
theorem tc_starPresented_conj {J : ℕ} {ω : Flower.IncTop.Star d → ℂ} {c : ℝ}
    (hω : Flower.IncTop.StarPresented J ω c) : Flower.IncTop.StarPresented J (fun y => conj (ω y)) c := by
  obtain ⟨α, mα, M, hM, hv⟩ := hω
  refine ⟨α, mα, ⟨M.μ, M.sigmaFinite, fun a => -M.frequency a, M.frequency_measurable.neg,
    fun a => conj (M.amplitude a), M.amplitude_integrable.norm.mono'
      (Complex.continuous_conj.comp_aestronglyMeasurable M.amplitude_integrable.aestronglyMeasurable)
      (ae_of_all _ fun a => by simp)⟩, ?_, fun y => ?_⟩
  · refine le_of_eq_of_le ?_ hM
    unfold Flower.IncTop.starMoment Flower.IncTop.starRootFrequency
    refine lintegral_congr fun a => ?_
    simp only [WithLp.ofLp_neg, Pi.neg_apply, Finset.sum_neg_distrib, norm_neg, RCLike.enorm_conj]
  · show _ = conj (ω y)
    rw [← hv y]
    unfold Cut2A.SpatialMeasure.value
    rw [← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    simp only [inner_neg_left, map_mul]
    congr 1
    rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

/-! ### The gate in both orientations -/

/-- **FILT-COH for a coherent couple in either orientation of its parent layers.** -/
theorem tc_coh_any {P : WTParams} (hFC : FiltCoherentBoundAt P) {p : ℕ} (hp : p < P.D) {n : ℕ}
    (hn : n ≤ P.N (p + 1) ^ 4) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) (Q : RegCpl) (LG : LayeredGarden 2)
    {q q' : ℕ} (hq : q ≤ p) (hq' : q' ≤ p) (hsz : Q.size = 2 * n) (hc : IsCoherentCoupleAt p q q' Q LG)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
    (M : GBranch LG.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B) :
    XNormRestr θ (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
      (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG H (fun b => if b.1.1 = 0 then ts 0 else ts 1)
        0 k (fun _ => 0) 0 (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F ann M κ *
          filtWeight Fu (fun _ => false) Mu κ)) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * regBound P n 0 * ENNReal.ofReal (leafSizeProduct LG B) := by
  rcases le_total q' q with hqq | hqq
  · exact (hFC p hp n hn θ hθ0 hθ1).1 Q LG q q' hqq hq hsz hc S ω cω hpres F ann M hM Fu Mu hMu H B hH
  -- the conjugate couple
  set LH := conjLayered LG (Equiv.swap (0 : Fin 2) 1) with hLH
  have h : IsConjugateCouple LG LH := conjLayered_isConjugateBy LG (Equiv.swap (0 : Fin 2) 1)
  set ν := nodeEquiv h with hν
  set β := branchEquiv h with hβ
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
  have key := (hFC p hp n hn θ hθ0 hθ1).1 (conjCpl Q) LH q' q hqq hq' ((size_conjCpl Q).trans hsz)
    (isCoherentCoupleAt_conj h hc) (S.map ν.toEmbedding) (fun a y => conj (ω (ν.symm a) y))
    (fun a => cω (ν.symm a)) hpres' (F.map β.toEmbedding) (fun b => ann (β.symm b)) (fun b => M (β.symm b)) hM'
    (Fu.map β.toEmbedding) (fun b => Mu (β.symm b)) hMu' (transferProf h H) (transferProf h B)
    (leafwiseControlled_conj h hH)
  have hfun : (fun (ts : Fin 2 → ℝ) (k : Mom P.d) => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG H
      (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0 (fun κ => Flower.IncTop.starWeight S ω κ *
        filtWeight F ann M κ * filtWeight Fu (fun _ => false) Mu κ)) =
      swapConj (Equiv.swap (0 : Fin 2) 1) (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LH
        (transferProf h H) (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0
        (fun κ => Flower.IncTop.starWeight (S.map ν.toEmbedding) (fun a y => conj (ω (ν.symm a) y)) κ *
          filtWeight (F.map β.toEmbedding) (fun b => ann (β.symm b)) (fun b => M (β.symm b)) κ *
          filtWeight (Fu.map β.toEmbedding) (fun _ => false) (fun b => Mu (β.symm b)) κ)) := by
    funext ts k
    simp only [swapConj, permT, Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [tc_coupleW_conj h P.L P.γ P.δ H (ts 0) (ts 1) k _ _ (fun K => ?_), Complex.conj_conj]
    have hFu := tc_filtWeight_conj h Fu (fun _ => false) Mu K
    rw [tc_starWeight_conj h S ω K, tc_filtWeight_conj h F ann M K, hFu, map_mul, map_mul,
      tc_conj_filtWeight, tc_conj_filtWeight]
  rw [hfun, XNormRestr_swapConj swap_invol, timeBox_permT]
  refine (le_of_eq (by norm_cast)).trans (key.trans (le_of_eq ?_))
  rw [Finset.prod_map, leafSizeProduct_conj h B]
  simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]

end WaveTurbulence.Flower.ProtPin
