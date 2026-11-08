/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.CapFam

/-! # B3s-HELPER8 / CAP: a trivial cap slot

On a trivial cap couple (both native trees single leaves) every native node is a leaf of the reconstruction
(`triv_not_branching`), so the per-slot factor `genΘs` is `1` and no selected vertex is native (`triv_selNative`).
The general slot kernel is the constant no-branch kernel (`genSlotKer_triv`, B3s's `kernelNodeWF_noBranch`), of
modulus at most `1`; the slot mass is at least `1` (`one_le_genSlotMass_triv`): **`capT_concl`**, with one mode
`m = 0` (any moment weight). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Set
open WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Links
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsB WaveTurbulence.Flower.MkSlotsI

namespace WaveTurbulence.Flower.MkSlotsO

namespace CapT

section Triv

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (q : SourcePair S)
  (ht : (D.couple q).trees.1 = .leaf ∧ (D.couple q).trees.2 = .leaf)

include ht in
/-- On a trivial cap couple no native node is a branching node of the reconstruction. -/
theorem triv_not_branching (z : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree) :
    ((nativeCoupleForest D hS q).nodeEmbedding z).1.2 ∉
      ((D.garden hS).tree ((nativeCoupleForest D hS q).nodeEmbedding z).1.1).branching := by
  have hT := triv_trees D hS layer hLayer q ht
  have hE := capCouple_emb D hS q
  rw [node_root_of_leaves hT z]
  have hj : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  rcases hj z.1.1 with h0 | h1
  · rw [h0]
    have e0 : ((nativeCoupleForest D hS q).nodeEmbedding
        (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree 0)).1 = addrExt (capUA D hS q) [] := rfl
    rw [e0]
    intro hb
    have := ((node_iff_of_subtree hE.nodeA hE.treeA []).2.2).1 hb
    rw [ht.1] at this
    simp [TTree.branching] at this
  · rw [h1]
    have e1 : ((nativeCoupleForest D hS q).nodeEmbedding
        (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree 1)).1 = addrExt (capUB D hS q) [] := rfl
    rw [e1]
    intro hb
    have := ((node_iff_of_subtree hE.nodeB hE.treeB []).2.2).1 hb
    rw [ht.2] at this
    simp [TTree.branching] at this

include ht in
theorem triv_capΘ {d : ℕ} (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (k' : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree → Mom d) :
    CapK.capΘ layer hLayer (q := q) (J := J) L σ kSel Rs k' = 1 := by
  unfold CapK.capΘ
  refine Finset.prod_eq_one fun z _ => ?_
  split_ifs
  · rfl
  · unfold genNW
    exact dite_eq_right_of_eq_false (eq_false (triv_not_branching D hS layer hLayer q ht z))

include ht in
theorem triv_selNative (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) :
    MkSlotsS.selNative D hS layer hLayer J kSel (.inl q) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
  obtain ⟨-, a, -, hva⟩ := Finset.mem_filter.1 hv
  have hb := v.2
  have hva' : v.1 = ((nativeCoupleForest D hS q).nodeEmbedding a).1 := hva
  rw [hva'] at hb
  exact triv_not_branching D hS layer hLayer q ht a hb

end Triv

section Slot

variable {P : WTParams} (hL : 2 ≤ P.L) (hd : 3 ≤ P.d)
  (C : ℝ) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
  (pat : Fin (2 * R) → FixPat) (t s : ℝ) (hGeo : CapGeo (recLG a) J p)
  (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb1 : 1 ≤ b)
  (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) {q : SourcePair a.prime.skeleton}
  (hq : IsCapPair a.prime.skeleton a.prime.prime.1 J q)
  (ht : (a.prime.data.couple q).trees.1 = .leaf ∧ (a.prime.data.couple q).trees.2 = .leaf) (x : Fin P.d → ℤ)

/-- The constant value of the trivial cap slot kernel. -/
abbrev Vt : ℂ :=
  kerNoBranch P.L P.γ P.δ (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) q)
    (fun z => anchProfiles J (recLG a) h P.L roots ((nativeCoupleForest a.prime.data a.prime.prime.1 q).nodeEmbedding z).1)
    (fun k' => ∏ z, capNodeW P.L P.γ P.δ p s (recLG a) J Rf dag
      ((nativeCoupleForest a.prime.data a.prime.prime.1 q).nodeEmbedding z) (k' z))
    (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))) (fun _ => 0) 0

include hq ht in
/-- **The trivial cap slot kernel is constant.** -/
theorem genSlotKer_triv (ts : Fin 2 → ℝ) :
    genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inl q) ts
      (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))) =
    Vt (P := P) (p := p) (q := q) a J s roots h Rf dag := by
  have hT := triv_trees a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q ht
  have := isEmpty_branch_of_leaves hT
  have hW : (fun k' : GNode (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) q).garden.tree → Mom P.d =>
      ∏ z, chainW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) P.L P.γ P.δ p s J Rf dag
        ((nativeCoupleForest a.prime.data a.prime.prime.1 q).nodeEmbedding z) (k' z)) =
      fun k' => ∏ z, capNodeW P.L P.γ P.δ p s (recLG a) J Rf dag
        ((nativeCoupleForest a.prime.data a.prime.prime.1 q).nodeEmbedding z) (k' z) := by
    funext k'
    refine Finset.prod_congr rfl fun z _ => ?_
    have hin := IntGeo.inCapNative_nativeNodeAt a.prime.data a.prime.prime.1 J q hq z
    unfold chainW capNodeW
    simp only [show InCapNative a.prime.data a.prime.prime.1 J
      ((nativeCoupleForest a.prime.data a.prime.prime.1 q).nodeEmbedding z) from hin, ↓reduceIte]
  unfold genSlotKer
  dsimp only [slotFnGWFRL]
  rw [hW, CapK.genΘs_inl]
  refine (kernelNodeWR_fold P.L P.γ P.δ (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
    (sourceLayer_isLayering a) q) _ _ _ (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q)))
    _ _ _ _).trans ?_
  have hΘ : (fun k' : GNode (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) q).garden.tree → Mom P.d =>
      (∏ z, capNodeW P.L P.γ P.δ p s (recLG a) J Rf dag
        ((nativeCoupleForest a.prime.data a.prime.prime.1 q).nodeEmbedding z) (k' z)) *
        CapK.capΘ (sourceLayer a) (sourceLayer_isLayering a) (q := q) (J := J) P.L σ kSel Rs k') =
      fun k' => ∏ z, capNodeW P.L P.γ P.δ p s (recLG a) J Rf dag
        ((nativeCoupleForest a.prime.data a.prime.prime.1 q).nodeEmbedding z) (k' z) := by
    funext k'
    rw [triv_capΘ a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q ht, mul_one]
  rw [hΘ]
  refine (kernelNodeWR_one_eq P.L P.γ P.δ _ _ _ _ (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 _ (fun _ => 0) 0 _
    (fun τ _ => ?_)).trans ?_
  · simp only [kDomainR, kDomain, Set.mem_ofPred_eq, IsEmpty.forall_iff]
  · exact kernelNodeWF_noBranch _ _ _ _ hT _ _ _ _ _ _ _ _

include hGeo hq ht in
theorem norm_Vt_le : ‖Vt (P := P) (p := p) (q := q) a J s roots h Rf dag‖ ≤ 1 := by
  have hT := triv_trees a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q ht
  refine norm_kerNoBranch_le _ _ _ _ hT _ _ _ _ _ (fun k' => ?_) (fun ℓ _ y => ?_)
  · rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun z _ => norm_capNodeW_le _ _ _ _ _ _ _ _ _ _ _
  · rw [node_root_of_leaves hT ℓ.toNode]
    exact triv_anch_le a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J q hGeo.cap_leaf hq
      ht h P.L roots _ y

include hL hb1 hq ht in
theorem one_le_genSlotMass_triv :
    1 ≤ genSlotMass P C b a J pat t s kSel Rs (.inl q) := by
  have hL1 : 1 ≤ P.L := by linarith
  unfold genSlotMass
  rw [triv_size a.prime.data q ht, triv_incoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q ht,
    triv_selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q ht J kSel,
    Finset.prod_empty]
  simp only [pow_zero, Nat.cast_zero, mul_zero, Real.rpow_zero, one_mul, mul_one]
  have hcF : 1 ≤ frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1 (.inl q) :=
    one_le_pow₀ (one_le_frontierConst P.d)
  have hLSb := triv_leaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q ht b hb1
  have hleaf : genLeaf a J b (.inl q) = b⁻¹ * slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) (fun _ => b.toNNReal) (.inl q) := by
    unfold genLeaf; simp only [hq, ↓reduceIte]
  rw [hleaf]
  have hLe : 1 ≤ P.L ^ (if HasProtNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (protI (recLG a) J pat t s kSel) (.inl q) then genLossExp P.d else 0) := by
    split_ifs
    · exact Real.one_le_rpow hL1 (by unfold genLossExp; positivity)
    · rw [Real.rpow_zero]
  calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
    _ ≤ _ := by gcongr

include hL hd hGeo hb1 hq ht in
/-- **A trivial cap slot.** -/
theorem capT_concl :
    SlotConcl P C capKg (p := p) a J pat t s σ kSel Rs h roots Rf dag b (.inl q) x := by
  have hL1 : 1 ≤ P.L := by linarith
  have hV := norm_Vt_le a J s hGeo roots h Rf dag hq ht (P := P) (p := p)
  have hM := one_le_genSlotMass_triv hL C a J pat t s kSel Rs b hb1 hq ht
  have hK := capKcen_le_capKg P.d P.η
  have hK0 : 0 ≤ capKcen P.d := le_trans zero_le_one (one_le_capKcen P.d)
  have hmu : ENNReal.ofReal (capKcen P.d) * ‖Vt (P := P) (p := p) (q := q) a J s roots h Rf dag‖ₑ ≤
      ENNReal.ofReal (capKg P.d P.η * genSlotMass P C b a J pat t s kSel Rs (.inl q)) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_mul hK0]
    refine ENNReal.ofReal_le_ofReal ?_
    calc capKcen P.d * ‖Vt (P := P) (p := p) (q := q) a J s roots h Rf dag‖ ≤ capKcen P.d * 1 :=
          mul_le_mul_of_nonneg_left hV hK0
      _ ≤ capKg P.d P.η * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hM (by linarith)
  have hLq : 1 ≤ P.L ^ (47 * (P.d : ℝ) + 2) := Real.one_le_rpow hL1 (by positivity)
  have hm0 : 0 ≤ genSlotMass P C b a J pat t s kSel Rs (.inl q) := by linarith
  have hKg0 : 0 ≤ capKg P.d P.η := le_trans zero_le_one (one_le_capKg P.d P.η)
  refine slotConcl_of_fam1 P C capKg a J pat t s σ kSel Rs h roots Rf dag b (.inl q) x
    (fun _ => slotFam1_of_const P a J pat t s σ kSel Rs h roots Rf dag q x hq P.η _
      (fun ts _ => genSlotKer_triv a J pat t s σ kSel Rs roots h Rf dag hq ht ts) _ hmu)
    (fun _ => slotFam1_of_const P a J pat t s σ kSel Rs h roots Rf dag q x hq (1 / 4) _
      (fun ts _ => genSlotKer_triv a J pat t s σ kSel Rs roots h Rf dag hq ht ts) _ (hmu.trans ?_))
  refine ENNReal.ofReal_le_ofReal ?_
  calc capKg P.d P.η * genSlotMass P C b a J pat t s kSel Rs (.inl q)
      = capKg P.d P.η * 1 * genSlotMass P C b a J pat t s kSel Rs (.inl q) := by ring
    _ ≤ _ := by gcongr

end Slot

end CapT

end WaveTurbulence.Flower.MkSlotsO
