/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepGate2M
public import WaveTurbulence.Foundations.Stage1.Represents.RepGate3
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-D (moments): tree slots from the leafwise gates, with the frequency moment

The moment-carrying versions of `tree_slot_incoh` / `tree_slot_coh` (RepGate3).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic Set
open scoped ENNReal

theorem tree_slot_incohM (P : WTParams) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (hη0 : 0 ≤ P.η)
    (hginc : LeafwiseIncoherentDecayAt P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ C = supTreeCM P.d P.η ∧ ∀ (p n : ℕ), p < P.D → n ≤ P.N (p + 1) ^ 4 →
      ∀ (X : RegChain), X.wf = true → X.size = 2 * n → ∀ (LG : LayeredGarden 1), X.DecodesTree LG.garden →
      (∀ b, ¬ LG.garden.IsFlowerParent b) →
      (∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1) →
      (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q' ≤ q → q ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q →
      (∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') →
      1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) →
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      SupM P.η (30 * P.d) (timeBoxGt (q : ℝ) q')
        (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k)
        (C * (regBound P n (LG.incoherency (X.treeLinks (LG.garden.sig 0))) *
          ENNReal.ofReal (leafSizeProduct LG B))) := by
  obtain ⟨C, hC, hCe, h⟩ := supM_tree P hd1 hη0
  refine ⟨C, hC, hCe, fun p n hp hn X hwf hsz LG hdec hnf hlo hlay q q' hqq' hqp hr0 hlone hi H B hctrl => ?_⟩
  refine h q q' _ _ (ENNReal.mul_ne_top (regBound_ne_top _ _ _) ENNReal.ofReal_ne_top) hqq' ?_ ?_
  · intro k
    exact continuous_treeLeaves_time P.L P.γ P.δ H LG hnf hlo k (hctrl.summable_coset hd1 hL1 k)
  · exact (hginc p hp n hn).2 X hwf hsz LG hdec hlay q q' hqq' hqp hr0 hlone hi H B hctrl

theorem tree_slot_cohM (P : WTParams) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη : P.η ≤ 1 / 2)
    (hC : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hgcoh : LeafwiseCoherentApproximationAt P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ C = supTreeCM P.d P.η ∧ ∀ (p n : ℕ), p < P.D → n ≤ P.N (p + 1) ^ 4 →
      ∀ (X : RegChain) (LG : LayeredGarden 1) (q q' : ℕ), q' ≤ q → q ≤ p → X.size = 2 * n →
      IsCoherentTreeAt p q q' X LG →
      (∀ b, ¬ LG.garden.IsFlowerParent b) →
      (∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1) →
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      SupM P.η (30 * P.d) (timeBoxGt (q : ℝ) q')
        (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k)
        (C * (regBound P n 1 * ENNReal.ofReal (leafSizeProduct LG B) +
          sepMass P n (leafSizeProduct LG B))) := by
  obtain ⟨C, hC0, hCe, h⟩ := supM_tree P hd1 hη0
  refine ⟨C, hC0, hCe, fun p n hp hn X LG q q' hqq' hqp hsz hcoh hnf hlo H B hctrl => ?_⟩
  obtain ⟨hXe, -, hsep⟩ := (hgcoh p hp n hn).2 X LG q q' hqq' hqp hsz hcoh H B hctrl
  have hcost : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hKc : ∀ k, Continuous fun ts : Fin 2 → ℝ => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k :=
    fun k => continuous_treeLeaves_time P.L P.γ P.δ H LG hnf hlo k (hctrl.summable_coset hd1 hL1 k)
  have hA : XNormRestr P.η (30 * P.d) 0 (timeBoxGt (q : ℝ) q') Set.univ
      (fun ts k => LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k) ≤
      sepMass P n (leafSizeProduct LG B) := by
    rw [PL2330.XNormRestr_eq_rN]
    exact rN_leafwiseSeparated_le hsep hd1 (by linarith) hC hδ hcost
  exact h q q' _ _ (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (regBound_ne_top _ _ _) ENNReal.ofReal_ne_top,
    ENNReal.ofReal_ne_top⟩) hqq' hKc (xnorm_add_split (by omega) _ _ hXe hA)

end WaveTurbulence.Represents
