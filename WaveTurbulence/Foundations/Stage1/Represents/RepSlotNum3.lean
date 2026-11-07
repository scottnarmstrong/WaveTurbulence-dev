/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepSlotNum2
import Mathlib.Tactic

/-!
# S2 REPRESENTS: tree slots in the target normalisation
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.PL2330 Set
open scoped ENNReal

theorem incoherency_nil (LG : LayeredGarden 1) (ζ : ℤˣ) : LG.incoherency (RegChain.nil.treeLinks ζ) = 0 := by
  unfold LayeredGarden.incoherency
  simp [RegChain.treeLinks, RegChain.linksAt]

/-- The explicit slot constant for trees (depends only on `d` and `η`). -/
noncomputable def Ktr (d : ℕ) (η : ℝ) : ℝ :=
  max (max ((supTreeC d η).toReal) (2 * (supTreeC d η).toReal)) 1

theorem tree_slot_target (P : WTParams) (E : GateEnv P) :
    ∃ K : ℝ, 1 ≤ K ∧ K = Ktr P.d P.η ∧ ∀ C : ℝ, 2 * P.C₁ ^ 2 * (1 + cLeib P.d (30 * P.d)) ≤ C →
      ∀ (p n : ℕ), p < P.D → n ≤ P.N (p + 1) ^ 4 → ∀ (X : RegChain), X.wf = true → X.size = 2 * n →
      ∀ (LG : LayeredGarden 1), X.DecodesTree LG.garden →
      (∀ b, ¬ LG.garden.IsFlowerParent b) →
      (∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1) →
      (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q' ≤ q → q ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q →
      (∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') →
      (X = RegChain.nil ∨ (1 ≤ n ∧ (1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) ∨
        (LG.incoherency (X.treeLinks (LG.garden.sig 0)) = 0 ∧ IsCoherentTreeAt p q q' X LG)))) →
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      Sup (30 * P.d) (timeBoxGt (q : ℝ) q')
        (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k)
        (ENNReal.ofReal (K * (C * Real.sqrt P.δ) ^ (X.size) *
          P.L ^ (-(P.η ^ 8) * (LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℝ)) *
          leafSizeProduct LG B)) := by
  obtain ⟨Ci, hCi, hCie, hinc⟩ := tree_slot_incoh P E.hd1 E.hL1 E.hη0 E.hinc
  obtain ⟨Ch, hCh, hChe, hcoh⟩ := tree_slot_coh P E.hd1 E.hL1 E.hη0 E.hη (by linarith [E.hC1]) E.hδ0 E.hcoh
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one E.hL1
  refine ⟨max (max (Ci.toReal) (2 * Ch.toReal)) 1, le_max_right _ _,
    by rw [Ktr, hCie, hChe],
    fun C hC p n hp hn X hwf hsz LG hdec hnf hlo hlay q q' hqq' hqp hr0 hlone hcase H B hctrl => ?_⟩
  set K : ℝ := max (max (Ci.toReal) (2 * Ch.toReal)) 1 with hK
  have hcost : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hcL : 0 ≤ cLeib P.d (30 * P.d) := cLeib_nonneg _ _
  have hCc : P.C₁ ≤ C := by nlinarith [E.hC1]
  have hLpos : 0 ≤ P.L ^ (-(P.η ^ 8) * (LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℝ)) :=
    Real.rpow_nonneg hL0.le _
  have hx : 0 ≤ (C * Real.sqrt P.δ) ^ (X.size) :=
    pow_nonneg (mul_nonneg (by nlinarith [E.hC1]) (Real.sqrt_nonneg _)) _
  rcases hcase with rfl | ⟨hn1, hcase⟩
  · have h := tree_slot_nil (d := P.d) (timeBoxGt (q : ℝ) q') P.L P.γ P.δ LG hdec H B
    refine h.mono (ENNReal.ofReal_le_ofReal ?_)
    have hs0 : RegChain.nil.size = 0 := rfl
    rw [hs0, incoherency_nil]
    simp only [pow_zero, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    exact le_mul_of_one_le_left hcost (le_max_right _ _)
  · rcases hcase with hg | ⟨hg, hQc⟩
    · have h := hinc p n hp hn X hwf hsz LG hdec hnf hlo hlay q q' hqq' hqp hr0 hlone hg H B hctrl
      refine h.mono ?_
      have hC0 : 0 ≤ P.C₁ := by linarith [E.hC1]
      have hreg0 : 0 ≤ P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) *
          (LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℝ)) := by
        have := E.hδ0
        positivity
      rw [regBound_eq, ← ENNReal.ofReal_mul hreg0, enn_mul_ofReal hCi _ (mul_nonneg hreg0 hcost)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hb := regBound_le_target P C n (LG.incoherency (X.treeLinks (LG.garden.sig 0))) hn1 E.hC1 hCc E.hδ0
        E.hL1 E.hκ
      rw [hsz]
      have hCiK : Ci.toReal ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
      have hpos : 0 ≤ (C * Real.sqrt P.δ) ^ (2 * n) *
          P.L ^ (-(P.η ^ 8) * (LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℝ)) :=
        mul_nonneg (by rw [← hsz]; exact hx) hLpos
      calc Ci.toReal * (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) *
            (LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℝ)) * leafSizeProduct LG B)
          ≤ Ci.toReal * ((C * Real.sqrt P.δ) ^ (2 * n) *
            P.L ^ (-(P.η ^ 8) * (LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℝ)) * leafSizeProduct LG B) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb hcost) ENNReal.toReal_nonneg
        _ ≤ K * ((C * Real.sqrt P.δ) ^ (2 * n) *
            P.L ^ (-(P.η ^ 8) * (LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℝ)) * leafSizeProduct LG B) :=
            mul_le_mul_of_nonneg_right hCiK (mul_nonneg hpos hcost)
        _ = _ := by ring
    · have h := hcoh p n hp hn X LG q q' hqq' hqp hsz hQc hnf hlo H B hctrl
      refine h.mono ?_
      have hC0 : 0 ≤ P.C₁ := by linarith [E.hC1]
      have hreg0 : 0 ≤ P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ)) := by
        have := E.hδ0
        positivity
      have hsep0 : 0 ≤ 2 ^ n * (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n * leafSizeProduct LG B)) *
          (P.C₁ * P.C₁ ^ n)) := by
        have := E.hδ0
        positivity
      have hsepEq : sepMass P n (leafSizeProduct LG B) = ENNReal.ofReal (2 ^ n * (cLeib P.d (30 * P.d) *
          (P.δ ^ n * (P.C₁ * P.C₁ ^ n * leafSizeProduct LG B)) * (P.C₁ * P.C₁ ^ n))) := rfl
      rw [regBound_eq, ← ENNReal.ofReal_mul hreg0, hsepEq, ← ENNReal.ofReal_add (mul_nonneg hreg0 hcost) hsep0,
        enn_mul_ofReal hCh _ (add_nonneg (mul_nonneg hreg0 hcost) hsep0)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hg, hsz]
      simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
      have hb := regBound_le_target P C n 1 hn1 E.hC1 hCc E.hδ0 E.hL1 E.hκ
      have hL1' : P.L ^ (-(P.η ^ 8) * ((1 : ℕ) : ℝ)) ≤ 1 := by
        apply Real.rpow_le_one_of_one_le_of_nonpos E.hL1
        have : 0 ≤ P.η ^ 8 := by have := E.hη0; positivity
        simp; linarith
      have hxx : 0 ≤ (C * Real.sqrt P.δ) ^ (2 * n) := by rw [← hsz]; exact hx
      have hreg1 : P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ)) ≤
          (C * Real.sqrt P.δ) ^ (2 * n) := by
        refine hb.trans ?_
        calc _ ≤ (C * Real.sqrt P.δ) ^ (2 * n) * 1 := mul_le_mul_of_nonneg_left hL1' hxx
          _ = _ := mul_one _
      have hsep := sep_le_target P.C₁ P.δ (cLeib P.d (30 * P.d)) C (leafSizeProduct LG B) n hn1 E.hC1 E.hδ0 hcL
        hcost hC
      have hChK : 2 * Ch.toReal ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
      calc Ch.toReal * (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ)) *
            leafSizeProduct LG B + 2 ^ n * (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n *
              leafSizeProduct LG B)) * (P.C₁ * P.C₁ ^ n)))
          ≤ Ch.toReal * ((C * Real.sqrt P.δ) ^ (2 * n) * leafSizeProduct LG B +
              (C * Real.sqrt P.δ) ^ (2 * n) * leafSizeProduct LG B) := by
            refine mul_le_mul_of_nonneg_left (add_le_add ?_ hsep) ENNReal.toReal_nonneg
            exact mul_le_mul_of_nonneg_right hreg1 hcost
        _ = (2 * Ch.toReal) * ((C * Real.sqrt P.δ) ^ (2 * n) * leafSizeProduct LG B) := by ring
        _ ≤ K * ((C * Real.sqrt P.δ) ^ (2 * n) * leafSizeProduct LG B) :=
            mul_le_mul_of_nonneg_right hChK (mul_nonneg hxx hcost)
        _ = _ := by ring

end WaveTurbulence.Represents
