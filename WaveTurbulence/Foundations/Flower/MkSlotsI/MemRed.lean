/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.VBZ1
public import WaveTurbulence.Foundations.Flower.MkSlotsB.RLeavesL

/-! # B3s-HELPER7 (general assembly, M): the reduction of a reconstruction to a weighted skeleton value

Generic glue between β's relaxed pinned skeleton reduction (`MkSlotsB.kernelLeaves_skeleton_reduction_selNWFMRL`)
and the weighted VINE-B♯ (`MkSlotsI.hasSum_skelValWZRL_outerValMμD`):

* `kernelLeavesSelNWFMR_mul_ind`: a multiplier factor that is a constant times an indicator on coset decorations
  moves into the selection and in front (α's `kernelLeavesSelNWF_mul_ind` for β's kernel);
* `kernelLeavesSelNWFMR_congr_sel`: congruence in the selection;
* **`redSum_eq_skelValWZRL`**: β's reduced skeleton sum, with a core multiplier `Za κ · topW κ` (atom weight × the
  units' top weights), is the weighted skeleton value `skelValWZRL` with the weight `[sel κ] · Za κ` and the slot
  family `⟨F, tw⟩`;
* **`member_reduction_gen`**: the reconstruction's relaxed pinned leaf kernel with node weight `(∏ W) · r` (`r` a
  constant times a skeleton indicator on coset decorations) and a decoration multiplier factorized as
  `Θ (collapse κ) · ∏ s, Θs s (slotMom …) (restrict κ s)`, `Θ = Za · topW`, is `c · skelValWZRL` of the skeleton. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.Represents WaveTurbulence.VineB WaveTurbulence.RedSplice
open WaveTurbulence.Flower.MkSlots (fixMeasure fixCore)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW topW)
open WaveTurbulence.Flower.MkSlotsB

namespace WaveTurbulence.Flower.MkSlotsI

variable {w d : ℕ}

/-- **A constant times an indicator in the multiplier** (β's kernel form). -/
theorem kernelLeavesSelNWFMR_mul_ind (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel Q : GenDecoration LG.garden d nroot nfl → Prop) (m₀ r : (GNode LG.garden.tree → Mom d) → ℂ) (c : ℂ)
    (hr : ∀ κ : GenDecoration LG.garden d nroot nfl,
      r (cosetDecoration LG.garden L k₀ κ.1) = if Q κ then c else 0)
    (Θg : GenDecoration LG.garden d nroot nfl → ℂ) (fix : GBranch LG.garden.tree → Option ℝ) :
    kernelLeavesSelNWFMR L γ δ LG H up k₀ nroot nfl sel (fun k => m₀ k * r k) Θg fix =
      c * kernelLeavesSelNWFMR L γ δ LG H up k₀ nroot nfl (fun κ => sel κ ∧ Q κ) m₀ Θg fix := by
  unfold kernelLeavesSelNWFMR
  rw [mul_left_comm c]
  congr 1
  refine (tsum_congr fun κ => ?_).trans tsum_mul_left
  simp only [hr κ]
  by_cases hs : sel κ <;> by_cases hq : Q κ <;> simp [hs, hq]
  all_goals ring

/-- Congruence of β's kernel in the selection. -/
theorem kernelLeavesSelNWFMR_congr_sel (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel sel' : GenDecoration LG.garden d nroot nfl → Prop) (hs : ∀ κ, sel κ ↔ sel' κ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (Θg : GenDecoration LG.garden d nroot nfl → ℂ)
    (fix : GBranch LG.garden.tree → Option ℝ) :
    kernelLeavesSelNWFMR L γ δ LG H up k₀ nroot nfl sel m Θg fix =
      kernelLeavesSelNWFMR L γ δ LG H up k₀ nroot nfl sel' m Θg fix := by
  rw [show sel = sel' from funext fun κ => propext (hs κ)]

section Regroup

variable {S : Garden w} {J : Type} [Fintype J]

/-- **β's reduced skeleton sum is a weighted skeleton value.** If the core multiplier is the atom weight `Za κ`
times the units' top weights `topW … κ`, the reduced sum of β's reduction is `skelValWZRL` with the weight
`[sel κ] · Za κ` and the slot family `⟨F, tw⟩`. -/
theorem redSum_eq_skelValWZRL (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (k₀ : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (sel : GenDecoration S d roots 0 → Prop) (F : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ)
    (tw : GBranch S.tree → (Fin 4 → Mom d) → ℂ) (Za : GenDecoration S d roots 0 → ℂ)
    (fixS lbS : GBranch S.tree → Option ℝ) :
    (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
      ∑' κ : GenDecoration S d roots 0, (if sel κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
        ((coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomC lbS)).indicator
          (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ.1) τ *
            ((∏ s, F s (slotTs hS tt τ s) (k₀ + latticePoint L (κ.1 (slotNode hS s)))) *
              (Za κ * topW blk ⟨F, tw⟩ L k₀ κ.1))) τ ∂(fixMeasure fixS) else 0) =
    skelValWZRL blk D hS L γ δ k₀ roots tt layer (fun κ => if sel κ then Za κ else 0) ⟨F, tw⟩ fixS lbS := by
  unfold skelValWZRL skelValWZ
  congr 1
  refine tsum_congr fun κ => ?_
  unfold skelTermWZ
  by_cases hs : sel κ
  · simp only [hs, ite_true]
    have hI : (∫ τ : GBranch S.tree → ℝ,
        ((coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomC lbS)).indicator
          (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ.1) τ *
            ((∏ s, F s (slotTs hS tt τ s) (k₀ + latticePoint L (κ.1 (slotNode hS s)))) *
              (Za κ * topW blk ⟨F, tw⟩ L k₀ κ.1))) τ ∂(fixMeasure fixS)) =
        Za κ * ∫ τ : GBranch S.tree → ℝ,
          ((coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS)).indicator
            (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ.1) τ *
              ((∏ s, (⟨F, tw⟩ : SlotFamW S d).fs s (slotTs hS tt τ s) (k₀ + latticePoint L (κ.1 (slotNode hS s)))) *
                topW blk ⟨F, tw⟩ L k₀ κ.1)) τ ∂(fixMeasure fixS) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
      have hset : (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomC lbS) =
          (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS) := rfl
      dsimp only
      rw [hset]
      by_cases h : τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; ring
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; ring
    rw [hI]
    ring
  · simp [hs]

end Regroup

/-- The conjunction of two selections (a named predicate, so that its `if` uses the classical instance). -/
def selAnd {X : Type*} (A B : X → Prop) : X → Prop := fun x => A x ∧ B x

/-- **The reduction of a reconstruction to a weighted skeleton value.** -/
theorem member_reduction_gen {S : Garden w} {J : Type} [Fintype J] (blk : J → CLBlock S)
    (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d)
    (W : GNode (D.forest hS) → Mom d → ℂ) (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (roots : Fin w → (Fin d → ℤ))
    (hH : ∀ ℓ ∈ inputLeaves (D.garden hS), Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|)
    (selSk Q : GenDecoration S d roots 0 → Prop) (fixG : GBranch (D.forest hS) → Option ℝ)
    (lbC : GBranch S.tree → Option ℝ)
    (hP : RelaxPins layer tt fixG) (hLS : LbSound D hS fixG lbC) (hLC : LbComplete D hS fixG lbC)
    (r : (GNode (D.forest hS) → Mom d) → ℂ) (c : ℂ)
    (hr : ∀ κ : GenDecoration (D.garden hS) d roots 0,
      r (cosetDecoration (D.garden hS) L k₀ κ.1) = if Q (collapseGenDecoration D hS κ) then c else 0)
    (tw : GBranch S.tree → (Fin 4 → Mom d) → ℂ) (Za : GenDecoration S d roots 0 → ℂ) (CΘ : ℝ)
    (hΘ : ∀ κ, ‖Za κ * topW blk ⟨fun _ _ _ => 0, tw⟩ L k₀ κ.1‖ ≤ CΘ)
    (Θs : (s : ReplacementSlot S) → Mom d → NativeRelativeDecoration D hS d s → ℂ) (CΘs : ℝ)
    (hΘs : ∀ s k ρ, ‖Θs s k ρ‖ ≤ CΘs)
    (Θg : GenDecoration (D.garden hS) d roots 0 → ℂ)
    (hΘg : ∀ κ, Θg κ = (Za (collapseGenDecoration D hS κ) *
        topW blk ⟨fun _ _ _ => 0, tw⟩ L k₀ (collapseGenDecoration D hS κ).1) *
      ∏ s : ReplacementSlot S, Θs s (slotMom hS L k₀ (collapseGenDecoration D hS κ).1 s)
        (restrictRelativeDecorations D hS κ s)) :
    kernelLeavesSelNWFMR L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) k₀ roots 0
        (fun κ => selSk (collapseGenDecoration D hS κ)) (fun k => (∏ z, W z (k z)) * r k) Θg fixG =
      c * skelValWZRL blk D hS L γ δ k₀ roots tt layer (fun κ => if selAnd selSk Q κ then Za κ else 0)
        ⟨slotFnGWFRL D hS L γ δ H W Θs layer hLayer fixG, tw⟩ (fixCore D hS fixG) lbC := by
  have h1 := kernelLeavesSelNWFMR_mul_ind L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) k₀
    roots 0 (fun κ => selSk (collapseGenDecoration D hS κ)) (fun κ => Q (collapseGenDecoration D hS κ))
    (fun k => ∏ z, W z (k z)) r c hr Θg fixG
  refine h1.trans ?_
  congr 1
  have hΘg' : Θg = fun κ => (Za (collapseGenDecoration D hS κ) *
        topW blk ⟨fun _ _ _ => 0, tw⟩ L k₀ (collapseGenDecoration D hS κ).1) *
      ∏ s : ReplacementSlot S, Θs s (slotMom hS L k₀ (collapseGenDecoration D hS κ).1 s)
        (restrictRelativeDecorations D hS κ s) := funext hΘg
  subst hΘg'
  have hred := kernelLeaves_skeleton_reduction_selNWFMRL D hS L γ δ H W Cw hCw hW layer hLayer tt k₀ roots 0 hH
    (selAnd selSk Q) fixG lbC hP hLS hLC
    (fun κS => Za κS * topW blk ⟨fun _ _ _ => 0, tw⟩ L k₀ κS.1) CΘ hΘ Θs CΘs hΘs
  refine hred.trans ?_
  exact redSum_eq_skelValWZRL blk D hS L γ δ k₀ roots tt layer (selAnd selSk Q)
    (slotFnGWFRL D hS L γ δ H W Θs layer hLayer fixG) tw Za (fixCore D hS fixG) lbC

end WaveTurbulence.Flower.MkSlotsI
