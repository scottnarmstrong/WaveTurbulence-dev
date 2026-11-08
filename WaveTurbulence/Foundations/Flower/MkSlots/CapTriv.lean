/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.CapGeoQ

/-! # B3s MK-SLOTS (cap slots): the trivial cap couple

When the native couple of a cap pair has two leaf trees (the capped flower is the skeleton leaf itself, its parent
a core branch), the native kernel has no time integral: its value does not depend on the slot clocks, the pins or
the lower time (`kernelNodeWF_noBranch`), and it is bounded by `1` (`norm_kernelNodeWF_noBranch_le`: unit
multiplier, anchored indicator profiles). Its size and incoherency vanish and its leaf size is at least `b`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open MeasureTheory
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine

namespace WaveTurbulence.Flower.MkSlots

section General

variable {w d : ℕ}

theorem isEmpty_branch_of_leaves {T : Fin w → TTree} (hT : ∀ j, T j = .leaf) : IsEmpty (GBranch T) := by
  refine ⟨fun b => ?_⟩
  have h := b.2
  rw [hT b.1.1] at h
  simp [TTree.branching] at h

theorem node_root_of_leaves {T : Fin w → TTree} (hT : ∀ j, T j = .leaf) (a : GNode T) :
    a = GNode.root T a.1.1 := by
  have h := a.2
  rw [hT a.1.1] at h
  simp only [TTree.nodes, Finset.mem_singleton] at h
  exact Subtype.ext (Prod.ext rfl h)

theorem genDecoration_subsingleton (G : Garden w) (hT : ∀ j, G.tree j = .leaf) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) : Subsingleton (GenDecoration G d nroot nfl) := by
  refine ⟨fun κ κ' => Subtype.ext (funext fun a => ?_)⟩
  rw [node_root_of_leaves hT a, κ.2.2.1, κ'.2.2.1]

theorem integral_noBranch (L γ δ : ℝ) (LG : LayeredGarden w) (hT : ∀ j, LG.garden.tree j = .leaf)
    (K : GNode LG.garden.tree → Mom d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) :
    ∫ τ, (kDomain LG up s).indicator (phaseProd L γ δ LG.garden K) τ ∂(fixMeasure fix) = 1 := by
  have := isEmpty_branch_of_leaves hT
  have h1 : ∀ τ, (kDomain LG up s).indicator (phaseProd L γ δ LG.garden K) τ = 1 := by
    intro τ
    have hm : τ ∈ kDomain LG up s := fun b => isEmptyElim b
    rw [Set.indicator_of_mem hm]
    unfold phaseProd
    exact Finset.prod_of_isEmpty _
  simp only [h1, integral_const]
  rw [Measure.real, fixMeasure, Measure.pi_univ, Finset.prod_of_isEmpty]
  simp

/-- The no-branch kernel in closed form. -/
def kerNoBranch (L γ δ : ℝ) (LG : LayeredGarden w) (A : GNode LG.garden.tree → Mom d → ℝ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      m (cosetDecoration LG.garden L k₀ κ.1) *
        ((epsDec LG.garden κ.1 : ℂ) * 1 *
          ∏ ℓ ∈ inputLeaves LG.garden, (A ℓ.toNode (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ))

/-- **The no-branch kernel does not see its times or pins.** -/
theorem kernelNodeWF_noBranch (L γ δ : ℝ) (LG : LayeredGarden w) (hT : ∀ j, LG.garden.tree j = .leaf)
    (A : GNode LG.garden.tree → Mom d → ℝ) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (fix : GBranch LG.garden.tree → Option ℝ) :
    kernelNodeWF L γ δ LG A m up s k₀ nroot nfl fix = kerNoBranch L γ δ LG A m k₀ nroot nfl := by
  unfold kernelNodeWF kerNoBranch
  congr 1
  refine tsum_congr fun κ => ?_
  rw [integral_noBranch L γ δ LG hT]

theorem norm_kerNoBranch_le (L γ δ : ℝ) (LG : LayeredGarden w) (hT : ∀ j, LG.garden.tree j = .leaf)
    (A : GNode LG.garden.tree → Mom d → ℝ) (m : (GNode LG.garden.tree → Mom d) → ℂ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (hm : ∀ k, ‖m k‖ ≤ 1)
    (hA : ∀ ℓ ∈ inputLeaves LG.garden, ∀ x, |A ℓ.toNode x| ≤ 1) :
    ‖kerNoBranch L γ δ LG A m k₀ nroot nfl‖ ≤ 1 := by
  have := isEmpty_branch_of_leaves hT
  have := genDecoration_subsingleton LG.garden hT nroot nfl
  have hord : LG.garden.order = 0 := by
    unfold Garden.order
    exact Finset.sum_eq_zero fun j _ => by rw [hT j]; rfl
  have hz : LG.garden.zeta = 1 := by unfold Garden.zeta; exact Finset.prod_of_isEmpty _
  unfold kerNoBranch
  rw [hord, hz, pow_zero, one_mul, one_mul]
  rcases isEmpty_or_nonempty (GenDecoration LG.garden d nroot nfl) with he | hne
  · rw [tsum_empty, norm_zero]; exact zero_le_one
  · obtain ⟨κ₀⟩ := hne
    rw [tsum_eq_single κ₀ (fun κ hκ => (hκ (Subsingleton.elim _ _)).elim)]
    have he : epsDec LG.garden κ₀.1 = 1 := by unfold epsDec; exact Finset.prod_of_isEmpty _
    rw [he, Complex.ofReal_one, one_mul, one_mul, norm_mul, norm_prod]
    refine mul_le_one₀ (hm _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun ℓ hℓ => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hA ℓ hℓ _

end General

/-! ### The trivial cap couple of a reconstruction -/

section Triv

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (q : SourcePair S)

theorem triv_trees (ht : (D.couple q).trees.1 = .leaf ∧ (D.couple q).trees.2 = .leaf) (j : Fin 2) :
    (nativeCoupleLayered D hS layer hLayer q).garden.tree j = .leaf := by
  rw [nativeCoupleLayered_garden]
  have hdec := decodedCouple_decodes (D.couple q)
  fin_cases j
  · exact hdec.2.1.trans ht.1
  · exact hdec.2.2.1.trans ht.2

theorem triv_size (ht : (D.couple q).trees.1 = .leaf ∧ (D.couple q).trees.2 = .leaf) :
    Represents.slotSize D (.inl q) = 0 := by
  show (D.couple q).size = 0
  rw [← decodedCouple_order]
  unfold Garden.order
  have hdec := decodedCouple_decodes (D.couple q)
  rw [Fin.sum_univ_two, hdec.2.1, hdec.2.2.1, ht.1, ht.2]
  rfl

theorem triv_incoh (ht : (D.couple q).trees.1 = .leaf ∧ (D.couple q).trees.2 = .leaf) :
    Represents.slotIncoh D hS layer hLayer (.inl q) = 0 := by
  have := isEmpty_branch_of_leaves (triv_trees D hS layer hLayer q ht)
  show ((Finset.univ : Finset (GBranch (nativeCoupleLayered D hS layer hLayer q).garden.tree ×
    GBranch (nativeCoupleLayered D hS layer hLayer q).garden.tree)).filter _).card = 0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x
  exact isEmptyElim x.1

theorem triv_leaf (ht : (D.couple q).trees.1 = .leaf ∧ (D.couple q).trees.2 = .leaf) (b : ℝ) (hb : 1 ≤ b) :
    1 ≤ b⁻¹ * Represents.slotLeaf D hS layer hLayer (fun _ => b.toNNReal) (.inl q) := by
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  set LGq := nativeCoupleLayered D hS layer hLayer q
  have hSL : Represents.slotLeaf D hS layer hLayer (fun _ => b.toNNReal) (.inl q) =
      b ^ (inputLeaves LGq.garden).card := by
    show leafSizeProduct LGq (Represents.nativeCoupleB D hS (fun _ => b.toNNReal) q) = _
    unfold leafSizeProduct
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    have hn : ℓ.1.2 ∈ ((nativeCoupleGarden D hS q).tree ℓ.1.1).nodes := ℓ.toNode.2
    simp only [Represents.nativeCoupleB, hn, ↓reduceDIte, Real.coe_toNNReal b hb0]
  have hpos : 0 < (inputLeaves LGq.garden).card := by
    refine Finset.card_pos.2 ?_
    have hleaf : ([] : Path) ∈ (LGq.garden.tree 0).leaves := by
      rw [triv_trees D hS layer hLayer q ht 0]; simp [TTree.leaves]
    have hsig : LGq.garden.sig = ![1, -1] := by
      rw [nativeCoupleLayered_garden]; exact (decodedCouple_decodes _).1.2
    refine ⟨⟨((0 : Fin 2), []), hleaf⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩⟩
    · show nodeSign LGq.garden.sig ((0 : Fin 2), ([] : Path)) = 1
      rw [hsig]; rfl
    · have hpl : LGq.garden.IsPlain := by
        rw [nativeCoupleLayered_garden]; exact (decodedCouple_decodes _).1.1
      exact hpl _
  rw [hSL]
  have h1 : b ≤ b ^ (inputLeaves LGq.garden).card := by
    calc b = b ^ 1 := (pow_one b).symm
      _ ≤ _ := pow_le_pow_right₀ hb hpos
  rw [le_inv_mul_iff₀ (lt_of_lt_of_le one_pos hb), mul_one]
  exact h1

end Triv

end WaveTurbulence.Flower.MkSlots
