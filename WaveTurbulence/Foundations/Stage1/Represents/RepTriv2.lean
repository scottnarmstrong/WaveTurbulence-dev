/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.LeafwiseKernel
public import WaveTurbulence.Foundations.Molecule.GardenNodeCounts
public import WaveTurbulence.Foundations.RegStruct.CodeOrders
public import WaveTurbulence.Foundations.Spine.LeafwiseCoherentApp
public import WaveTurbulence.Foundations.RegStruct.DecodedCouple
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the kernel of a garden of order zero (trivial couples and trees)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Mole TTree MeasureTheory

variable {w d : ℕ}

theorem isEmpty_gbranch_of_order_zero (G : Garden w) (h : G.order = 0) : IsEmpty (GBranch G.tree) := by
  have := Mole.card_gbranch G.tree
  have h0 : Fintype.card (GBranch G.tree) = 0 := by
    rw [this]; exact h
  exact Fintype.card_eq_zero_iff.1 h0

theorem node_eq_root_of_order_zero (G : Garden w) (h : G.order = 0) (a : GNode G.tree) :
    a = GNode.root G.tree a.1.1 := by
  have hE := isEmpty_gbranch_of_order_zero G h
  by_contra hne
  have ha : a.1.2 ≠ [] := fun he => hne (Subtype.ext (Prod.ext rfl he))
  exact hE.false (GNode.parent a ha)

open scoped Classical in
theorem kernelLeaves_order_zero (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (h : LG.garden.order = 0) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) :
    kernelLeaves L γ δ LG H up s k₀ (fun _ => 0) 0 =
      ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 k₀ : ℂ) := by
  have hE := isEmpty_gbranch_of_order_zero LG.garden h
  have hz : LG.garden.zeta = 1 := by
    unfold Garden.zeta
    exact Finset.prod_eq_one fun b _ => hE.elim b
  have hdec : IsDecoration LG.garden (fun _ : GNode LG.garden.tree => (0 : Fin d → ℤ)) :=
    ⟨fun b => hE.elim b, fun _ => rfl⟩
  let κ0 : GenDecoration LG.garden d (fun _ => 0) 0 := ⟨fun _ => 0, hdec, fun _ => rfl, fun _ _ => rfl⟩
  have hu : ∀ κ : GenDecoration LG.garden d (fun _ => 0) 0, κ = κ0 := by
    intro κ
    apply Subtype.ext
    funext a
    rw [node_eq_root_of_order_zero LG.garden h a]
    exact κ.2.2.1 a.1.1
  unfold kernelLeaves
  rw [tsum_eq_single κ0 (fun κ hκ => absurd (hu κ) hκ), hz, h]
  have hFree : IsEmpty LG.garden.FreeBranch := ⟨fun b => hE.elim b.1⟩
  have hint : phaseIntegral L γ δ LG.garden (kDomain LG up s) s
      (cosetDecoration LG.garden L k₀ κ0.1) = 1 := by
    unfold phaseIntegral
    rw [Measure.volume_pi_eq_dirac, integral_dirac]
    have hmem : LG.garden.extendTime s isEmptyElim ∈ kDomain LG up s := fun b => hE.elim b
    rw [Set.indicator_of_mem hmem]
    exact Finset.prod_eq_one fun b _ => hE.elim b
  have heps : epsDec LG.garden κ0.1 = 1 := by
    unfold epsDec; exact Finset.prod_eq_one fun b _ => hE.elim b
  simp only [pow_zero, one_mul, hint, heps, Complex.ofReal_one]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  have h0 : latticePoint L ((0 : Fin d → ℤ)) = (0 : Mom d) := by
    ext j; simp [latticePoint]
  simp [cosetDecoration, κ0, h0]

open scoped Classical in
theorem coupleLeaves_triv {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 2) (H : LeafProfiles 2 d)
    (hQ : RegCpl.triv.Decodes LG.garden) (t s : ℝ) (k : Mom d) :
    ∃ ℓ0 : GLeaf LG.garden.tree, ℓ0.1 = (0, []) ∧ inputLeaves LG.garden = {ℓ0} ∧
      coupleLeaves L γ δ LG H t s k = (H ℓ0.1 k : ℂ) := by
  have hord : LG.garden.order = 0 := Reg.size_eq_order hQ
  have hplain : LG.garden.IsPlain := hQ.1.1
  have hsig : LG.garden.sig = ![1, -1] := hQ.1.2
  have ht0 : LG.garden.tree 0 = TTree.leaf := hQ.2.1
  have ht1 : LG.garden.tree 1 = TTree.leaf := hQ.2.2.1
  have htree : ∀ j : Fin 2, LG.garden.tree j = TTree.leaf := by
    intro j; fin_cases j
    exacts [ht0, ht1]
  have hpath : ∀ ℓ : GLeaf LG.garden.tree, ℓ.1.2 = [] := by
    rintro ⟨⟨j, p⟩, hp⟩
    have hp' : p ∈ (LG.garden.tree j).leaves := hp
    rw [htree j] at hp'
    simpa [TTree.leaves] using hp'
  let ℓ0 : GLeaf LG.garden.tree := ⟨(0, []), by
    show ([] : TTree.Path) ∈ (LG.garden.tree 0).leaves
    rw [ht0]; simp [TTree.leaves]⟩
  have hsign : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.sign ℓ.toNode = LG.garden.sig ℓ.1.1 := by
    intro ℓ
    simp only [Garden.sign, GLeaf.toNode, nodeSign, TTree.pathSign, hpath ℓ, List.count_nil, pow_zero, mul_one]
  have hin : inputLeaves LG.garden = {ℓ0} := by
    ext ℓ
    simp only [inputLeaves, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, -⟩
      rw [hsign] at h1
      have hj : ℓ.1.1 = 0 := by
        rcases Fin.exists_fin_two.1 ⟨ℓ.1.1, rfl⟩ with h | h
        · exact h
        · rw [h, hsig] at h1
          exfalso
          revert h1; decide
      exact Subtype.ext (Prod.ext hj (hpath ℓ))
    · rintro rfl
      refine ⟨?_, hplain _⟩
      rw [hsign, hsig]; rfl
  refine ⟨ℓ0, rfl, hin, ?_⟩
  unfold coupleLeaves
  rw [kernelLeaves_order_zero L γ δ LG H hord _ _ k, hin, Finset.prod_singleton]

open scoped Classical in
theorem treeLeaves_nil {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d)
    (hX : RegChain.nil.DecodesTree LG.garden) (t s : ℝ) (k : Mom d) :
    inputLeaves LG.garden = ∅ ∧ treeLeaves L γ δ LG H t s k = 1 := by
  obtain ⟨ht, hmark, -⟩ := hX
  have ht' : LG.garden.tree 0 = TTree.leaf := ht
  have htree : ∀ j : Fin 1, LG.garden.tree j = TTree.leaf := by
    intro j; fin_cases j; exact ht'
  have hord : LG.garden.order = 0 := by
    simp [Garden.order, htree, TTree.order]
  have hpath : ∀ ℓ : GLeaf LG.garden.tree, ℓ.1.2 = [] := by
    rintro ⟨⟨j, p⟩, hp⟩
    have hp' : p ∈ (LG.garden.tree j).leaves := hp
    rw [htree j] at hp'
    simpa [TTree.leaves] using hp'
  have hin : inputLeaves LG.garden = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro ℓ hℓ
    simp only [inputLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    have := hmark ℓ
    rw [hℓ.2] at this
    have hl : ℓ.1.2 = RegChain.nil.lonePath := by rw [hpath ℓ]; rfl
    rw [if_pos hl] at this
    exact absurd this (by simp)
  refine ⟨hin, ?_⟩
  unfold treeLeaves
  rw [kernelLeaves_order_zero L γ δ LG H hord _ _ k, hin, Finset.prod_empty]

end WaveTurbulence.Represents
