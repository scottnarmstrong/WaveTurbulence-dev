/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH1
public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm3

/-!
# S2 REPRESENTS, VINE-D (2): on the support of an assembled slot mode, every node momentum is near its centre

`prod_ampS_split`: the bond product of the edge amplitudes times the constant amplitudes of the bond-free slots is the
product of all slot amplitudes at the decoration.  Hence (`node_near`) if the slot part `constW · E` of an assembled mode is
non-zero at the decoration `κ`, every node momentum `k_ν` lies in the unit ball around `latPt (nodeCen ξ ν)`: the unit-ball
restriction of TARGET L1959-L1961 that the vine factors need (VINEEST's `outSet` balls around `centre`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.FS

variable {w d : ℕ} {S : Garden w}

open scoped Classical in
theorem prod_ampS_split (fam : SlotFam S d) (hS : S.IsPlain) (Cχ L : ℝ) (base : Mom d)
    (roots : Fin w → Fin d → ℤ) (κ : GenDecoration S d roots 0) (ξ : XiT fam) :
    (∏ x ∈ S.molecule.bonds, edgeS fam hS Cχ ξ x (base + latticePoint L (bondIndex S κ.1 x))) *
      (∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => ¬ hasBond hS s),
        ampS fam Cχ ξ s (base + latticePoint L (kconstInt hS roots s))) =
      ∏ s, ampS fam Cχ ξ s (base + latticePoint L (κ.1 (slotNode hS s))) := by
  have hdec := κ.2.1
  have hz : ∀ ℓ : GLeaf S.tree, κ.1 ℓ.toNode = κ.1 (S.pair ℓ).toNode := hdec.2
  have hroot : ∀ j, κ.1 (GNode.root S.tree j) = roots j := κ.2.2.1
  set kk : ReplacementSlot S → Mom d := fun s => base + latticePoint L (κ.1 (slotNode hS s)) with hkk
  have hE : ∏ x ∈ S.molecule.bonds, edgeS fam hS Cχ ξ x (base + latticePoint L (bondIndex S κ.1 x)) =
      ∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (hasBond hS), ampS fam Cχ ξ s (kk s) := by
    rw [← prod_bonds_eq hS (fun s => ampS fam Cχ ξ s (kk s))]
    refine Finset.prod_congr rfl fun x _ => ?_
    unfold edgeS
    simp only [hkk]
    rw [bondIndex_eq_slotNode hS κ.1 hz x]
  have hN : ∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => ¬ hasBond hS s),
        ampS fam Cχ ξ s (base + latticePoint L (kconstInt hS roots s)) =
      ∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => ¬ hasBond hS s),
        ampS fam Cχ ξ s (kk s) := by
    refine Finset.prod_congr rfl fun s hs => ?_
    have hs' : ¬ hasBond hS s := by simpa using hs
    simp only [hkk]
    rw [kconstInt_spec hS roots s hs' κ.1 hz hroot]
  rw [hE, hN]
  exact Finset.prod_filter_mul_prod_filter_not _ _ _

open scoped Classical in
/-- On the support of the slot part of an assembled mode, every slot momentum is near its slot centre. -/
theorem slot_near (fam : SlotFam S d) (hS : S.IsPlain) (Cχ L : ℝ) (base : Mom d)
    (roots : Fin w → Fin d → ℤ) (tt : Fin w → ℝ) (κ : GenDecoration S d roots 0) (ξ : XiT fam)
    (h : constW fam hS Cχ L base roots tt ξ *
      (∏ x ∈ S.molecule.bonds, edgeS fam hS Cχ ξ x (base + latticePoint L (bondIndex S κ.1 x))) ≠ 0)
    (s : ReplacementSlot S) :
    ‖(base + latticePoint L (κ.1 (slotNode hS s))) - cenS fam ξ s‖ ≤ 1 := by
  have hprod : ∏ s, ampS fam Cχ ξ s (base + latticePoint L (κ.1 (slotNode hS s))) ≠ 0 := by
    rw [← prod_ampS_split fam hS Cχ L base roots κ ξ]
    intro h0
    apply h
    have hc : constW fam hS Cχ L base roots tt ξ =
        ((Cχ : ℂ) ^ (Fintype.card (GBranch S.tree)) * (∏ s, ((fam.w s (ξ.1 s) : ℝ) : ℂ)) *
          (if ξ.2 ∈ nodeCentreSet (fam.leafCentre hS ξ.1) then 1 else 0) *
          ∏ j : Fin w, Complex.exp (((Real.pi * modeFreq fam hS ξ (Sum.inl j) * tt j : ℝ) : ℂ) * Complex.I)) *
        (∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => ¬ hasBond hS s),
          ampS fam Cχ ξ s (base + latticePoint L (kconstInt hS roots s))) := by
      unfold constW; ring
    rw [hc]
    linear_combination ((Cχ : ℂ) ^ (Fintype.card (GBranch S.tree)) * (∏ s, ((fam.w s (ξ.1 s) : ℝ) : ℂ)) *
          (if ξ.2 ∈ nodeCentreSet (fam.leafCentre hS ξ.1) then 1 else 0) *
          ∏ j : Fin w, Complex.exp (((Real.pi * modeFreq fam hS ξ (Sum.inl j) * tt j : ℝ) : ℂ) * Complex.I)) * h0
  exact ampS_support fam Cχ ξ s _ (Finset.prod_ne_zero_iff.mp hprod s (Finset.mem_univ _))

open scoped Classical in
/-- On the support of the slot part of an assembled mode, every node momentum is near its centre `nodeCen`. -/
theorem node_near (fam : SlotFam S d) (hS : S.IsPlain) (Cχ L : ℝ) (base : Mom d)
    (roots : Fin w → Fin d → ℤ) (tt : Fin w → ℝ) (κ : GenDecoration S d roots 0) (ξ : XiT fam)
    (h : constW fam hS Cχ L base roots tt ξ *
      (∏ x ∈ S.molecule.bonds, edgeS fam hS Cχ ξ x (base + latticePoint L (bondIndex S κ.1 x))) ≠ 0)
    (ν : GNode S.tree) :
    ‖(base + latticePoint L (κ.1 ν)) - latPt d (nodeCen fam hS ξ ν)‖ ≤ 1 := by
  have hz : ∀ ℓ : GLeaf S.tree, κ.1 ℓ.toNode = κ.1 (S.pair ℓ).toNode := κ.2.1.2
  rcases (TTree.mem_nodes_iff _ _).mp ν.2 with hl | hb
  · set ℓ : GLeaf S.tree := ⟨ν.1, hl⟩
    have hν : ν = ℓ.toNode := Subtype.ext rfl
    rw [hν, nodeCen_leaf, dec_leaf_eq_first hS κ.1 hz ℓ]
    exact slot_near fam hS Cχ L base roots tt κ ξ h (Sum.inl (pairOfLeaf S hS ℓ))
  · set b : GBranch S.tree := ⟨ν.1, hb⟩
    have hν : ν = b.toNode := Subtype.ext rfl
    rw [hν, nodeCen_eq_cenS_branch]
    exact slot_near fam hS Cχ L base roots tt κ ξ h (Sum.inr b)

end WaveTurbulence.Represents
