/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm2
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the skeleton integrand at a fixed decoration and time is the assembled superposition
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS3.FS
open scoped ENNReal

variable {w d : ℕ} {S : Garden w}

theorem dec_leaf_eq_first (hS : S.IsPlain) (z : GNode S.tree → Fin d → ℤ)
    (hz : ∀ ℓ : GLeaf S.tree, z ℓ.toNode = z (S.pair ℓ).toNode) (ℓ : GLeaf S.tree) :
    z ℓ.toNode = z (((pairOfLeaf S hS ℓ).firstLeaf hS)).toNode := by
  by_cases hsn : nodeSign S.sig ℓ.1 = 1
  · rw [pairOfLeaf_first_of_positive S hS ℓ hsn]
  · rw [(pairOfLeaf_sides_neg S hS ℓ hsn).1]
    exact hz ℓ

open scoped Classical in
theorem hasSum_assembled (fam : SlotFam S d) (hS : S.IsPlain) (Cχ : ℝ) (hCχ : Cχ ≠ 0) (L : ℝ)
    (base : Mom d) (roots : Fin w → Fin d → ℤ) (tt : Fin w → ℝ)
    (Fn : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (κ : GenDecoration S d roots 0)
    (τ : GBranch S.tree → ℝ)
    (hFn : ∀ s, HasSum (fun l => (fam.w s l : ℂ) * fam.a s l (base + latticePoint L (κ.1 (slotNode hS s))) *
      fsPhase (fam.m s l) (slotTs hS tt τ s))
      (Fn s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s))))) :
    HasSum (fun ξ : XiT fam => constW fam hS Cχ L base roots tt ξ *
      (∏ x ∈ S.molecule.bonds, edgeS fam hS Cχ ξ x (base + latticePoint L (bondIndex S κ.1 x))) *
        timeFac fam hS ξ τ)
      (∏ s, Fn s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) := by
  have hdec := κ.2.1
  have hz : ∀ ℓ : GLeaf S.tree, κ.1 ℓ.toNode = κ.1 (S.pair ℓ).toNode := hdec.2
  have hroot : ∀ j, κ.1 (GNode.root S.tree j) = roots j := κ.2.2.1
  set kk : ReplacementSlot S → Mom d := fun s => base + latticePoint L (κ.1 (slotNode hS s)) with hkk
  have key := hasSum_node_slots fam hS Fn (slotTs hS tt τ) kk hFn
    (cosetDecoration S L base κ.1)
    (fun b => by
      simp only [cosetDecoration]
      rw [hdec.1 b, latticePoint_sub_add]
      abel)
    (fun ℓ => by
      simp only [cosetDecoration, hkk, slotNode]
      rw [dec_leaf_eq_first hS κ.1 hz ℓ])
    (fun b => rfl)
  refine key.congr_fun (fun ξ => ?_)
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
  have hAll : (∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (hasBond hS), ampS fam Cχ ξ s (kk s)) *
      (∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => ¬ hasBond hS s),
        ampS fam Cχ ξ s (kk s)) = ∏ s, ampS fam Cχ ξ s (kk s) :=
    Finset.prod_filter_mul_prod_filter_not _ _ _
  have hsplit : ∏ s, ampS fam Cχ ξ s (kk s) =
      (∏ s, fam.a s (ξ.1 s) (kk s)) *
        ((∏ b : GBranch S.tree, chiC d (ξ.2 b) (kk (Sum.inr b))) / (Cχ : ℂ) ^ (Fintype.card (GBranch S.tree))) := by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type (fun s => fam.a s (ξ.1 s) (kk s))]
    simp only [ampS, Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_const,
      Finset.card_univ]
    ring
  have hph := prod_fsPhase_slotTs fam hS tt τ ξ
  have hCne : (Cχ : ℂ) ^ (Fintype.card (GBranch S.tree)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hCχ)
  unfold SlotFam.term constW
  rw [hN, hE]
  have hfull : (∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (hasBond hS), ampS fam Cχ ξ s (kk s)) *
      (∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => ¬ hasBond hS s),
        ampS fam Cχ ξ s (kk s)) =
      (∏ s, fam.a s (ξ.1 s) (kk s)) *
        ((∏ b : GBranch S.tree, chiC d (ξ.2 b) (kk (Sum.inr b))) / (Cχ : ℂ) ^ (Fintype.card (GBranch S.tree))) :=
    hAll.trans hsplit
  rw [hph]
  have hfull' : (∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (hasBond hS), ampS fam Cχ ξ s (kk s)) *
      (∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => ¬ hasBond hS s),
        ampS fam Cχ ξ s (kk s)) * (Cχ : ℂ) ^ (Fintype.card (GBranch S.tree)) =
      (∏ s, fam.a s (ξ.1 s) (kk s)) * ∏ b : GBranch S.tree, chiC d (ξ.2 b) (kk (Sum.inr b)) := by
    rw [hfull]; field_simp
  linear_combination ((∏ s, ((fam.w s (ξ.1 s) : ℝ) : ℂ)) *
    (if ξ.2 ∈ nodeCentreSet (fam.leafCentre hS ξ.1) then (1 : ℂ) else 0) *
    (∏ j : Fin w, Complex.exp (((Real.pi * modeFreq fam hS ξ (Sum.inl j) * tt j : ℝ) : ℂ) * Complex.I)) *
    timeFac fam hS ξ τ) * hfull'

end WaveTurbulence.Represents
