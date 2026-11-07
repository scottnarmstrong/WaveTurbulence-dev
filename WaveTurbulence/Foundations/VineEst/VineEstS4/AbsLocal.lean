/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalKernel
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairSides

/-! # A local CL decoration is determined by the labels at the first leaves of its regional pairs (V5 Step 4b)

`clLocalDecoration_ext_of_pairs`: with the four boundary momenta fixed, two decorations of the CL region that agree at the first
leaf of every regional leaf pair coincide.  (Internal leaves are the two ends of the regional pairs; the branch labels follow by
conservation from the leaf labels and the boundary.)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem internalLeaf_first_or_second (hG : G.IsPlain) (ℓ : GLeaf G.tree) (hℓ : Mole.IsInternalLeaf G U ℓ) :
    ∃ p ∈ clRegionalPairs hG U, p.firstLeaf hG = ℓ ∨ p.firstLeaf hG = G.pair ℓ := by
  classical
  by_cases hs : nodeSign G.sig ℓ.1 = 1
  · have h := pairOfLeaf_sides_pos G hG ℓ hs
    refine ⟨pairOfLeaf G hG ℓ, ?_, Or.inl h.1⟩
    simp only [clRegionalPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h.1]
    exact hℓ
  · have hne := Comb.pair_ne_of_plain hG ℓ
    have hsn : nodeSign G.sig (G.pair ℓ).1 = 1 := by
      have := G.pair_sign ℓ hne
      rw [this]
      rcases Int.units_eq_one_or (nodeSign G.sig ℓ.1) with h | h
      · exact absurd h hs
      · rw [h]; rfl
    have h := pairOfLeaf_sides_pos G hG (G.pair ℓ) hsn
    have hℓ' := (Mole.internal_leaf_pair_iff G U ℓ).mpr hℓ
    refine ⟨pairOfLeaf G hG (G.pair ℓ), ?_, Or.inr h.1⟩
    simp only [clRegionalPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h.1]
    exact hℓ'

theorem clLocalDecoration_ext_of_pairs (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (hG : G.IsPlain)
    {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → Mom d) (z z' : CLLocalDecoration R L base β)
    (h : ∀ p ∈ clRegionalPairs hG U,
      clExtendIndices R z.1 (p.firstLeaf hG).toNode = clExtendIndices R z'.1 (p.firstLeaf hG).toNode) :
    z = z' := by
  classical
  let δ : GNode G.tree → (Fin d → ℤ) := fun n => clExtendIndices R z.1 n - clExtendIndices R z'.1 n
  have hfirst : ∀ p ∈ clRegionalPairs hG U, δ (p.firstLeaf hG).toNode = 0 := fun p hp =>
    sub_eq_zero.mpr (h p hp)
  have hleaf : ∀ ℓ : GLeaf G.tree, Mole.IsInternalLeaf G U ℓ → δ ℓ.toNode = 0 := by
    intro ℓ hℓ
    obtain ⟨p, hp, hpℓ⟩ := internalLeaf_first_or_second hG ℓ hℓ
    rcases hpℓ with he | he
    · rw [← he]; exact hfirst p hp
    · have h0 := hfirst p hp
      rw [he] at h0
      have hp1 := z.2.2.1 ℓ hℓ
      have hp2 := z'.2.2.1 ℓ hℓ
      simp only [δ] at h0 ⊢
      rw [hp1, hp2]
      exact h0
  have hbd : ∀ j, δ (clBoundaryNodes R j) = 0 := fun j =>
    sub_eq_zero.mpr (clLocalDecoration_boundary_indices_eq R hL base β z z' j)
  set B := (Finset.univ : Finset (GNode G.tree)).sup fun a => a.1.2.length with hB
  have hle : ∀ a : GNode G.tree, a.1.2.length ≤ B := fun a =>
    Finset.le_sup (f := fun a : GNode G.tree => a.1.2.length) (Finset.mem_univ a)
  have key : ∀ n : GNode G.tree, n ∈ clLocalSupport R → δ n = 0 := by
    intro n
    induction hm : B - n.1.2.length using Nat.strong_induction_on generalizing n with
    | _ m ih =>
      intro hn
      rcases Finset.mem_union.mp hn with hr | hb'
      · rcases (Comb.TreePath.mem_nodes_iff _ _).1 n.2 with hl | hbr
        · have hint := (leaf_mem_clRealizationNodes (G := G) (U := U) ⟨n.1, hl⟩).mp hr
          exact hleaf ⟨n.1, hl⟩ hint
        · let v : GBranch G.tree := ⟨n.1, hbr⟩
          have hv : v ∈ U := (branch_mem_clRealizationNodes v).mp hr
          have hcons := z.2.1 v hv
          have hcons' := z'.2.1 v hv
          have hc : ∀ i : Fin 3, δ (v.child i) = 0 := by
            intro i
            have hlen : (v.child i).1.2.length = n.1.2.length + 1 := by simp [GBranch.child, v]
            refine ih (B - (v.child i).1.2.length) ?_ (v.child i) rfl (cl_child_mem_support hU R hv i)
            · have := hle (v.child i)
              omega
          have : δ v.toNode = δ (v.child 0) - δ (v.child 1) + δ (v.child 2) := by
            simp only [δ, hcons, hcons']
            abel
          rw [hc 0, hc 1, hc 2] at this
          exact (by simpa using this : δ v.toNode = 0)
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb'
        exact hbd j
  apply Subtype.ext
  funext ⟨x, hx⟩
  have := key x hx
  simp only [δ] at this
  rw [clExtendIndices_apply R _ x hx, clExtendIndices_apply R _ x hx] at this
  exact sub_eq_zero.mp this

end WaveTurbulence.VineEstS4
