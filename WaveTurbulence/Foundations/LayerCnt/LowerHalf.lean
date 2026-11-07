/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.HLowerV
public import WaveTurbulence.Foundations.LayerCnt.HLowerVI
public import WaveTurbulence.Foundations.LayerCnt.ChainGarden
import Mathlib.Tactic

/-! # The lower half of the layer range (TARGET layervine, L1531)

For a coherent (CL) vine, every atom has layer at least `𝔏_{v_2}`; for the atoms of vines (V)–(VIII) outside the cut
groups this uses the canonical pair criterion on the nodes of the vine region.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence WaveTurbulence.Vine TTree
variable {w : ℕ}

theorem lower_half_aux {G : Garden w} {f : GBranch G.tree → ℕ} {p : ℕ} {Reg : GNode G.tree → Prop}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (hf : LFTwist.IsBranchPrelayering G f)
    (hC : CanonPairs G f p Reg) (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b)
    (hRegS : ∀ x ∈ S, x ≠ a → Reg x.toNode)
    (hRegLeaf : ∀ ℓ : GLeaf G.tree, ∀ hr : ℓ.1.2 ≠ [], GNode.parent ℓ.toNode hr ∈ S →
      GNode.parent ℓ.toNode hr ≠ a → Reg (G.pair ℓ).toNode) :
    ∀ (X : VineType) (R : VineRealization G.molecule X S a b),
      Coherent f (realizedGroups R) → ∀ x ∈ S, f b ≤ f x := by
  intro X R hcoh
  have hch := chain_exists G hB hCL hf
  have hDB : G.molecule.DegreeBlock S a b := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ := hB
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hctx : PeelCtx G f p Reg X S a b R := ⟨hf, hC, hDB, hRegS, hRegLeaf, hcoh⟩
  have hjoint : ∀ z ∈ S, R.f z < 2 → f b ≤ f z := by
    intro z hz h2
    have hjt := R.joints_eq
    have : R.f z ∈ ({R.f a, R.f b} : Finset ℕ) := by
      rw [hjt]; simp; omega
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    have ha : a ∈ S := hDB.2.1
    have hb : b ∈ S := hDB.2.2.1
    rcases this with e | e
    · have : z = a := R.injOn hz ha e
      rw [this]; exact rtg_layer_mono hch
    · have : z = b := R.injOn hz hb e
      rw [this]
  have hgood : ∀ z ∈ S, ∀ g, g ∈ (X.expand R.k).groups → GoodGroup X R.k g → R.f z ∈ g → f b ≤ f z :=
    fun z hz g hg hgood hzg => lower_of_good R hcoh hch hg hgood hz hzg
  cases X
  · -- (I): no groups
    refine lower_cover R hcoh hjoint hgood ?_ ?_
    · intro g hg; simp [VineType.template] at hg
    · intro c hc; simp [VineType.template] at hc
  · refine lower_cover R hcoh hjoint hgood ?_ ?_
    · intro g hg hncut
      exact absurd ((by decide +kernel : ∀ g ∈ VineType.II.template.groups, CutG VineType.II.template g) g hg) hncut
    · intro c hc hncut
      have : c = 0 := by have : c < 1 := hc; omega
      subst this
      exact absurd (show CutS VineType.II.template 0 (VineType.II.template.slots[0]'(by decide)) by
        decide +kernel) hncut
  · refine lower_cover R hcoh hjoint hgood ?_ ?_
    · intro g hg hncut
      exact absurd ((by decide +kernel : ∀ g ∈ VineType.III.template.groups, CutG VineType.III.template g) g hg) hncut
    · intro c hc hncut
      have hc3 : c = 0 ∨ c = 1 := by have : c < 2 := hc; omega
      rcases hc3 with rfl | rfl
      · exact absurd (show CutS VineType.III.template 0 (VineType.III.template.slots[0]'(by decide)) by
          decide +kernel) hncut
      · exact absurd (show CutS VineType.III.template 1 (VineType.III.template.slots[1]'(by decide)) by
          decide +kernel) hncut
  · refine lower_cover R hcoh hjoint hgood ?_ ?_
    · intro g hg hncut
      exact absurd ((by decide +kernel : ∀ g ∈ VineType.IV.template.groups, CutG VineType.IV.template g) g hg) hncut
    · intro c hc hncut
      have hc3 : c = 0 ∨ c = 1 := by have : c < 2 := hc; omega
      rcases hc3 with rfl | rfl
      · exact absurd (show CutS VineType.IV.template 0 (VineType.IV.template.slots[0]'(by decide)) by
          decide +kernel) hncut
      · exact absurd (show CutS VineType.IV.template 1 (VineType.IV.template.slots[1]'(by decide)) by
          decide +kernel) hncut
  · exact hlower_V hctx hjoint
  · exact hlower_VI hctx hjoint hgood
  · exact hlower_VII hctx hjoint hgood
  · exact hlower_VIII hctx hjoint hgood

end WaveTurbulence.LayerCnt
