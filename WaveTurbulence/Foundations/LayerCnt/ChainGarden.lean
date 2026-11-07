/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.ChainLower
public import WaveTurbulence.Foundations.LayerCnt.LayerRange
import Mathlib.Tactic

/-! # The parent chain from `v_2` to `v_1` (TARGET layervine, L1531)

In a (CL) block `S` of a garden with upper joint `a` and lower joint `b`, repeatedly passing to the parent node is a
chain of bonds of `S` with non-decreasing layer that ends at `a`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open TTree
variable {w : ℕ}

theorem parent_mem_block (G : Garden w) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (D : Mole.CLGeometricData G S a b) {x : GBranch G.tree} (hx : x ∈ S) (hxr : x.1.2 ≠ [])
    (ha : a.toNode.IsDesc x.toNode) (hxa : x ≠ a) : GNode.parent x.toNode hxr ∈ S := by
  have hxr' := (D.realization x.toNode).mp ((Mole.branch_incidence_realization_iff G S x).mpr hx)
  rw [← Mole.branch_incidence_realization_iff G S (GNode.parent x.toNode hxr), D.realization]
  have hpx : (GNode.parent x.toNode hxr).toNode.IsDesc x.toNode := by
    refine ⟨rfl, ?_⟩
    show x.1.2.dropLast <+: x.1.2
    exact List.dropLast_prefix _
  have hap : a.toNode.IsDesc (GNode.parent x.toNode hxr).toNode := by
    obtain ⟨hj, q, hq⟩ : a.1.1 = x.1.1 ∧ ∃ q, a.1.2 ++ q = x.1.2 := ha
    have hq0 : q ≠ [] := by
      rintro rfl
      apply hxa
      apply Subtype.ext
      exact Prod.ext hj.symm (by simpa using hq.symm)
    refine ⟨hj, q.dropLast, ?_⟩
    show a.1.2 ++ q.dropLast = x.1.2.dropLast
    rw [← hq, List.dropLast_append_of_ne_nil hq0]
  have hdesc : ∀ c : GNode G.tree, c.IsDesc (GNode.parent x.toNode hxr).toNode → c.IsDesc x.toNode := by
    intro c hc
    exact ⟨hc.1.trans hpx.1, hc.2.trans hpx.2⟩
  exact ⟨hap, fun h => hxr'.2.1 (hdesc _ h), fun h => hxr'.2.2.1 (hdesc _ h),
    fun h => hxr'.2.2.2 (hdesc _ h)⟩

theorem chain_exists (G : Garden w) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b) {f : GBranch G.tree → ℕ}
    (hf : LFTwist.IsBranchPrelayering G f) :
    Relation.ReflTransGen (StepF G.molecule S f) b a := by
  have hB0 := hB
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ := hB
  have hDB : G.molecule.DegreeBlock S a b := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  obtain ⟨D⟩ := Mole.cl_geometric_data G hB0 hCL
  have key : ∀ n, ∀ x : GBranch G.tree, x.1.2.length = n → x ∈ S → a.toNode.IsDesc x.toNode →
      Relation.ReflTransGen (StepF G.molecule S f) x a := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hn hx hax
      by_cases hxa : x = a
      · subst hxa; exact Relation.ReflTransGen.refl
      · have hxr : x.1.2 ≠ [] := by
          obtain ⟨hj, q, hq⟩ : a.1.1 = x.1.1 ∧ ∃ q, a.1.2 ++ q = x.1.2 := hax
          intro h0
          rw [h0] at hq
          have : a.1.2 = [] ∧ q = [] := by simpa using hq
          apply hxa
          apply Subtype.ext
          exact Prod.ext hj.symm (by rw [h0, this.1])
        have hpS := parent_mem_block G D hx hxr hax hxa
        have hap : a.toNode.IsDesc (GNode.parent x.toNode hxr).toNode := by
          obtain ⟨hj, q, hq⟩ : a.1.1 = x.1.1 ∧ ∃ q, a.1.2 ++ q = x.1.2 := hax
          have hq0 : q ≠ [] := by
            rintro rfl
            apply hxa
            apply Subtype.ext
            exact Prod.ext hj.symm (by simpa using hq.symm)
          refine ⟨hj, q.dropLast, ?_⟩
          show a.1.2 ++ q.dropLast = x.1.2.dropLast
          rw [← hq, List.dropLast_append_of_ne_nil hq0]
        have hlen : (GNode.parent x.toNode hxr).1.2.length < n := by
          rw [← hn]
          show x.1.2.dropLast.length < x.1.2.length
          rw [List.length_dropLast]
          have := List.length_pos_of_ne_nil hxr; omega
        refine Relation.ReflTransGen.head (b := GNode.parent x.toNode hxr) ?_ (ih _ hlen _ rfl hpS hap)
        refine ⟨hx, hpS, ?_, garden_parent_step_le G hf x hxr⟩
        have hig : G.molecule.InGroup S (Sum.inl (⟨x, hxr⟩, false)) := by
          unfold Molecule.InGroup; exact ⟨hx, hpS⟩
        exact mem_groupBonds_of_inGroup (M := G.molecule) S _ hig
  exact key _ b rfl h3 (by simpa using D.lower_descendant)

end WaveTurbulence.LayerCnt
