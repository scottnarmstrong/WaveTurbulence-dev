/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.HeavyPathAncestors
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SignSearchTarget

/-! # No repeated start sign in an actually constructed predecessor route -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

def NoSignInside (sig : Fin w → ℤˣ) (ζ : ℤˣ) (v x : GBranch tree) : Prop :=
  v.toNode.IsDesc x.toNode ∧ ∀ z : GBranch tree,
    v.toNode.IsDesc z.toNode → z.toNode.IsDesc x.toNode → z ≠ v → nodeSign sig z.1 ≠ ζ

theorem branch_desc_antisymm {v z : GBranch tree} (hvz : v.toNode.IsDesc z.toNode)
    (hzv : z.toNode.IsDesc v.toNode) : v = z :=
  Subtype.ext (Prod.ext hvz.1 (hvz.2.eq_of_length_le hzv.2.length_le))

theorem noSignInside_self (sig : Fin w → ℤˣ) (ζ : ℤˣ) (v : GBranch tree) : NoSignInside sig ζ v v := by
  refine ⟨GNode.isDesc_refl _,?_⟩
  intro z hvz hzv hne
  exact (hne (branch_desc_antisymm hzv hvz)).elim

/-- Source ancestry and the absence of repeated start sign are proved for
every visited branch of the terminating search. -/
theorem signHeavySearch_route_spec (sig : Fin w → ℤˣ) (ζ : ℤˣ) (v x : GBranch tree)
    (hx : x ∈ (signHeavySearch sig ζ v).1) : NoSignInside sig ζ v x := by
  induction hm : branchDepthBound tree-v.1.2.length using Nat.strong_induction_on generalizing v with
  | h n ih =>
    cases hn : nextHeavyBranch v with
    | none =>
      rw [signHeavySearch_none sig ζ v hn] at hx
      have he : x = v := List.mem_singleton.mp hx
      subst x
      exact noSignInside_self sig ζ v
    | some z =>
      by_cases hz : nodeSign sig z.1 = ζ
      · rw [signHeavySearch_same sig ζ hn hz] at hx
        have he : x = v := List.mem_singleton.mp hx
        subst x
        exact noSignInside_self sig ζ v
      · rw [signHeavySearch_different sig ζ hn hz] at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact noSignInside_self sig ζ x
        · have hlt : branchDepthBound tree-z.1.2.length < n := by
            rw [← hm]
            exact nextHeavyBranch_measure_lt hn
          have ht := ih _ hlt z hx rfl
          refine ⟨(nextHeavyBranch_desc hn).trans ht.1,?_⟩
          intro y hvy hyx hyv
          have hzy := nextHeavyBranch_between hn ht.1 hvy hyx hyv
          by_cases hyz : y = z
          · subst y
            exact hz
          · exact ht.2 y hzy hyx hyz

/-- Actual routes satisfy the two-color interval predicate used by the
charging proof; it is not an assumed property of a proposed predecessor. -/
theorem signPredecessorRoute_colorInterval (sig : Fin w → ℤˣ) (v x : GBranch tree)
    (hx : x ∈ signPredecessorRoute sig v) :
    ColorInterval (fun a b : GBranch tree => a.toNode.IsDesc b.toNode)
      (fun a => signColor (nodeSign sig a.1)) v x := by
  classical
  have ht := signHeavySearch_route_spec sig (nodeSign sig v.1) v x (List.mem_toFinset.mp hx)
  refine ⟨ht.1,?_⟩
  intro z hvz hzx hvne he
  exact ht.2 z hvz hzx (Ne.symm hvne) (signColor_injective he)

end WaveTurbulence.VineEstS2
