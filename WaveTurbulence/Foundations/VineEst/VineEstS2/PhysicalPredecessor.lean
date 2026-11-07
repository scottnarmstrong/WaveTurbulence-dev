/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SearchLeafSupport

/-! # Subtraction-only physical-momentum predecessor identities -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

theorem intUnit_square (ζ : ℤˣ) : (ζ : ℤ)*(ζ : ℤ) = 1 := by
  rcases Int.units_eq_one_or ζ with rfl | rfl <;> norm_num

theorem intUnit_zsmul_twice {E : Type*} [AddCommGroup E] (ζ : ℤˣ) (x : E) :
    (ζ : ℤ) • ((ζ : ℤ) • x) = x := by
  rw [smul_smul,intUnit_square,one_smul]

noncomputable def physicalPredecessor {E : Type*} [AddCommGroup E] (sig : Fin w → ℤˣ)
    (κ : GNode tree → E) (v : GBranch tree) : E :=
  (signPredecessor sig v).elim 0 (fun u => κ u.toNode)

theorem normalize_searchEndpoint {E : Type*} [AddCommGroup E] (sig : Fin w → ℤˣ)
    (κ : GNode tree → E) (v : GBranch tree) :
    (nodeSign sig v.1 : ℤ) • searchSignedEndpoint sig (nodeSign sig v.1) κ v = physicalPredecessor sig κ v := by
  cases hp : signPredecessor sig v with
  | none =>
    have he : (signHeavySearch sig (nodeSign sig v.1) v).2 = none := hp
    simp only [searchSignedEndpoint,physicalPredecessor,he,hp,Option.elim_none,smul_zero]
  | some u =>
    have he : (signHeavySearch sig (nodeSign sig v.1) v).2 = some u := hp
    have hs := (signPredecessor_target sig v u hp).1
    simp only [searchSignedEndpoint,physicalPredecessor,he,hp,Option.elim_some]
    rw [hs]
    exact intUnit_zsmul_twice _ _

/-- Every leaf coefficient before pair cancellation is an actual sign. -/
def predecessorLeafCoeff (sig : Fin w → ℤˣ) (v : GBranch tree) (ℓ : GLeaf tree) : ℤ :=
  (nodeSign sig v.1 : ℤ)*(nodeSign sig ℓ.1 : ℤ)

theorem predecessorLeafCoeff_unit (sig : Fin w → ℤˣ) (v : GBranch tree) (ℓ : GLeaf tree) :
    predecessorLeafCoeff sig v ℓ = 1 ∨ predecessorLeafCoeff sig v ℓ = -1 := by
  have h := Int.units_eq_one_or (nodeSign sig v.1*nodeSign sig ℓ.1)
  rcases h with h | h
  · left
    exact congrArg (fun ζ : ℤˣ => (ζ : ℤ)) h
  · right
    exact congrArg (fun ζ : ℤˣ => (ζ : ℤ)) h

/-- The exact physical row needed by sumint(ii), with subtraction even when
the immediate heavy child has the opposite sign. -/
theorem physical_predecessor_leaf_sum {E : Type*} [AddCommGroup E] (sig : Fin w → ℤˣ)
    (κ : GNode tree → E)
    (hκ : ∀ v : GBranch tree, κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (v : GBranch tree) :
    κ v.toNode-physicalPredecessor sig κ v =
      ∑ ℓ ∈ searchLeafSupport sig (nodeSign sig v.1) v, predecessorLeafCoeff sig v ℓ • κ ℓ.toNode := by
  have he := congrArg (fun x : E => (nodeSign sig v.1 : ℤ) • x)
    (searchLeafSupport_sum sig (nodeSign sig v.1) κ hκ v)
  simp only [smul_sub,Finset.smul_sum] at he
  rw [intUnit_zsmul_twice,normalize_searchEndpoint] at he
  simpa only [smul_smul,predecessorLeafCoeff] using he

end WaveTurbulence.VineEstS2
