/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistDecorations
public import WaveTurbulence.Foundations.Molecule.TwistSignCancellation

/-! # Preservation of the source epsilon coefficient under a unit twist

TARGET defepscoef and Definition twist: conservation at the lower branch
makes the epsilon coefficient invariant under the root/retained exchange.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Conservation identifies the two equalities used by the epsilon coefficient. -/
theorem lower_equalities {d : ℕ} (a b c : Fin d → ℤ) :
    (c = a-b+c ↔ a = b) ∧ (a = a-b+c ↔ b = c) := by
  constructor
  · constructor
    · intro h
      ext i
      have hi := congrFun h i
      change c i = a i-b i+c i at hi
      omega
    · intro h
      rw [h,sub_self,zero_add]
  · constructor
    · intro h
      ext i
      have hi := congrFun h i
      change a i = a i-b i+c i at hi
      omega
    · intro h
      rw [h,sub_add_cancel]

/-- The lower coefficient is invariant when the retained slot is the left child. -/
theorem epsCoef_exchange_left {d : ℕ} (a b c : Fin d → ℤ) :
    epsCoef (a-b+c) c b = epsCoef a b c := by
  classical
  have h := lower_equalities a b c
  by_cases hab : a = b <;> by_cases hbc : b = c <;>
    simp_all [epsCoef,eq_comm]

/-- The lower coefficient is invariant when the retained slot is the right child. -/
theorem epsCoef_exchange_right {d : ℕ} (a b c : Fin d → ℤ) :
    epsCoef b a (a-b+c) = epsCoef a b c := by
  classical
  have h := lower_equalities a b c
  by_cases hab : a = b <;> by_cases hbc : b = c <;>
    simp_all [epsCoef,eq_comm]

variable {w d : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The literal source epsilon coefficient at every corresponding branch is unchanged. -/
theorem unitTwist_epsCoef (κ : GNode G.tree → (Fin d → ℤ)) (hκ : IsDecoration G κ) (b : GBranch G.tree) :
    epsCoef (twistNodeLabels G P κ ((coreBranchEquiv G P b).child 0))
      (twistNodeLabels G P κ ((coreBranchEquiv G P b).child 1))
      (twistNodeLabels G P κ ((coreBranchEquiv G P b).child 2)) =
    epsCoef (κ (b.child 0)) (κ (b.child 1)) (κ (b.child 2)) := by
  by_cases hb : b = P.lower
  · subst b
    rw [twistNodeLabels_lower_child,twistNodeLabels_lower_child,twistNodeLabels_lower_child]
    have hk : P.keep = 0 ∨ P.keep = 2 := by have hh := P.outer; omega
    rcases hk with hk | hk
    · simp only [hk,freeSwap,Equiv.swap_apply_def]
      norm_num
      rw [hκ.1 P.lower]
      exact epsCoef_exchange_left _ _ _
    · simp only [hk,freeSwap,Equiv.swap_apply_def]
      norm_num
      rw [hκ.1 P.lower]
      exact epsCoef_exchange_right _ _ _
  · have h₀ := twistNodeLabels_other_child G P κ (hκ.2 P.retained) b hb 0
    have h₁ := twistNodeLabels_other_child G P κ (hκ.2 P.retained) b hb 1
    have h₂ := twistNodeLabels_other_child G P κ (hκ.2 P.retained) b hb 2
    exact (congrArg₂ (fun x y => epsCoef x y
      (twistNodeLabels G P κ ((coreBranchEquiv G P b).child 2))) h₀ h₁).trans
        (congrArg (epsCoef (κ (b.child 0)) (κ (b.child 1))) h₂)


/-- The literal full source epsilon product is preserved. -/
theorem unitTwist_epsDec (κ : GNode G.tree → (Fin d → ℤ)) (hκ : IsDecoration G κ) :
    epsDec (unitTwistGarden G P) (twistNodeLabels G P κ) = epsDec G κ := by
  classical
  exact (Fintype.prod_equiv (coreBranchEquiv G P)
    (fun b => epsCoef (κ (b.child 0)) (κ (b.child 1)) (κ (b.child 2)))
    (fun b => epsCoef (twistNodeLabels G P κ (b.child 0)) (twistNodeLabels G P κ (b.child 1))
      (twistNodeLabels G P κ (b.child 2)))
    (fun b => (unitTwist_epsCoef G P κ hκ b).symm)).symm

/-- The actual sign and epsilon prefactors cancel against a common amplitude.
The later LFTWIST packet controls the unequal original time domains and amplitudes. -/
theorem unitTwist_epsilon_amplitude_cancel (κ : GNode G.tree → (Fin d → ℤ)) (hκ : IsDecoration G κ) (A : ℂ) :
    (((branchSignProduct G : ℤ) : ℂ) * (epsDec G κ : ℂ) * A) +
      (((branchSignProduct (unitTwistGarden G P) : ℤ) : ℂ) *
        (epsDec (unitTwistGarden G P) (twistNodeLabels G P κ) : ℂ) * A) = 0 := by
  rw [unitTwist_epsDec G P κ hκ,branchSignProduct_unitTwist]
  simp

end WaveTurbulence.Twist
