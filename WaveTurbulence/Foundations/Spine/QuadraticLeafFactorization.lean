/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafMonomialFactorization
/-! Signed quadratic root choices are exact multilinear coordinate modifications of leaves. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

def quadraticCoordinate {I : Type*} {d : ℕ}
    (c : RootQuadraticChoice I d) (b : Bool) : Option (I × Fin d) :=
  match c with
  | none => none
  | some (j, a, a') => some (if b then a' else a, j)

def quadraticSign {I : Type*} {d : ℕ} (ε : I → ℤˣ) : RootQuadraticChoice I d → ℝ
  | none => 1
  | some (_, a, a') => ((ε a : ℤ) : ℝ) * ((ε a' : ℤ) : ℝ)

theorem rootQuadraticTerm_factor {I : Type*} {d : ℕ} (ε : I → ℤˣ)
    (v : I → Mom d) (c : RootQuadraticChoice I d) :
    rootQuadraticTerm ε v c = quadraticSign ε c *
      ∏ b : Bool, coordinateSlotValue v (quadraticCoordinate c b) := by
  cases c with
  | none => simp [rootQuadraticTerm, quadraticSign, quadraticCoordinate, coordinateSlotValue]
  | some c =>
    rcases c with ⟨j, a, a'⟩
    simp only [rootQuadraticTerm, quadraticSign, quadraticCoordinate, Fintype.prod_bool,
      Bool.false_eq_true, ite_false, ite_true, coordinateSlotValue]
    ring

/-- The local leaf index of one root is sent to the original positive input slot. -/
def mapQuadraticChoice {A I : Type*} {d : ℕ} (f : A → I) :
    RootQuadraticChoice A d → RootQuadraticChoice I d
  | none => none
  | some (j, a, b) => some (j, f a, f b)

theorem rootQuadraticTerm_mapped_factor {A I : Type*} {d : ℕ}
    (f : A → I) (ε : A → ℤˣ) (v : I → Mom d) (c : RootQuadraticChoice A d) :
    rootQuadraticTerm ε (v ∘ f) c = quadraticSign ε c *
      ∏ b : Bool, coordinateSlotValue v (quadraticCoordinate (mapQuadraticChoice f c) b) := by
  rw [rootQuadraticTerm_factor]
  congr 1
  apply prod_congr rfl
  intro b _
  cases c with
  | none => rfl
  | some c =>
    rcases c with ⟨j, a, a'⟩
    cases b <;> rfl

/-- Different roots may have different local leaf types. All chosen factors are nevertheless
redistributed to the same original positive input slots, before the momentum sum is taken. -/
theorem prod_mappedQuadratic_leaf_factorization {I T : Type*} [Fintype I] [DecidableEq I]
    [Fintype T] {A : T → Type*} {d : ℕ}
    (H : I → Mom d → ℝ) (f : ∀ t, A t → I) (ε : ∀ t, A t → ℤˣ)
    (c : ∀ t, RootQuadraticChoice (A t) d) (v : I → Mom d) :
    (∏ l, H l (v l)) * (∏ t, rootQuadraticTerm (ε t) (v ∘ f t) (c t)) =
      (∏ t, quadraticSign (ε t) (c t)) *
        ∏ l, monomialLeafProfile H
          (fun tb : T × Bool => quadraticCoordinate (mapQuadraticChoice (f tb.1) (c tb.1)) tb.2)
          l (v l) := by
  classical
  simp_rw [rootQuadraticTerm_mapped_factor]
  rw [prod_mul_distrib, prod_monomialLeafProfile, Fintype.prod_prod_type]
  ring

/-- Once the root-weight choices are fixed, every oscillatory summand is a scalar sign
times the same kernel with separate modified input leaves. All finite choices are independent
of the momentum decoration. -/
theorem prod_quadratic_leaf_factorization {I T : Type*} [Fintype I] [DecidableEq I]
    [Fintype T] {d : ℕ} (H : I → Mom d → ℝ) (ε : T → I → ℤˣ)
    (c : T → RootQuadraticChoice I d) (v : I → Mom d) :
    (∏ l, H l (v l)) * (∏ t, rootQuadraticTerm (ε t) v (c t)) =
      (∏ t, quadraticSign (ε t) (c t)) *
        ∏ l, monomialLeafProfile H
          (fun tb : T × Bool => quadraticCoordinate (c tb.1) tb.2) l (v l) := by
  classical
  simp_rw [rootQuadraticTerm_factor]
  rw [prod_mul_distrib, prod_monomialLeafProfile, Fintype.prod_prod_type]
  ring

end WaveTurbulence.LGSpine
