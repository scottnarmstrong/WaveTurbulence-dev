/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLOriginCoefficients

/-! # Unit source coefficients for any uniformly signed leaf subset -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Closure of the source unit-coefficient predicate under multiplication. -/
theorem unitCoeff_mul {a b : ℤ} (ha : IsUnitCoeff a) (hb : IsUnitCoeff b) : IsUnitCoeff (a*b) := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> norm_num [IsUnitCoeff]

theorem intUnit_isUnitCoeff (ζ : ℤˣ) : IsUnitCoeff (ζ : ℤ) := by
  rcases Int.units_eq_one_or ζ with rfl | rfl <;> norm_num [IsUnitCoeff]

noncomputable def clSignedSubsetCoeff (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (S : Finset (GLeaf (CLTreeForest R))) (q : GBranch (CLTreeForest R))
    (ζ : ℤˣ) (o : ↥(clRegionalPairs hG U) ⊕ Fin 4) : ℤ :=
  ((ζ : ℤ)*(nodeSign (fun _ : Fin 1 => G.sign a.toNode) q.1 : ℤ)) * clOriginCoeff hU R hG S q o

theorem clSignedSubsetCoeff_unit (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (S : Finset (GLeaf (CLTreeForest R))) (q : GBranch (CLTreeForest R))
    (ζ : ℤˣ) (o : ↥(clRegionalPairs hG U) ⊕ Fin 4) : IsUnitCoeff (clSignedSubsetCoeff hU R hG S q ζ o) :=
  unitCoeff_mul (unitCoeff_mul (intUnit_isUnitCoeff ζ) (intUnit_isUnitCoeff _))
    (clOriginCoeff_unit hU R hG S q o)

/-- Actual source pair cancellation applies to any leaf subset, with any
uniform sign; it does not require a predecessor or a hypothetical matrix. -/
theorem clSignedSubset_sum {E : Type*} [AddCommGroup E]
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (hG : G.IsPlain)
    (S : Finset (GLeaf (CLTreeForest R))) (q : GBranch (CLTreeForest R)) (ζ : ℤˣ)
    (κ : GNode G.tree → E)
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) :
    (∑ ℓ ∈ S, ((ζ : ℤ)*(nodeSign (fun _ : Fin 1 => G.sign a.toNode) ℓ.1 : ℤ)) • κ (clTreeNode R ℓ.toNode)) =
      ∑ o, clSignedSubsetCoeff hU R hG S q ζ o • clOriginValue hU R hG κ o := by
  have he := pushSignedCoeff_smul S (clLeafOrigin hU R hG)
    (predecessorLeafCoeff (fun _ : Fin 1 => G.sign a.toNode) q) (clOriginValue hU R hG κ)
  have hh := congrArg (fun z : E =>
    ((ζ : ℤ)*(nodeSign (fun _ : Fin 1 => G.sign a.toNode) q.1 : ℤ)) • z) he
  simp only [Finset.smul_sum,smul_smul] at hh
  simp only [mul_assoc,← mul_assoc (nodeSign (fun _ : Fin 1 => G.sign a.toNode) q.1 : ℤ),
    predecessorLeafCoeff,intUnit_square,mul_one] at hh
  simp_rw [← clLeafOrigin_value hU R hG κ hp] at hh
  simpa only [one_mul,clSignedSubsetCoeff,clOriginCoeff,mul_assoc] using hh

end WaveTurbulence.VineEstS2
