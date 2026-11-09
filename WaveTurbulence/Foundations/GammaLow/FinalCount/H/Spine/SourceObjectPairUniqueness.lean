/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceObjectPairUniqueness
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceObjectPairUniqueness`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 A designated source object determines its joint pair, including in its actual hyper adjoint. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open SourceVine

abbrev SourceObjectJointPair {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} (P : Src.Object Src.γL M) (v : V) (x y : D) : Prop :=
  M.atom x = v ∧ M.atom y = v ∧ P.ContainsDart x ∧ P.ContainsDart y ∧
    M.out x = true ∧ M.out y = false

/-- Exact oriented uniqueness uses the designated deleted bond for hyper objects. -/
theorem source_object_joint_pair_unique {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} (P : Src.Object Src.γL M) {v : V}
    (hv : v = P.upper ∨ v = P.lower) {x y x' y' : D}
    (hxy : SourceObjectJointPair P v x y) (hxy' : SourceObjectJointPair P v x' y') :
    x = x' ∧ y = y' := by
  rcases P with ⟨S, a, b, shape⟩
  cases shape with
  | vc h => exact source_joint_pair_unique M h.1 hv hxy hxy'
  | hyper R =>
    let E := Molecule.eraseBond M R.added
    let xe : {d : D // d ≠ R.added ∧ d ≠ M.mate R.added} :=
      ⟨x, hxy.2.2.1.1, hxy.2.2.1.2.1⟩
    let ye : {d : D // d ≠ R.added ∧ d ≠ M.mate R.added} :=
      ⟨y, hxy.2.2.2.1.1, hxy.2.2.2.1.2.1⟩
    let xe' : {d : D // d ≠ R.added ∧ d ≠ M.mate R.added} :=
      ⟨x', hxy'.2.2.1.1, hxy'.2.2.1.2.1⟩
    let ye' : {d : D // d ≠ R.added ∧ d ≠ M.mate R.added} :=
      ⟨y', hxy'.2.2.2.1.1, hxy'.2.2.2.1.2.1⟩
    have hp : SourceJointPair E S v xe ye :=
      ⟨hxy.1, hxy.2.1, hxy.2.2.1.2.2, hxy.2.2.2.1.2.2, hxy.2.2.2.2⟩
    have hp' : SourceJointPair E S v xe' ye' :=
      ⟨hxy'.1, hxy'.2.1, hxy'.2.2.1.2.2, hxy'.2.2.2.1.2.2, hxy'.2.2.2.2⟩
    have he := source_joint_pair_unique E R.adjoint.1 hv hp hp'
    exact ⟨congrArg Subtype.val he.1, congrArg Subtype.val he.2⟩

/-- Forgetting the orientation leaves precisely the source's swap ambiguity. -/
theorem source_object_joint_pair_eq_or_swap {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} (P : Src.Object Src.γL M) {v : V}
    (hv : v = P.upper ∨ v = P.lower) {x y x₀ y₀ : D}
    (hxy₀ : SourceObjectJointPair P v x₀ y₀)
    (hx : M.atom x = v) (hy : M.atom y = v) (hgx : P.ContainsDart x) (hgy : P.ContainsDart y)
    (ho : M.out x ≠ M.out y) :
    (x = x₀ ∧ y = y₀) ∨ (x = y₀ ∧ y = x₀) := by
  by_cases hox : M.out x = true
  · have hoy : M.out y = false := by cases hy' : M.out y <;> simp_all
    exact Or.inl (source_object_joint_pair_unique P hv ⟨hx, hy, hgx, hgy, hox, hoy⟩ hxy₀)
  · have hox' : M.out x = false := by cases hx' : M.out x <;> simp_all
    have hoy : M.out y = true := by cases hy' : M.out y <;> simp_all
    have hh := source_object_joint_pair_unique P hv ⟨hy, hx, hgy, hgx, hoy, hox'⟩ hxy₀
    exact Or.inr ⟨hh.2, hh.1⟩

end WaveTurbulence.GammaLow.FinalCount.H
