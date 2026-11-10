/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceJointPairUniqueness
public import WaveTurbulence.Foundations.Spine.SourceVineData
/-! A designated source object determines its joint pair, including in its actual hyper adjoint. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open SourceVine

abbrev SourceObjectJointPair {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} (P : Object M) (v : V) (x y : D) : Prop :=
  M.atom x = v ∧ M.atom y = v ∧ P.ContainsDart x ∧ P.ContainsDart y ∧
    M.out x = true ∧ M.out y = false

/-- Exact oriented uniqueness uses the designated deleted bond for hyper objects. -/
theorem source_object_joint_pair_unique {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} (P : Object M) {v : V}
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

end WaveTurbulence.LGSpine
