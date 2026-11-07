/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineCollectionIndices
/-! Support alone fixes an object's ordinary/hyper tag and unordered joints.
The actual added bond of a hyper object is deliberately not identified here. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine.SourceVine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- The only two shape constructors used by actual collection choices. -/
def objectHyperTag (O : Object M) : Bool := match O.shape with
  | .vc _ => false
  | .hyper _ => true

/-- Ordinary and hyper block supports cannot coincide: their joint degrees differ. -/
theorem block_not_hyper {S : Finset V} {a b c d : V} (hB : M.IsBlock S a b)
    (e : D) (he : M.ends e = s(c, d)) (hH : (Mole.eraseBond M e).IsBlock S c d) : False := by
  have hd := Mole.hyperBlock_degrees M ⟨e, he, hH⟩
  have h2 := (Mole.block_joint_degrees M hB).1
  by_cases hac : a = c
  · have h3 : M.degIn S a = 3 := hac.symm ▸ hd.1
    omega
  · by_cases had : a = d
    · have h3 : M.degIn S a = 3 := had.symm ▸ hd.2.1
      omega
    · have h4 := hd.2.2 a hB.2.1 hac had
      omega

/-- Hyper-block joints are also intrinsic to the actual support. -/
theorem hyper_joints_unique {S : Finset V} {a b c d : V}
    (e f : D) (he : M.ends e = s(a, b)) (hf : M.ends f = s(c, d))
    (hE : (Mole.eraseBond M e).IsBlock S a b) (hF : (Mole.eraseBond M f).IsBlock S c d) :
    ({a, b} : Finset V) = {c, d} := by
  have hd := Mole.hyperBlock_degrees M ⟨e, he, hE⟩
  have kd := Mole.hyperBlock_degrees M ⟨f, hf, hF⟩
  have key {u v : V} (g : D) (hg : M.ends g = s(u, v))
      (hG : (Mole.eraseBond M g).IsBlock S u v) (x : V) (hx : x ∈ S) (h3 : M.degIn S x = 3) :
      x ∈ ({u, v} : Finset V) := by
    by_contra hn
    simp only [mem_insert, mem_singleton, not_or] at hn
    have h4 := (Mole.hyperBlock_degrees M ⟨g, hg, hG⟩).2.2 x hx hn.1 hn.2
    omega
  apply Finset.Subset.antisymm
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact key f hf hF x hE.2.1 hd.1
    · rw [mem_singleton.mp hx]
      exact key f hf hF b hE.2.2.1 hd.2.1
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact key e he hE x hF.2.1 kd.1
    · rw [mem_singleton.mp hx]
      exact key e he hE d hF.2.2.1 kd.2.1

/-- Independently chosen objects on the same support agree in tag and unordered joints. -/
theorem object_geometry_eq_of_atoms (P Q : Object M) (h : P.atoms = Q.atoms) :
    ({P.upper, P.lower} : Finset V) = {Q.upper, Q.lower} ∧ objectHyperTag P = objectHyperTag Q := by
  cases hp : P.shape with
  | vc hP =>
    cases hq : Q.shape with
    | vc hQ =>
      refine ⟨Vine.block_joints_unique M hP.1 (h.symm ▸ hQ.1), ?_⟩
      simp only [objectHyperTag, hp, hq]
    | hyper R =>
      exact (block_not_hyper hP.1 R.added R.ends_eq (h.symm ▸ R.adjoint.1)).elim
  | hyper R =>
    cases hq : Q.shape with
    | vc hQ =>
      exact (block_not_hyper hQ.1 R.added R.ends_eq (h ▸ R.adjoint.1)).elim
    | hyper T =>
      refine ⟨hyper_joints_unique R.added T.added R.ends_eq T.ends_eq R.adjoint.1 (h.symm ▸ T.adjoint.1), ?_⟩
      simp only [objectHyperTag, hp, hq]

end WaveTurbulence.VineA
