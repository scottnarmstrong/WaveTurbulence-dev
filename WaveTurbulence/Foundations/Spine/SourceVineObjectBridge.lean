/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceVineData
public import WaveTurbulence.Foundations.Molecule.VineLikeGapObjects
/-! Definition-preserving transport of the spine's designated objects to the proved VINES API. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.SourceVine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

 theorem Chain.toVine {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain M S a b n) : Vine.Chain M S a b n := by
  induction h with
  | single h => exact .single h
  | append h hV hI hne ih => exact .append ih hV hI hne

 theorem IsVC.toVine {M : Molecule V D} {S : Finset V} {a b : V}
    (h : IsVC M S a b) : Vine.IsVC M S a b := by
  obtain ⟨n, hn⟩ := h.2
  exact ⟨h.1, n, hn.toVine⟩

def HyperLikeRealization.toVine {M : Molecule V D} {S : Finset V} {a b : V}
    (R : HyperLikeRealization M S a b) : Vine.HyperLikeRealization M S a b where
  added := R.added
  ends_eq := R.ends_eq
  adjoint := R.adjoint.toVine

def VineLikeObject.toVine {M : Molecule V D} {S : Finset V} {a b : V} :
    VineLikeObject M S a b → Vine.VineLikeObject M S a b
  | .vc h => .vc h.toVine
  | .hyper R => .hyper R.toVine

theorem VineLikeObject.toVine_isGap {M : Molecule V D} {S : Finset V} {a b : V}
    (P : VineLikeObject M S a b) {d : ℕ} (L : ℝ) (base : Mom d) (κ : D → (Fin d → ℤ)) (r : Mom d) :
    P.toVine.IsGap L base κ r ↔ P.IsGap L base κ r := by
  cases P <;> rfl

theorem VineLikeObject.toVine_isContained {M : Molecule V D} {S A : Finset V} {a b x y : V}
    (P : VineLikeObject M A x y) (Q : VineLikeObject M S a b) :
    P.toVine.IsContained Q.toVine ↔ P.IsContained Q := by
  cases P <;> cases Q <;> rfl

theorem Object.contained_atoms_subset {M : Molecule V D} (P Q : Object M) (h : P.IsContained Q) :
    P.atoms ⊆ Q.atoms := by
  exact (P.shape.toVine.atoms_subset Q.shape.toVine)
    ((P.shape.toVine_isContained Q.shape).mpr h)

end WaveTurbulence.LGSpine.SourceVine
