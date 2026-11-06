/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamRootIntegerMatrix
public import WaveTurbulenceVineParam.VineParamReducedDecoder
import Mathlib.Tactic

/-! # Complete source-fiber equivalence of a normalized integer certificate -/

public section
namespace WaveTurbulence.Vine.Param.RootIntegerMatrix
variable {q : ℕ} (C : RootIntegerMatrix q) {E : Type*} [AddCommGroup E]

/-- Every actual nonjoint row in the source fiber is zero. -/
theorem source_interior_zero (r : E) (k : DirectedRootFiber C.ends C.a C.b r) (v : Fin (q-1)) :
    directedFlow C.ends (C.interior v).1 k.1=0 := by
  simpa only [rootForcing,(C.interior v).2.1,(C.interior v).2.2,ite_false] using k.2 (C.interior v).1

/-- The encoder reads the exact included-joint gap on the source fiber. -/
theorem source_gap (r : E) (k : DirectedRootFiber C.ends C.a C.b r) :
    intEval C.forward k.1 C.gapIndex=r := by
  rw [C.eval_gap]
  simpa only [rootForcing,C.distinct.symm,ite_false,ite_true] using k.2 C.b

/-- Conservation is precisely the zero tail required by the integer inverse. -/
theorem source_later_zero (r : E) (k : DirectedRootFiber C.ends C.a C.b r)
    (i : Fin (2 * q)) (hi : q < i.val) : intEval C.forward k.1 i=0 := by
  obtain ⟨v,rfl⟩ := C.later_index i hi
  rw [C.eval_interior]
  exact C.source_interior_zero r k v

/-- Every free vector decodes to the actual full source fiber, including
both joint equations; the omitted joint row is forced by finite cut flow. -/
@[expose] def decodeRoot (r : E) (x : Fin q → E) : DirectedRootFiber C.ends C.a C.b r := by
  let k := intEval C.inverse (packCoordinates C.gap_lt x r)
  have he : intEval C.forward k=packCoordinates C.gap_lt x r :=
    coordinates_of_integer_certificate C.gap_lt C.forward C.inverse C.forward_inverse x r
  have hb : directedFlow C.ends C.b k=r := by
    rw [← C.eval_gap,he]
    exact pack_gap C.gap_lt x r
  have hv : ∀ v : Fin (q-1),directedFlow C.ends (C.interior v).1 k=0 := by
    intro v
    rw [← C.eval_interior,he]
    apply pack_large C.gap_lt
    change q < q+1+v.1
    omega
  have hz : ∀ v,v ≠ C.a → v ≠ C.b → directedFlow C.ends v k=0 := by
    intro v hva hvb
    let w := C.interior.symm ⟨v,hva,hvb⟩
    have hw : (C.interior w).1=v := congrArg Subtype.val (C.interior.apply_symm_apply ⟨v,hva,hvb⟩)
    rw [← hw]
    exact hv w
  have ha : directedFlow C.ends C.a k= -r := by
    rw [second_joint_flow_neg_finite C.ends k C.b C.a C.distinct.symm (fun v hvb hva => hz v hva hvb),hb]
  refine ⟨k,?_⟩
  intro v
  by_cases hva : v=C.a
  · subst v
    simpa only [rootForcing,ite_true] using ha
  · by_cases hvb : v=C.b
    · subst v
      simpa only [rootForcing,C.distinct.symm,ite_false,ite_true] using hb
    · simpa only [rootForcing,hva,hvb,ite_false] using hz v hva hvb

/-- Exact unimodular coordinates on the whole source label fiber. -/
@[expose] def rootChart (r : E) : DirectedRootFiber C.ends C.a C.b r ≃ (Fin q → E) where
  toFun := fun k => freeCoordinates C.gap_lt (intEval C.forward k.1)
  invFun := C.decodeRoot r
  left_inv := by
    intro k
    apply Subtype.ext
    exact reconstruct_of_integer_certificate C.gap_lt C.forward C.inverse C.inverse_forward k.1 r
      (C.source_gap r k) (C.source_later_zero r k)
  right_inv := by
    intro x
    change freeCoordinates C.gap_lt
      (intEval C.forward (intEval C.inverse (packCoordinates C.gap_lt x r)))=x
    rw [coordinates_of_integer_certificate C.gap_lt C.forward C.inverse C.forward_inverse,free_pack]

/-- The raw inverse is the complete integer matrix decoder on the packed
free/gap vector, with every interior divergence fixed to zero. -/
theorem rootChart_decode (r : E) (x : Fin q → E) :
    ((C.rootChart r).symm x).1=intEval C.inverse (packCoordinates C.gap_lt x r) := rfl

end WaveTurbulence.Vine.Param.RootIntegerMatrix
